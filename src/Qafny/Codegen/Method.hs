{-# LANGUAGE
    ConstraintKinds
  , FlexibleContexts
  , NamedFieldPuns
  , TupleSections
  , TypeApplications
  , TypeFamilies
  , TypeOperators
  #-}

module Qafny.Codegen.Method where

-- eff
import           Control.Effect.Lens

-- data
import           Control.Lens
    (at, (?~))
import qualified Data.Map.Strict          as Map

-- Qafny
import           Control.Monad
    (forM, liftM2)
import           Data.Function
    (on)
import           Data.Functor
import           Qafny.Effect
import           Qafny.Syntax.AST
import           Qafny.Syntax.ASTFactory
    (mkAssignment, mkDeclAssign)
import           Qafny.Syntax.EmitBinding
import           Qafny.Syntax.IR
import           Qafny.Typing.Utils
    (tyKetByQTy)

import           Data.Foldable
    (Foldable (toList))
import           Qafny.Codegen.Common
    (codegenAssignEmitData)
import           Qafny.Typing.Method
    (collectPureBindings)
import           Qafny.Typing.Phase
    (queryPhase)
import           Qafny.Typing.Typing
    (typingPartitionQTy)
import           Qafny.Utils.EmitBinding
    (eraseRanges, findEmitBasesByRanges, findEmsByLocus, genEmStFromLocus,
    gensymBinding, extractEmitablesFromEds)
import           Qafny.Utils.Utils
    (dumpSt, fst2)

-- * Method related definitions


-- | Take the emit state and generate totally new emit symbols and emit
-- statements to match the translation
--
-- This is needed because you cannot mutate the parameter of a method.
-- An alternative is to copy the augument into a local variable where mutation
-- are allowed.
genEmitSt :: GensymEmitterWithState sig m => m [Stmt']
genEmitSt = do
  eSt <- use emitSt
  emitSt %= const Map.empty
  concat <$> mapM (uncurry replicateEmitEntry) (Map.toList eSt)

replicateEmitEntry
  :: GensymEmitterWithState sig m
  => RangeOrLoc -> EmitData -> m [Stmt']
replicateEmitEntry rl
  ed@EmitData{evBasis, evPhaseRef, evAmp} =
  do evBasis'    <- evBasisM
     evPhaseRef' <- evPhaseRefM
     let refs = liftM2 (,) evPhaseRef' evPhaseRef
     -- let evPhase' = uncurry mkPhaseRef <$> prVars
     emitSt %= (at rl ?~ ed{evBasis=evBasis', evPhaseRef=evPhaseRef'})
     return $
       toList (liftM2 (uncurry mkDeclAssign) evBasis' (evBasis <&> fst))
       ++ concat (toList (refs <&> replicatePhases))

  where
    evBasisM    = mapM (uncurry gensymBinding) evBasis
    evPhaseRefM = mapM (uncurry replicatePhase) evPhaseRef
    replicatePhases ((p1, ty1), (p2, ty2)) =
      [ mkDeclAssign (prBase p1) TNat (prBase p2)
      , mkDeclAssign (prRepr p1) ty1 (prRepr p2)
      ]

replicatePhase
  :: Has (Gensym Emitter) sig m
  => PhaseRef -> Ty -> m (PhaseRef, Ty)
replicatePhase PhaseRef{prBase, prRepr} tyRepr =
  liftM2 go prBaseM prReprM
  where
    go prBase'' prRepr'' = (PhaseRef prBase'' prRepr'', tyRepr)
    prBaseM = fst <$> gensymBinding prBase TNat
    prReprM = fst <$> gensymBinding prRepr tyRepr

-- | Generate method parameters from the method signature
codegenMethodParams :: MethodType -> [EmitData] -> [Binding']
codegenMethodParams MethodType{ mtSrcParams } eds =
  let pureVars = collectPureBindings mtSrcParams
      emitables = concatMap extractEmitables eds
  in pureVars ++ (uncurry Binding <$> emitables)


codegenMethodReturns
  :: ( Has (State TState) sig m
     , Has (Gensym Emitter) sig m
     , Has (Error String) sig m
     , Has (Reader IEnv) sig m
     , Has Trace sig m
     )
  => MethodType -> m ([Stmt'], [Binding'])
codegenMethodReturns MethodType{ mtSrcReturns=srcReturns
                               , mtReceiver=receiver
                               } = do
  let pureBds = collectPureBindings srcReturns
      qVars = [ (v, Range v 0 card) | MTyQuantum v card <- srcReturns ]
      inst = receiver $ Map.fromList qVars
  -- perform type checking
  loci <- forM (fst2 <$> inst) (uncurry typingPartitionQTy)
  eds <- mapM findEmsByLocus loci
  edsRet <- mapM genEmStFromLocus loci
  let stmtsAssign = (codegenAssignEmitData `on` compactEds) eds edsRet

  return ( stmtsAssign
         , pureBds ++ bindEmitables edsRet)
  where
    compactEds = concatMap eraseRanges
    bindEmitables =
      (uncurry Binding <$>) . concatMap (uncurry extractEmitablesFromEds)

codegenPhaseBinding :: PhaseRef -> Ty -> [Binding']
codegenPhaseBinding PhaseRef{prBase, prRepr} ty =
  [ Binding prBase TNat , Binding prRepr ty ]

