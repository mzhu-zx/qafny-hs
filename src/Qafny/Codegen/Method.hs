{-# LANGUAGE
    ConstraintKinds
  , FlexibleContexts
  , NamedFieldPuns
  , TupleSections
  , TypeApplications
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
    (liftM2)
import           Data.Functor
import           Qafny.Effect
import           Qafny.Syntax.AST
import           Qafny.Syntax.ASTFactory
    (mkDeclAssign)
import           Qafny.Syntax.EmitBinding
import           Qafny.Syntax.IR
import           Qafny.TypeUtils
    (tyKetByQTy)
import           Qafny.Typing.Typing
    (collectPureBindings)
import           Qafny.Utils.EmitBinding
    (findEmitBasesByRanges, gensymBinding)
import           Qafny.Utils.Utils
    (dumpSt)
import Data.Foldable (Foldable(toList))

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
codegenMethodParams
  :: ( StateMayFail sig m
     , Has Trace sig m
     )
  => MethodType -> [(PhaseRef, Ty)] -> m [Binding']
codegenMethodParams
  MethodType{ mtSrcParams=srcParams , mtInstantiate=instantiator}
  ptysResolved
  = do
  trace "* codegenMethodParams"
  let pureVars = collectPureBindings srcParams
      qVars = [ (v, Range v 0 card) | MTyQuantum v card <- srcParams ]
      inst = instantiator $ Map.fromList qVars
      pVars = uncurry codegenPhaseBinding `concatMap` ptysResolved
  trace $ "QVARS: " ++ show qVars
  trace $ "INSTANCE: " ++ show inst
  trace $ "PVars" ++ show pVars
  vqEmits <- concat <$> sequence
    [ findEmitBasesByRanges ranges
    | (Partition{ranges}, qt, _) <- inst ]
  dumpSt "MethodParams"
  pure $ pureVars ++ (uncurry Binding <$> vqEmits) ++ pVars


codegenPhaseBinding :: PhaseRef -> Ty -> [Binding']
codegenPhaseBinding PhaseRef{prBase, prRepr} ty =
  [ Binding prBase TNat , Binding prRepr ty ]
  
