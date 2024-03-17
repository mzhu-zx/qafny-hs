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
    (Bifunctor (bimap), at, sans, (?~), (^.))
import qualified Data.Map.Strict          as Map

-- Qafny
import           Control.Monad
    (join, liftM, liftM2, liftM3, zipWithM)
import           Data.Maybe
    (catMaybes)
import           Effect.Gensym
    (gensym)
import           Qafny.Effect
import           Qafny.Syntax.AST
import           Qafny.Syntax.ASTFactory
    (mkAssignment, mkDAssignment)
import           Qafny.Syntax.EmitBinding
    (EmitData (..), Emitter (EmAnyBinding))
import           Qafny.Syntax.IR
import           Qafny.TypeUtils
    (typingPhaseEmitReprN, tyKetByQTy)
import           Qafny.Typing.Typing
    (collectPureBindings)
import           Qafny.Utils.EmitBinding
    (findEmitBasesByRanges, gensymBinding)
import           Qafny.Utils.Utils
    (dumpSt)

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
  ed@EmitData{evBasis, evBasisTy, evPhaseSeqTy, evPhaseRef, evAmp} =
  do evBasis'    <- sequence evBasisM
     evPhaseRef' <- sequence evPhaseRefM
     let refs = liftM2 (,) evPhaseRef' evPhaseRef
     -- let evPhase' = uncurry mkPhaseRef <$> prVars
     emitSt %= (at rl ?~ ed{evBasis=evBasis', evPhaseRef=evPhaseRef'})
     return $ catMaybes
       [ liftM3 mkDAssignment evBasisTy evBasis' evBasis
       , uncurry (mkDAssignment TNat) . bimap prBase prBase <$> refs
       , decl $ bimap prRepr prRepr <$> refs
       ]
  where
    evBasisM    = liftM2 gensymBinding evBasis evBasisTy
    evPhaseRefM = liftM2 replicatePhase evPhaseSeqTy evPhaseRef
    decl = (uncurry <$> (mkDAssignment <$> evPhaseSeqTy) <*>)

replicatePhase
  :: Has (Gensym Emitter) sig m
  => Ty -> PhaseRef -> m PhaseRef
replicatePhase tyRepr PhaseRef{prBase, prRepr} =
  liftM2 PhaseRef prBase' prRepr'
  where
    prBase' = gensymBinding prBase TNat
    prRepr' = gensymBinding prRepr tyRepr

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
    [ ((, tyKetByQTy qt) <$>) <$> findEmitBasesByRanges ranges
    | (Partition{ranges}, qt, _) <- inst ]
  dumpSt "MethodParams"
  pure $ pureVars ++ (uncurry Binding <$> vqEmits) ++ pVars


codegenPhaseBinding :: PhaseRef -> Ty -> [Binding']
codegenPhaseBinding PhaseRef{prBase, prRepr} ty =
  [ Binding prBase TNat , Binding prRepr ty ]
  
