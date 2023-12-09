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
import           Control.Algebra
    (Has)
import           Control.Effect.Error
    (Error)
import           Control.Effect.Lens
import           Control.Effect.Trace
    (Trace, trace)

-- data
import           Control.Lens
    (at, sans, (?~), (^.))
import qualified Data.Map.Strict          as Map

-- Qafny
import           Control.Monad
    (liftM, liftM2)
import           Data.Maybe
    (catMaybes)
import           Effect.Gensym
    (gensym)
import           Qafny.Env
import           Qafny.Syntax.AST
import           Qafny.Syntax.ASTFactory
    (mkAssignment)
import           Qafny.Syntax.ASTUtils
    (phaseRefToTy)
import           Qafny.Syntax.EmitBinding
    (EmitData (..), Emitter (EmAnyBinding))
import           Qafny.TypeUtils
    (bindingsFromPtys, typingQEmit)
import           Qafny.Typing.Typing
    (collectPureBindings)
import           Qafny.Utils.EmitBinding
    (GensymWithState, StateMayFail, findEmitBasesByRanges, gensymBinding)
import           Qafny.Utils.Utils
    (dumpSt)

-- * Method related definitions


-- | Take the emit state and generate totally new emit symbols and emit
-- statements to match the translation
--
-- This is needed because you cannot mutate the parameter of a method.
-- An alternative is to copy the augument into a local variable where mutation
-- are allowed.
genEmitSt :: GensymWithState sig m => m [Stmt']
genEmitSt = do
  eSt <- use emitSt
  emitSt %= const Map.empty
  concat <$> mapM (uncurry replicateEmitEntry) (Map.toList eSt)

replicateEmitEntry
  :: GensymWithState sig m
  => RangeOrLoc -> EmitData -> m [Stmt']
replicateEmitEntry rl
  ed@EmitData{evBasis, evBasisTy, evPhaseSeqTy, evPhase, evAmp} =
  do evBasis' <- sequence evBasisM
     prVars   <- sequence evPhaseM
     let evPhase' = uncurry mkPhaseRef <$> prVars
     emitSt %= (at rl ?~ ed{evBasis=evBasis', evPhase=evPhase'})
     return $ catMaybes [ liftM2 mkAssignment evBasis evBasis'
                        , uncurry mkAssignment <$> prVars
                        ]
  where
    evBasisM = liftM2 gensymBinding evBasis evBasisTy       
    evPhaseM = liftM2 replicatePhaseRef evPhaseSeqTy evPhase

    replicatePhaseRef tyRepr PhaseRef{prBase, prRepr} =
      liftM2 (,) (gensymBinding prBase TNat) (gensymBinding prRepr tyRepr)

-- | Generate method parameters from the method signature
codegenMethodParams
  :: ( StateMayFail sig m
     , Has Trace sig m
     )
  => MethodType -> [PhaseTy] -> m [Binding']
codegenMethodParams
  MethodType{ mtSrcParams=srcParams , mtInstantiate=instantiator}
  ptysResolved
  = do
  let pureVars = collectPureBindings srcParams
      qVars = [ (v, Range v 0 card) | MTyQuantum v card <- srcParams ]
      inst = instantiator $ Map.fromList qVars
      pVars = bindingsFromPtys ptysResolved
  trace $ "QVARS: " ++ show qVars
  trace $ "INSTANCE: " ++ show inst
  trace $ "PVars" ++ show pVars
  vqEmits <- concat <$> sequence
    [ ((, typingQEmit qt) <$>) <$> findEmitBasesByRanges ranges
    | (Partition{ranges}, qt, _) <- inst ]
  dumpSt "MethodParams"
  pure $ pureVars ++ (uncurry Binding <$> vqEmits) ++ pVars
