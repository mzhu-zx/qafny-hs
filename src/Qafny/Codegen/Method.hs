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
    (join, liftM, liftM2, liftM3)
import           Data.Maybe
    (catMaybes)
import           Effect.Gensym
    (gensym)
import           Qafny.Effect
import           Qafny.Syntax.AST
import           Qafny.Syntax.ASTFactory
    (mkAssignment, mkDAssignment)
import           Qafny.Syntax.ASTUtils
    (getPhaseRefMaybe, phaseRefToTy)
import           Qafny.Syntax.EmitBinding
    (EmitData (..), Emitter (EmAnyBinding))
import           Qafny.Syntax.IR
import           Qafny.TypeUtils
    (bindingsFromPtys, typingPhaseEmitReprN, typingQEmit)
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
  ed@EmitData{evBasis, evBasisTy, evPhaseSeqTy, evPhaseTy, evAmp} =
  do evBasis'   <- sequence evBasisM
     evPhaseTy' <- sequence evPhaseM
     let refs = liftM2 (,) (phaseRefOf evPhaseTy') (phaseRefOf evPhaseTy)
     -- let evPhase' = uncurry mkPhaseRef <$> prVars
     emitSt %= (at rl ?~ ed{evBasis=evBasis', evPhaseTy=evPhaseTy'})
     return $ catMaybes [ liftM3 mkDAssignment evBasisTy evBasis' evBasis
                        , uncurry (mkDAssignment TNat) . bimap prBase prBase <$> refs
                        , decl $ bimap prRepr prRepr <$> refs
                        ]
  where
    evBasisM = liftM2 gensymBinding evBasis evBasisTy
    evPhaseM = replicatePhaseTy <$> evPhaseTy
    phaseRefOf = (getPhaseRefMaybe =<<)
    decl = (uncurry <$> (mkDAssignment <$> evPhaseSeqTy) <*>)

replicatePhaseTy
  :: GensymEmitterWithState sig m
  => PhaseTy -> m PhaseTy
replicatePhaseTy PT0 = return PT0
replicatePhaseTy (PTN n PhaseRef{prBase, prRepr}) =
  PTN n <$> liftM2 mkPhaseRef prBase' prRepr'
  where
    prBase' = gensymBinding prBase TNat
    prRepr' = gensymBinding prRepr (typingPhaseEmitReprN n)

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
  trace "* codegenMethodParams"
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
