{-# LANGUAGE
    TupleSections
  , TypeApplications
  , TypeOperators
  #-}

module Qafny.Utils.EmitBinding where

import           Control.Lens
    (at, (?~), (^.))
import           Control.Monad
    (forM)
import           Data.Bifunctor
    (second)
import           Data.Functor
    ((<&>))
import qualified Data.Map.Strict          as Map
import           Data.Maybe
    (mapMaybe)
import qualified Data.Set                 as Set
import           Data.Sum
import           Text.Printf
    (printf)

import           Effect.Gensym
    (Gensym, gensym)
import           Qafny.Env
    (TState, emitSt)
import           Qafny.Partial
    (Reducible (reduce))
import           Qafny.Syntax.AST
import           Qafny.Syntax.EmitBinding
import           Qafny.TypeUtils
    (typingPhaseEmitReprN, typingQEmit)
import           Qafny.Utils.Utils
    (rethrowMaybe)

import           Control.Effect.Error
    (Error, throwError)
import           Control.Effect.Lens
import           Control.Effect.Reader
import           Control.Effect.State



--------------------------------------------------------------------------------
-- * Gensym Utils
--
-- $doc
-- The following functions operate on a 'Range'/'Loc' and a 'QTy', form a
-- `Binding` to be normalized to a variable name, perform modification and query
-- to the emit symbol state w/ the __Gensym EmitBinding__ effect.
-- $doc
--------------------------------------------------------------------------------

-- | Generate a /complete/ 'EmitData' of a Range and manage it within the 'emitSt'
gensymEmitDataStByRange
  :: ( Has (Gensym Emitter) sig m
     , Has (State TState) sig m
     )
  => Range -> QTy -> Int -> m EmitData
gensymEmitDataStByRange r qt i = do
  vB <- gensym $ EmBaseSeq r qt
  vP <- gensym $ EmPhaseSeq (inj r) i
  let ed =  EmitData { evPhase = Just vP
                     , evBasis = Just vB
                     , evAmp   = Nothing
                     }
  emitSt %= (inj r ?~ ed)
  return ed



-- | Generate a varaible from a 'Range' and its 'QTy' and add the corresponding
-- 'Binding' into 'emitSt'
gensymEmitRangeQTy
  :: ( Has (Gensym Emitter) sig m
     , Has (State TState) sig m
     )
  => Range -> QTy-> m Var
gensymEmitRangeQTy r qty = gensymEmitRB (rbindingOfRange r (inj qty))

-- | Generate a new variable for phase representation and returns a new PhaseTy
-- that refers to the new variable.
gensymEmitRangePTyRepr
  :: ( Has (Gensym EmitBinding) sig m
     , Has (State TState) sig m
     , Has (Error String) sig m
     )
  => Range -> Int -> m PhaseTy
gensymEmitRangePTyRepr _ 0 = pure PT0
gensymEmitRangePTyRepr r i = do
  vBase <- findEmitEB (BBinding (inj r, i))
  phaseTyN i vBase <$> gensymEmitEB (RBinding (r, inj i))

-- | Generate a new Phase Type from the range and its degree and manage it in
-- the global store.
gensymEmitRangeDegree
  :: ( Has (Gensym EmitBinding) sig m
     , Has (State TState) sig m
     )
  => Range -> Int-> m PhaseTy
gensymEmitRangeDegree _ 0 =
  return PT0
gensymEmitRangeDegree r i = do
  vRepr <- gensymEmitEB (RBinding (r, inj i))
  vBase <- gensymEmitEB (BBinding (inj r, i))
  return . PTN i $ PhaseRef { prBase=vBase, prRepr=vRepr }

gensymEmitLocDegree
  :: ( Has (Gensym EmitBinding) sig m
     , Has (State TState) sig m
     )
  => Loc -> Int-> m PhaseTy
gensymEmitLocDegree _ 0 =
  return PT0
gensymEmitLocDegree r i = do
  vRepr <- gensymEmitEB (LBinding (r, i))
  vBase <- gensymEmitEB (BBinding (inj r, i))
  return . PTN i $ PhaseRef { prBase=vBase, prRepr=vRepr }


gensymEmitEB
  :: ( Has (Gensym EmitBinding) sig m , Has (State TState) sig m)
  => EmitBinding -> m Var
gensymEmitEB rb = do
  name <- gensym rb
  emitSt %= (at rb ?~ name)
  return name

{-# DEPRECATED gensymEmitRB "Use gensymEmitEB instead!" #-}
gensymEmitRB
  :: ( Has (Gensym EmitBinding) sig m
     , Has (State TState) sig m
     )
  => EmitBinding -> m Var
gensymEmitRB = gensymEmitEB

-- | Similar to 'gensymEmitRangeQTy' but gensym without adding it the 'emitSt'
gensymRangeQTy
  :: ( Has (Gensym EmitBinding) sig m
     )
  => Range -> QTy -> m Var
gensymRangeQTy r qty =
  gensym $ rbindingOfRange r (inj qty)

gensymEmitPartitionQTy
  :: ( Has (Gensym EmitBinding) sig m
     , Has (State TState) sig m
     )
  => Partition -> QTy -> m [Var]
gensymEmitPartitionQTy p qty =
  forM (unpackPart p) (`gensymEmitRangeQTy` qty)

liftPartition :: Monad m => (Range -> m b) -> Partition -> m [b]
liftPartition f p = forM (unpackPart p) f

findEmitEB
  :: ( Has (State TState) sig m
     , Has (Error String) sig m
     )
  => EmitBinding -> m Var
findEmitEB eb = do
  st <- use emitSt
  rethrowMaybe
    (return (st ^. at eb)) $
    printf "the binding `%s` cannot be found in the renaming state.\n%s"
      (show eb)
      (show st)

findEmitRangeDegree
  :: ( Has (State TState) sig m
     , Has (Error String) sig m
     )
  => Range -> Int -> m PhaseTy
findEmitRangeDegree r 0 = return PT0
findEmitRangeDegree r i = do
  let rBinding = RBinding (r, inj i)
      bBinding = BBinding (inj r, i)
  st <- use emitSt
  let vReprM = st ^. at rBinding
  let vBaseM = st ^. at bBinding
  case (,) <$>  vReprM <*> vBaseM of
    Just (vRepr', vBase') -> return . PTN i $
      PhaseRef { prRepr=vRepr', prBase=vBase' }
    Nothing -> throwError @String $
      printf "the phase binding of %s : %d cannot be found in the renaming state.\n%s"
      (show r) i (show st)

findEmitLocDegree
  :: ( Has (State TState) sig m
     , Has (Error String) sig m
     )
  => Loc -> Int -> m PhaseTy
findEmitLocDegree l 0 = return PT0
findEmitLocDegree l i = do
  let rBinding = LBinding (l, i)
      bBinding = BBinding (inj l, i)
  st <- use emitSt
  let vReprM = st ^. at rBinding
  let vBaseM = st ^. at bBinding
  case (,) <$>  vReprM <*> vBaseM of
    Just (vRepr', vBase') -> return . PTN i $
      PhaseRef { prRepr=vRepr', prBase=vBase' }
    Nothing -> throwError @String $
      printf "the phase binding of %s : %d cannot be found in the renaming state.\n%s"
      (show l) i (show st)


findEmitRangeQTy
  :: ( Has (State TState) sig m
     , Has (Error String) sig m
     )
  => Range -> QTy -> m Var
findEmitRangeQTy r qty = do
  let rb = rbindingOfRange r (inj qty)
  st <- use emitSt
  rethrowMaybe
    (return (st ^. at rb)) $
    printf "the binding `%s` cannot be found in the renaming state.\n%s"
      (show rb)
      (show st)

findEmitBindingsFromPartition
  :: ( Has (State TState) sig m
     , Has (Error String) sig m
     )
  => Partition -> QTy -> m [Binding']
findEmitBindingsFromPartition part q =
  forM (unpackPart part) $ (uncurry Binding . (, typingQEmit q) <$>) . (`findEmitRangeQTy` q)


findEmitVarsFromPartition
  :: ( Has (State TState) sig m
     , Has (Error String) sig m
     )
  => Partition -> QTy -> m [Var]
findEmitVarsFromPartition part q =
  forM (unpackPart part) (`findEmitRangeQTy` q)



modifyEmitRangeQTy
  :: ( Has (State TState) sig m )
  => Range -> QTy -> Var -> m ()
modifyEmitRangeQTy r qty name = do
  let rb = rbindingOfRange r (inj qty)
  emitSt %= (at rb ?~ name)


removeEmitPartitionQTys
  :: ( Has (State TState) sig m)
  => Partition -> QTy -> m ()
removeEmitPartitionQTys p qty = do
  removeEmitRangeQTys ((, qty) <$> unpackPart p)

removeEmitRangeQTys
  :: ( Has (State TState) sig m)
  => [(Range, QTy)] -> m ()
removeEmitRangeQTys rqts = do
  let bs = uncurry rbindingOfRange <$> (rqts <&> second inj)
  emitSt %= (`Map.withoutKeys` Set.fromList bs)


-- * Codegen-related

--------------------------------------------------------------------------------
-- * EmitBinding Related

-- projEmitBindingRangeQTy :: EmitBinding -> Maybe (Range, QTy)
-- projEmitBindingRangeQTy (RBinding (r, Inl qty)) = Just (r, qty)
-- projEmitBindingRangeQTy _                       = Nothing


-- collectRQTyBindings ::[(EmitBinding, Var)] -> [((Range, QTy), Var)]
-- collectRQTyBindings = mapMaybe (\(e, v) -> projEmitBindingRangeQTy e <&> (, v))

-- bindingFromEmitBinding :: (EmitBinding, Var) -> Binding'
-- bindingFromEmitBinding = go
--   where
--     go (RBinding (_, Inl qty), v) = Binding v (typingQEmit qty)
--     go (RBinding (_, Inr dgr), v) = Binding v (typingPhaseEmitReprN dgr)
--     go (LBinding (_, dgr), v)     = Binding v (typingPhaseEmitReprN dgr)
--     go (BBinding (_, dgr), v)     = Binding v TNat
