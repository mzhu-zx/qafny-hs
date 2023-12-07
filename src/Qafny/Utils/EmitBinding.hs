{-# LANGUAGE
    ConstraintKinds
  , FlexibleContexts
  , NamedFieldPuns
  , TupleSections
  , TypeApplications
  , TypeOperators
  #-}
module Qafny.Utils.EmitBinding
  (genEDStUpdatePhase, findED)
where

import           Control.Lens
    (at, (?~), (^.), (^?!))
import           Control.Monad
    (forM, liftM2, replicateM)
import           Data.Bifunctor
    (second)
import           Data.Functor
    ((<&>))
import qualified Data.Map.Strict          as Map
import           Data.Maybe
    (fromMaybe, mapMaybe)
import qualified Data.Set                 as Set
import           Data.Sum
import           Text.Printf
    (printf)

import           Effect.Gensym
    (Gensym, gensym)
import           Qafny.Env
    (EmitState, RangeOrLoc, TState, emitSt)
import           Qafny.Partial
    (Reducible (reduce))
import           Qafny.Syntax.AST
import           Qafny.Syntax.EmitBinding
import           Qafny.TypeUtils
    (isEN, typingPhaseEmitReprN, typingQEmit)
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
-- to the emit symbol state w/ the __Gensym Emitter__ effect.
-- $doc
--------------------------------------------------------------------------------

type GensymWithState sig m =
  (Has (Gensym Emitter) sig m , Has (State TState) sig m)

genPhaseRefByDegree
  :: ( Has (Gensym Emitter) sig m
     )
  => Int -> RangeOrLoc -> m (Maybe PhaseRef)
genPhaseRefByDegree 0 _ = return Nothing
genPhaseRefByDegree n r =
  Just <$> liftM2 mkPhaseRef (gensym (EmPhaseSeq r n)) (gensym (EmPhaseSeq r n))

-- | Generate a /complete/ 'EmitData' of a Range and manage it within the 'emitSt'
genEDStByRange :: GensymWithState sig m => QTy -> Int -> Range -> m EmitData
genEDStByRange qt i r = do
  vB  <- gensym $ EmBaseSeq r qt
  vmP <- genPhaseRefByDegree i (inj r)
  let ed =  EmitData { evPhase = vmP
                     , evBasis = Just vB
                     , evAmp   = Nothing
                     }
  emitSt %= (at (inj r) ?~ ed)
  return ed


-- | Generate a /complete/ 'EmitData' of a Partition, managed 'emitSt'
--
genEDStByLoc
  :: GensymWithState sig m
  => Loc -> Int -> QTy -> [(Range, Int)] -> m (EmitData, [(Range, EmitData)])
genEDStByLoc l iLoc qt ris = do
  rAndEDs <- sequence [ (r,) <$> genEDStByRange qt i r | (r, i) <- ris ]
  vMP <- genPhaseRefByDegree iLoc (inj l)
  let edL = mtEmitData { evPhase = vMP }
  emitSt %= (at (inj l) ?~ edL)
  return ( edL , rAndEDs )


-- | Generate an 'EmitData' w/o Phase, managed by 'emitSt'
genEDStSansPhase
  :: GensymWithState sig m
  => Loc -> QTy -> [Range] -> m (EmitData, [(Range, EmitData)])
genEDStSansPhase l qt = genEDStByLoc l 0 qt . ((, 0) <$>)

-- | Update by appending to entries in emitSt
appendEDSt
  :: StateMayFail sig m
  => RangeOrLoc -> EmitData -> m EmitData
appendEDSt rl ed = do
  emitSt %= Map.adjust (<> ed) rl
  findED rl

-- | Update an existing EmitData by generating phase for it.
genEDStUpdatePhase
  :: ( GensymWithState sig m
     , Has (Error String) sig m
     )
  => RangeOrLoc -> Int -> m EmitData
genEDStUpdatePhase rl i  = do
  evPhase <- genPhaseRefByDegree i rl
  appendEDSt rl (mtEmitData {evPhase})

-- ** Getters
type StateMayFail sig m =
  (Has (Error String) sig m , Has (State TState) sig m)

findED :: StateMayFail sig m => RangeOrLoc -> m EmitData
findED rl = do
  ed <- use emitSt <&> (^. at rl)
  maybe (complain =<< use emitSt) return ed
  where
    complain st = throwError @String $
      printf "%s cannot be found in emitSt!\n%s" (show rl) (show st)


-- -- | Generate a varaible from a 'Range' and its 'QTy' and add the corresponding
-- -- 'Binding' into 'emitSt'
-- gensymEmitRangeQTy
--   :: ( Has (Gensym Emitter) sig m
--      , Has (State TState) sig m
--      )
--   => Range -> QTy-> m Var
-- gensymEmitRangeQTy r qty = gensymEmitRB (rbindingOfRange r (inj qty))

-- -- | Generate a new variable for phase representation and returns a new PhaseTy
-- -- that refers to the new variable.
-- gensymEmitRangePTyRepr
--   :: ( Has (Gensym Emitter) sig m
--      , Has (State TState) sig m
--      , Has (Error String) sig m
--      )
--   => Range -> Int -> m PhaseTy
-- gensymEmitRangePTyRepr _ 0 = pure PT0
-- gensymEmitRangePTyRepr r i = do
--   vBase <- findEmitEB (BBinding (inj r, i))
--   phaseTyN i vBase <$> gensymEmitEB (RBinding (r, inj i))

-- -- | Generate a new Phase Type from the range and its degree and manage it in
-- -- the global store.
-- gensymEmitRangeDegree
--   :: ( Has (Gensym Emitter) sig m
--      , Has (State TState) sig m
--      )
--   => Range -> Int-> m PhaseTy
-- gensymEmitRangeDegree _ 0 =
--   return PT0
-- gensymEmitRangeDegree r i = do
--   vRepr <- gensymEmitEB (RBinding (r, inj i))
--   vBase <- gensymEmitEB (BBinding (inj r, i))
--   return . PTN i $ PhaseRef { prBase=vBase, prRepr=vRepr }

-- gensymEmitLocDegree
--   :: ( Has (Gensym Emitter) sig m
--      , Has (State TState) sig m
--      )
--   => Loc -> Int-> m PhaseTy
-- gensymEmitLocDegree _ 0 =
--   return PT0
-- gensymEmitLocDegree r i = do
--   vRepr <- gensymEmitEB (LBinding (r, i))
--   vBase <- gensymEmitEB (BBinding (inj r, i))
--   return . PTN i $ PhaseRef { prBase=vBase, prRepr=vRepr }


-- gensymEmitEB
--   :: ( Has (Gensym Emitter) sig m , Has (State TState) sig m)
--   => EmitBinding -> m Var
-- gensymEmitEB rb = do
--   name <- gensym rb
--   emitSt %= (at rb ?~ name)
--   return name

-- {-# DEPRECATED gensymEmitRB "Use gensymEmitEB instead!" #-}
-- gensymEmitRB
--   :: ( Has (Gensym Emitter) sig m
--      , Has (State TState) sig m
--      )
--   => EmitBinding -> m Var
-- gensymEmitRB = gensymEmitEB

-- -- | Similar to 'gensymEmitRangeQTy' but gensym without adding it the 'emitSt'
-- gensymRangeQTy
--   :: ( Has (Gensym Emitter) sig m
--      )
--   => Range -> QTy -> m Var
-- gensymRangeQTy r qty =
--   gensym $ rbindingOfRange r (inj qty)

-- gensymEmitPartitionQTy
--   :: ( Has (Gensym Emitter) sig m
--      , Has (State TState) sig m
--      )
--   => Partition -> QTy -> m [Var]
-- gensymEmitPartitionQTy p qty =
--   forM (unpackPart p) (`gensymEmitRangeQTy` qty)

-- liftPartition :: Monad m => (Range -> m b) -> Partition -> m [b]
-- liftPartition f p = forM (unpackPart p) f

-- findEmitEB
--   :: ( Has (State TState) sig m
--      , Has (Error String) sig m
--      )
--   => EmitBinding -> m Var
-- findEmitEB eb = do
--   st <- use emitSt
--   rethrowMaybe
--     (return (st ^. at eb)) $
--     printf "the binding `%s` cannot be found in the renaming state.\n%s"
--       (show eb)
--       (show st)

-- findEmitRangeDegree
--   :: ( Has (State TState) sig m
--      , Has (Error String) sig m
--      )
--   => Range -> Int -> m PhaseTy
-- findEmitRangeDegree r 0 = return PT0
-- findEmitRangeDegree r i = do
--   let rBinding = RBinding (r, inj i)
--       bBinding = BBinding (inj r, i)
--   st <- use emitSt
--   let vReprM = st ^. at rBinding
--   let vBaseM = st ^. at bBinding
--   case (,) <$>  vReprM <*> vBaseM of
--     Just (vRepr', vBase') -> return . PTN i $
--       PhaseRef { prRepr=vRepr', prBase=vBase' }
--     Nothing -> throwError @String $
--       printf "the phase binding of %s : %d cannot be found in the renaming state.\n%s"
--       (show r) i (show st)

-- findEmitLocDegree
--   :: ( Has (State TState) sig m
--      , Has (Error String) sig m
--      )
--   => Loc -> Int -> m PhaseTy
-- findEmitLocDegree l 0 = return PT0
-- findEmitLocDegree l i = do
--   let rBinding = LBinding (l, i)
--       bBinding = BBinding (inj l, i)
--   st <- use emitSt
--   let vReprM = st ^. at rBinding
--   let vBaseM = st ^. at bBinding
--   case (,) <$>  vReprM <*> vBaseM of
--     Just (vRepr', vBase') -> return . PTN i $
--       PhaseRef { prRepr=vRepr', prBase=vBase' }
--     Nothing -> throwError @String $
--       printf "the phase binding of %s : %d cannot be found in the renaming state.\n%s"
--       (show l) i (show st)


-- findEmitRangeQTy
--   :: ( Has (State TState) sig m
--      , Has (Error String) sig m
--      )
--   => Range -> QTy -> m Var
-- findEmitRangeQTy r qty = do
--   let rb = rbindingOfRange r (inj qty)
--   st <- use emitSt
--   rethrowMaybe
--     (return (st ^. at rb)) $
--     printf "the binding `%s` cannot be found in the renaming state.\n%s"
--       (show rb)
--       (show st)

-- findEmitBindingsFromPartition
--   :: ( Has (State TState) sig m
--      , Has (Error String) sig m
--      )
--   => Partition -> QTy -> m [Binding']
-- findEmitBindingsFromPartition part q =
--   forM (unpackPart part) $ (uncurry Binding . (, typingQEmit q) <$>) . (`findEmitRangeQTy` q)


-- findEmitVarsFromPartition
--   :: ( Has (State TState) sig m
--      , Has (Error String) sig m
--      )
--   => Partition -> QTy -> m [Var]
-- findEmitVarsFromPartition part q =
--   forM (unpackPart part) (`findEmitRangeQTy` q)



-- modifyEmitRangeQTy
--   :: ( Has (State TState) sig m )
--   => Range -> QTy -> Var -> m ()
-- modifyEmitRangeQTy r qty name = do
--   let rb = rbindingOfRange r (inj qty)
--   emitSt %= (at rb ?~ name)


-- removeEmitPartitionQTys
--   :: ( Has (State TState) sig m)
--   => Partition -> QTy -> m ()
-- removeEmitPartitionQTys p qty = do
--   removeEmitRangeQTys ((, qty) <$> unpackPart p)

-- removeEmitRangeQTys
--   :: ( Has (State TState) sig m)
--   => [(Range, QTy)] -> m ()
-- removeEmitRangeQTys rqts = do
--   let bs = uncurry rbindingOfRange <$> (rqts <&> second inj)
--   emitSt %= (`Map.withoutKeys` Set.fromList bs)


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
