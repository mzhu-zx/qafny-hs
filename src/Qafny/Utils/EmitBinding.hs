{-# LANGUAGE
    ConstraintKinds
  , FlexibleContexts
  , NamedFieldPuns
  , TupleSections
  , TypeApplications
  , TypeOperators
  #-}
module Qafny.Utils.EmitBinding
  ( -- * Gensyms
    gensymBinding
  , genEmStUpdatePhase, genEmStByRange, genEmStByRanges, genEmStFromLocus
  , genEmStUpdatePhaseFromLocus
  , genEmStUpdateKets
    -- * Gensyms w/o State
  , genEmByRange
    -- * Query
  , findEm, findEms
  , visitEm, visitEms, visitEmBasis, visitEmsBasis
  , findVisitEm, findVisitEms
  , findEmitBasesByRanges, findEmitBasisByRange
    -- * Deletion
  , deleteEm, deleteEms, deleteEmPartition
    -- * Update
  , appendEmSt
    -- * Helper
  , fsts, extractEmitablesFromLocus
  )
where

import           Control.Lens
    (at, sans, (?~), (^.))
import           Control.Monad
    (liftM2, zipWithM, zipWithM_, (>=>))
import           Data.Functor
    ((<&>))
import qualified Data.Map.Strict          as Map
import qualified Data.Set                 as Set
import           Data.Sum
import           Text.Printf
    (printf)

import           Control.Effect.Lens
import           Data.Maybe
    (catMaybes)
import           Qafny.Effect
import           Qafny.Syntax.AST
import           Qafny.Syntax.EmitBinding
import           Qafny.Syntax.IR
import           Qafny.TypeUtils
    (tyAmp, tyKetByQTy, typingPhaseEmitReprN)
import           Qafny.Utils.Utils
    (errTrace)

--------------------------------------------------------------------------------
-- * Gensym Utils
--
-- $doc
-- The following functions operate on a 'Range'/'Loc' and a 'QTy', form a
-- `Binding` to be normalized to a variable name, perform modification and query
-- to the emit symbol state w/ the __Gensym Emitter__ effect.
-- $doc
--------------------------------------------------------------------------------

-- ** Basics

gensymBinding :: (Has (Gensym Emitter) sig m) => Var -> Ty -> m (Var, Ty)
gensymBinding v t = (,t) <$> gensym (EmAnyBinding v t)

genKetsByQTy :: Has (Gensym Emitter) sig m => QTy -> [Range] -> m [Maybe (Var, Ty)]
genKetsByQTy qty ranges =
  maybe (return (replicate (length ranges) Nothing)) go tyKets
  where
    go ty = mapM (go' ty) ranges
    go' ty r = Just . (,ty) <$> gensym (EmBaseSeq r ty)
    tyKets = tyKetByQTy qty

genKet :: Has (Gensym Emitter) sig m => QTy -> Range -> m (Maybe (Var, Ty))
genKet qty range =
  mapM go tyKets
  where
    go ty = (,ty) <$> gensym (EmBaseSeq range ty)
    tyKets = tyKetByQTy qty

-- | Generate a phase representation
-- TODO: a lot of redundency from changes, refactor this
genPhase
  :: Has (Gensym Emitter) sig m
  => QTy -> Int -> Loc -> m (Maybe (PhaseRef, Ty))
genPhase TNor _ loc = return Nothing
genPhase _ 0 _ = return Nothing
genPhase _ n r
  | n < 0 = return Nothing
  | otherwise = do
      pr <- liftM2 PhaseRef (gensym (EmPhaseBase r)) (gensym (EmPhaseSeq r n))
      return $ Just (pr, typingPhaseEmitReprN n)

genAmp :: Has (Gensym Emitter) sig m
       => QTy -> Loc -> m (Maybe (Var, Ty))
genAmp qty l =
  mapM go $ tyAmp qty
  where
    go ty = gensym (EmAmplitude l qty) <&> (, ty)

-- ** Basics but Stateful

-- | Generate a /complete/ 'EmitData' of a Range and manage it within the 'emitSt'
genEmStByRange ::  GensymEmitterWithState sig m => QTy -> Range -> m EmitData
genEmStByRange qt r = do
  ed <- genEmByRange qt r
  emitSt %= (at (inj r) ?~ ed)
  return ed

genEmByRange :: (Has (Gensym Emitter) sig m) => QTy -> Range -> m EmitData
genEmByRange qt r = do
  b <- genKet qt r
  let ed =  EmitData { evPhaseRef   = Nothing
                     , evBasis      = b
                     , evAmp        = Nothing -- amplitude is not managed by range
                     }
  return ed

-- | Generate EmitData for a list of ranges and manage it in state. 
genEmStByRanges
  :: ( GensymEmitterWithState sig m
     , Traversable t
     )
  => QTy -> t Range -> m (t (Range, EmitData))
genEmStByRanges qt = mapM go
  where
    go r = (r,) <$> genEmStByRange qt r

-- | Generate an `EmitData` from a Locus including both amplitude, range and
-- phase.
genEmStFromLocus
  :: ( GensymEmitterWithState sig m
     , Traversable t
     )
  => LocusT t -> m (EmitData, t (Range, EmitData))
genEmStFromLocus Locus{loc, part=Partition{ranges}, qty, degrees} = do
  rEms <- genEmStByRanges qty ranges
  p <- genPhase qty (head degrees) loc
  a <- genAmp qty loc
  let edL = mtEmitData { evPhaseRef = p }
  emitSt %= (at (inj loc) ?~ edL)
  return ( edL , rEms )

-- | Update existing `EmitData` based on degree information from a Locus.
genEmStUpdatePhaseFromLocus
  :: ( GensymEmitterWithState sig m
     , Has (Error String) sig m
     )
  => Locus -> m [EmitData]
genEmStUpdatePhaseFromLocus Locus{loc, part=Partition{ranges=rs}, qty, degrees} =
  zipWithM (genEmStUpdatePhase qty) degrees [loc]

-- -- | Generate an 'EmitData' w/o Phase, managed by 'emitSt'
-- genEmStSansPhaseByLocAndRange
--   :: GensymEmitterWithState sig m
--   => Loc -> QTy -> [Range] -> m (EmitData, [(Range, EmitData)])
-- genEmStSansPhaseByLocAndRange l qt = genEmStByLoc l (-1) qt . ((, -1) <$>)

-- {-# INLINE genEmStByRangesSansPhase #-}
-- genEmStByRangesSansPhase
--   :: GensymEmitterWithState sig m
--   => QTy -> [Range] -> m [(Range, EmitData)]
-- genEmStByRangesSansPhase qt = genEmStByRanges qt . ((, -1) <$>)

-- -- | Same as `genEmStByRangesSansPhase` but without `Range` indices
-- genEmStByRangesSansPhase'
--   :: GensymEmitterWithState sig m
--   => QTy -> [Range] -> m [EmitData]
-- genEmStByRangesSansPhase' qt = ((snd <$>) <$>) . genEmStByRanges qt . ((, -1) <$>)

-- genEmStSansPhaseByRanges
--   :: GensymEmitterWithState sig m
--   => QTy -> [Range] -> m [(Range, EmitData)]
-- genEmStSansPhaseByRanges = genEmStByRangesSansPhase

-- | Append the given `EmitData` to the given entry.
appendEmSt
  :: StateMayFail sig m
  => RangeOrLoc -> EmitData -> m EmitData
appendEmSt rl ed = do
  emitSt %= Map.adjust (<> ed) rl
  findEm rl

-- | Update an existing `EmitData` by generating a phase from a given degree.
genEmStUpdatePhase
  :: GensymEmitterWithStateError sig m
  => QTy -> Int -> Loc -> m EmitData
genEmStUpdatePhase qt i l  = errTrace "`genEmStUpdatePhase`" $ do
  evPhaseRef  <- genPhase qt i l
  appendEmSt (inj l) (mtEmitData {evPhaseRef})

genEmStUpdateKets
  :: GensymEmitterWithStateError sig m
  => QTy -> [Range] -> m [Var]
genEmStUpdateKets qty ranges = do
  vtys <- genKetsByQTy qty ranges
  zipWithM_ (\r evBasis -> appendEmSt (inj r) (mtEmitData{evBasis}))
    ranges vtys
  return (fsts (catMaybes vtys))


-- ** Getters
findEm :: StateMayFail sig m => RangeOrLoc -> m EmitData
findEm rl = do
  ed <- use emitSt <&> (^. at rl)
  maybe (complain =<< use emitSt) return ed
  where
    complain st = throwError @String $
      printf "%s cannot be found in emitSt!\n%s" (show rl) (show st)

findEms :: StateMayFail sig m => [RangeOrLoc] -> m [EmitData]
findEms = mapM findEm


-- | Find the EmitData and visit it with an accessor
visitEm :: Has (Error String) sig m => (EmitData -> Maybe a) -> EmitData -> m a
visitEm evF ed = do
  maybe (complain ed) return (evF ed)
  where
    complain ed' = throwError @String $
      printf "Attempting to access non-Just field in %s" (show ed')

visitEms
  :: Has (Error String) sig m
  => (EmitData -> Maybe a) -> [EmitData] -> m [a]
visitEms f = mapM (visitEm f)

findVisitEm
  :: StateMayFail sig m
  => (EmitData -> Maybe c) -> RangeOrLoc -> m c
findVisitEm evF = findEm >=> visitEm evF

findVisitEms
  :: StateMayFail sig m
  => (EmitData -> Maybe c) -> [RangeOrLoc] -> m [c]
findVisitEms f = errTrace "findVisitEms" .
  mapM (findVisitEm f)


-- *** Shorthands
visitEmBasis :: Has (Error String) sig m => EmitData -> m (Var, Ty)
visitEmBasis = visitEm evBasis

visitEmsBasis :: Has (Error String) sig m => [EmitData] -> m [(Var, Ty)]
visitEmsBasis = mapM visitEmBasis

findVisitEmsBasis
  :: StateMayFail sig m
  => [RangeOrLoc] -> m [(Var, Ty)]
findVisitEmsBasis = findVisitEms evBasis

findEmitBasisByRange
  :: StateMayFail sig m
  => Range -> m (Var, Ty)
findEmitBasisByRange = findVisitEm evBasis . inj

findEmitBasesByRanges
  :: StateMayFail sig m
  => [Range] -> m [(Var, Ty)]
findEmitBasesByRanges = findVisitEms evBasis . (inj <$>)

-- ** Destructor
deleteEm :: (Has (State TState) sig m) => RangeOrLoc -> m ()
deleteEm rl = emitSt %= sans rl

deleteEms :: (Has (State TState) sig m) => [RangeOrLoc] -> m ()
deleteEms s = emitSt %= (`Map.withoutKeys` Set.fromList s)

deleteEmPartition :: (Has (State TState) sig m) => Loc -> [Range] -> m ()
deleteEmPartition l rs =
  deleteEms (inj l : (inj <$> rs))

-- ** Helpers
fsts :: [(a, b)] -> [a]
fsts = (fst <$>)


extractEmitablesFromLocus :: StateMayFail sig m => Locus -> m [(Var, Ty)]
extractEmitablesFromLocus Locus{loc, part} = do
  emLoc <- findEm (inj loc)
  emRanges <- (findEm . inj) `mapM` ranges part
  return $ concatMap extractEmitables (emLoc : emRanges)
