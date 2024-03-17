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
  , genEmStSansPhaseByRanges
  , genEmStByRangesSansPhase, genEmStByRangeSansPhase
  , genEmStByRangesSansPhase'
  , genEmStUpdateKets
    -- * Gensyms w/o State
  , genEmByRange
  , genEmByRangeSansPhase
    -- * Wrappers for Emitter
  , genPhaseTyByDegree
    -- * Query
  , findEm, findEms
  , visitEm, visitEms, visitEmBasis, visitEmsBasis
  , findVisitEm, findVisitEms
  , findVisitEmsBasis
  , findEmitBasesByRanges, findEmitBasisByRange
    -- * Deletion
  , deleteEm, deleteEms, deleteEmPartition
    -- * Update
  , appendEmSt
  )
where

import           Control.Lens
    (at, sans, (?~), (^.))
import           Control.Monad
    (forM, liftM2, zipWithM, (>=>), void, forM_, zipWithM_)
import           Data.Functor
    ((<&>))
import qualified Data.Map.Strict          as Map
import qualified Data.Set                 as Set
import           Data.Sum
import           Text.Printf
    (printf)

import           Control.Effect.Lens
import           Qafny.Effect
import           Qafny.Syntax.AST
import           Qafny.Syntax.EmitBinding
import           Qafny.Syntax.IR
    (Locus (..), RangeOrLoc, TState, emitSt)
import           Qafny.TypeUtils
    (emitTypeFromDegree, isEN, tyKetByQTy, typingPhaseEmitReprN)
import           Qafny.Utils.Utils
    (errTrace, haveSameLength, onlyOne)

--------------------------------------------------------------------------------
-- * Gensym Utils
--
-- $doc
-- The following functions operate on a 'Range'/'Loc' and a 'QTy', form a
-- `Binding` to be normalized to a variable name, perform modification and query
-- to the emit symbol state w/ the __Gensym Emitter__ effect.
-- $doc
--------------------------------------------------------------------------------

gensymBinding :: (Has (Gensym Emitter) sig m) => Var -> Ty -> m Var
gensymBinding v t = gensym (EmAnyBinding v t)

genKetsByQTy :: Has (Gensym Emitter) sig m => QTy -> [Range] -> m ([Var], Ty)
genKetsByQTy qty ranges =
  (, tyKets) <$> mapM genV ranges
  where
    genV r = gensym (EmBaseSeq r qty)
    tyKets = tyKetByQTy qty


genPhaseTyByDegree
  :: Has (Gensym Emitter) sig m
  => Int -> RangeOrLoc -> m (Maybe PhaseRef, Maybe Ty)
genPhaseTyByDegree 0 _ = return (Nothing, Nothing)
genPhaseTyByDegree n r
  | n < 0 = return (Nothing, Nothing)
  | otherwise = do
      pr <- liftM2 PhaseRef (gensym (EmPhaseBase r)) (gensym (EmPhaseSeq r n))
      return (Just pr, Just (typingPhaseEmitReprN n))


-- | Generate a /complete/ 'EmitData' of a Range and manage it within the 'emitSt'
genEmStByRange ::  GensymEmitterWithState sig m => QTy -> Int -> Range -> m EmitData
genEmStByRange qt i r = do
  ed <- genEmByRange qt i r
  emitSt %= (at (inj r) ?~ ed)
  return ed

genEmByRange :: (Has (Gensym Emitter) sig m) => QTy -> Int -> Range -> m EmitData
genEmByRange qt i r = do
  vB  <- gensym $ EmBaseSeq r qt
  (vmP, tyP) <- genPhaseTyByDegree i (inj r)
  let ed =  EmitData { evPhaseRef   = vmP
                     , evPhaseSeqTy = tyP
                     , evBasis      = Just vB
                     , evBasisTy    = Just $ tyKetByQTy qt
                     , evAmp        = Nothing
                     }
  return ed


genEmStByRangeSansPhase ::  GensymEmitterWithState sig m => QTy -> Range -> m EmitData
genEmStByRangeSansPhase qt = genEmStByRange qt 0

genEmByRangeSansPhase
  :: (Has (Gensym Emitter) sig m)
  => QTy -> Range -> m EmitData
genEmByRangeSansPhase qt = genEmByRange qt 0


genEmStByRanges
  :: GensymEmitterWithState sig m
  => QTy -> [(Range, Int)] -> m [(Range, EmitData)]
genEmStByRanges qt ris =
  sequence [ (r,) <$> genEmStByRange qt i r | (r, i) <- ris ]

-- | Generate a /complete/ 'EmitData' of a Partition, managed 'emitSt'
--
genEmStByLoc
  :: GensymEmitterWithState sig m
  => Loc -> Int -> QTy -> [(Range, Int)] -> m (EmitData, [(Range, EmitData)])
genEmStByLoc l iLoc qt ris = do
  rAndEms <- sequence [ (r,) <$> genEmStByRange qt i r | (r, i) <- ris ]
  (vMP, tyP) <- genPhaseTyByDegree iLoc (inj l)
  let edL = mtEmitData { evPhaseRef = vMP, evPhaseSeqTy = tyP }
  emitSt %= (at (inj l) ?~ edL)
  return ( edL , rAndEms )


-- | Generate an `EmitData` of a Partition from a Locus.
-- In particular, generate degree and phases based on its qt
genEmStFromLocus
  :: ( GensymEmitterWithState sig m
     , Has (Error String) sig m
     )
  => Locus -> m (EmitData, [(Range, EmitData)])
genEmStFromLocus Locus{loc=l, part=Partition{ranges}, qty, degrees=is} = do
  (il, ir) <- if isEN qty
    then (, repeat (-1)) <$> onlyOne throwError is
    else (-1, is)  <$ haveSameLength is ranges
  genEmStByLoc l il qty $ zip ranges ir

-- | Update existing `EmitData` based on degree information from a Locus.
genEmStUpdatePhaseFromLocus
  :: ( GensymEmitterWithState sig m
     , Has (Error String) sig m
     )
  => Locus -> m [EmitData]
genEmStUpdatePhaseFromLocus Locus{loc, part=Partition{ranges=rs}, qty, degrees} = do
  is' <- if isEN qty
    then (: repeat (-1)) <$> onlyOne throwError degrees
    else (-1 : degrees)  <$ haveSameLength degrees rs
  zipWithM genEmStUpdatePhase degrees (inj loc : (inj <$> rs))


-- | Generate an 'EmitData' w/o Phase, managed by 'emitSt'
genEmStSansPhaseByLocAndRange
  :: GensymEmitterWithState sig m
  => Loc -> QTy -> [Range] -> m (EmitData, [(Range, EmitData)])
genEmStSansPhaseByLocAndRange l qt = genEmStByLoc l (-1) qt . ((, -1) <$>)

{-# INLINE genEmStByRangesSansPhase #-}
genEmStByRangesSansPhase
  :: GensymEmitterWithState sig m
  => QTy -> [Range] -> m [(Range, EmitData)]
genEmStByRangesSansPhase qt = genEmStByRanges qt . ((, -1) <$>)

-- | Same as `genEmStByRangesSansPhase` but without `Range` indices
genEmStByRangesSansPhase'
  :: GensymEmitterWithState sig m
  => QTy -> [Range] -> m [EmitData]
genEmStByRangesSansPhase' qt = ((snd <$>) <$>) . genEmStByRanges qt . ((, -1) <$>)



genEmStSansPhaseByRanges
  :: GensymEmitterWithState sig m
  => QTy -> [Range] -> m [(Range, EmitData)]
genEmStSansPhaseByRanges = genEmStByRangesSansPhase

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
  => Int -> RangeOrLoc -> m EmitData
genEmStUpdatePhase i rl  = errTrace "`genEmStUpdatePhase`" $ do
  (evPhaseRef, evPhaseSeqTy)  <- genPhaseTyByDegree i rl
  appendEmSt rl (mtEmitData {evPhaseRef, evPhaseSeqTy})

genEmStUpdateKets
  :: GensymEmitterWithStateError sig m
  => QTy -> [Range] -> m [Var]
genEmStUpdateKets qty ranges = do
  (vs, ty) <- genKetsByQTy qty ranges
  let evBasisTy = Just ty
  zipWithM_ (\r evBasis -> appendEmSt (inj r) (mtEmitData{evBasis, evBasisTy}))
    ranges (Just <$> vs)
  return vs
  

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
visitEmBasis :: Has (Error String) sig m => EmitData -> m Var
visitEmBasis = visitEm evBasis

visitEmsBasis :: Has (Error String) sig m => [EmitData] -> m [Var]
visitEmsBasis = mapM visitEmBasis

findVisitEmsBasis
  :: StateMayFail sig m
  => [RangeOrLoc] -> m [Var]
findVisitEmsBasis = findVisitEms evBasis

findEmitBasisByRange
  :: StateMayFail sig m
  => Range -> m Var
findEmitBasisByRange = findVisitEm evBasis . inj

findEmitBasesByRanges
  :: StateMayFail sig m
  => [Range] -> m [Var]
findEmitBasesByRanges = findVisitEms evBasis . (inj <$>)


-- ** Destructor
deleteEm :: (Has (State TState) sig m) => RangeOrLoc -> m ()
deleteEm rl = emitSt %= sans rl

deleteEms :: (Has (State TState) sig m) => [RangeOrLoc] -> m ()
deleteEms s = emitSt %= (`Map.withoutKeys` Set.fromList s)

deleteEmPartition :: (Has (State TState) sig m) => Loc -> [Range] -> m ()
deleteEmPartition l rs =
  deleteEms (inj l : (inj <$> rs))
