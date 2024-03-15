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
  , genEDStUpdatePhase, genEDStByRange, genEDStByRanges, genEDStFromLocus
  , genEDStUpdatePhaseFromLocus
  , genEDStSansPhaseByRanges
  , genEDStByRangesSansPhase, genEDStByRangeSansPhase
  , genEDStByRangesSansPhase'
    -- * Gensyms w/o State
  , genEDByRange
  , genEDByRangeSansPhase
    -- * Query
  , findED
  , visitED, visitEDs, visitEDBasis, visitEDsBasis
  , findVisitED, findVisitEDs
  , findVisitEDsBasis
  , findEmitBasesByRanges, findEmitBasisByRange
    -- * Deletion
  , deleteED, deleteEDs, deleteEDPartition
    -- * Update
  , appendEDSt
  )
where

import           Control.Lens
    (at, sans, (?~), (^.))
import           Control.Monad
    (liftM2, zipWithM, (>=>))
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
    (RangeOrLoc, TState, emitSt, Locus(..))
import           Qafny.TypeUtils
    (emitTypeFromDegree, isEN, typingPhaseEmitReprN, typingQEmit)
import           Qafny.Utils.Utils
    (checkListCorr, errTrace, onlyOne)

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

genPhaseTyByDegree
  :: ( Has (Gensym Emitter) sig m
     )
  => Int -> RangeOrLoc -> m (Maybe PhaseTy, Maybe Ty)
genPhaseTyByDegree 0 _ = return (Just PT0, Nothing)
genPhaseTyByDegree n r
  | n < 0 = return (Nothing, Nothing)
  | otherwise =
    (, emitTypeFromDegree n) . Just . PTN n <$>
    liftM2 mkPhaseRef (gensym (EmPhaseBase r)) (gensym (EmPhaseSeq r n))


-- | Generate a /complete/ 'EmitData' of a Range and manage it within the 'emitSt'
genEDStByRange ::  GensymEmitterWithState sig m => QTy -> Int -> Range -> m EmitData
genEDStByRange qt i r = do
  ed <- genEDByRange qt i r
  emitSt %= (at (inj r) ?~ ed)
  return ed

genEDByRange :: (Has (Gensym Emitter) sig m) => QTy -> Int -> Range -> m EmitData
genEDByRange qt i r = do
  vB  <- gensym $ EmBaseSeq r qt
  (vmP, tyP) <- genPhaseTyByDegree i (inj r)
  let ed =  EmitData { evPhaseTy = vmP
                     , evPhaseSeqTy = tyP
                     , evBasis = Just vB
                     , evBasisTy = Just $ typingQEmit qt
                     , evAmp   = Nothing
                     }
  return ed


genEDStByRangeSansPhase ::  GensymEmitterWithState sig m => QTy -> Range -> m EmitData
genEDStByRangeSansPhase qt = genEDStByRange qt 0

genEDByRangeSansPhase
  :: (Has (Gensym Emitter) sig m)
  => QTy -> Range -> m EmitData
genEDByRangeSansPhase qt = genEDByRange qt 0


genEDStByRanges
  :: GensymEmitterWithState sig m
  => QTy -> [(Range, Int)] -> m [(Range, EmitData)]
genEDStByRanges qt ris =
  sequence [ (r,) <$> genEDStByRange qt i r | (r, i) <- ris ]

-- | Generate a /complete/ 'EmitData' of a Partition, managed 'emitSt'
--
genEDStByLoc
  :: GensymEmitterWithState sig m
  => Loc -> Int -> QTy -> [(Range, Int)] -> m (EmitData, [(Range, EmitData)])
genEDStByLoc l iLoc qt ris = do
  rAndEDs <- sequence [ (r,) <$> genEDStByRange qt i r | (r, i) <- ris ]
  (vMP, tyP) <- genPhaseTyByDegree iLoc (inj l)
  let edL = mtEmitData { evPhaseTy = vMP, evPhaseSeqTy = tyP }
  emitSt %= (at (inj l) ?~ edL)
  return ( edL , rAndEDs )


-- | Generate a /complete/ 'EmitData' of a Partition from its Locus
-- In particular, generate degree and phases based on its qt

genEDStFromLocus
  :: ( GensymEmitterWithState sig m
     , Has (Error String) sig m
     )
  => Loc -> [Range] -> QTy -> [Int] -> m (EmitData, [(Range, EmitData)])
genEDStFromLocus l rs qt is = do
  (il, ir) <- if isEN qt
    then (, repeat (-1)) <$> onlyOne throwError is
    else (-1, is)  <$ checkListCorr is rs
  genEDStByLoc l il qt $ zip rs ir

genEDStUpdatePhaseFromLocus
  :: ( GensymEmitterWithState sig m
     , Has (Error String) sig m
     )
  => Locus -> m [EmitData]
genEDStUpdatePhaseFromLocus Locus{loc, part=Partition{ranges=rs}, qty, degrees} = do
  is' <- if isEN qty
    then (: repeat (-1)) <$> onlyOne throwError degrees
    else (-1 : degrees)  <$ checkListCorr degrees rs
  zipWithM genEDStUpdatePhase degrees (inj loc : (inj <$> rs))


-- | Generate an 'EmitData' w/o Phase, managed by 'emitSt'
genEDStSansPhaseByLocAndRange
  :: GensymEmitterWithState sig m
  => Loc -> QTy -> [Range] -> m (EmitData, [(Range, EmitData)])
genEDStSansPhaseByLocAndRange l qt = genEDStByLoc l (-1) qt . ((, -1) <$>)

{-# INLINE genEDStByRangesSansPhase #-}
genEDStByRangesSansPhase
  :: GensymEmitterWithState sig m
  => QTy -> [Range] -> m [(Range, EmitData)]
genEDStByRangesSansPhase qt = genEDStByRanges qt . ((, -1) <$>)

-- | Same as `genEDStByRangesSansPhase` but without `Range` indices
genEDStByRangesSansPhase'
  :: GensymEmitterWithState sig m
  => QTy -> [Range] -> m [EmitData]
genEDStByRangesSansPhase' qt = ((snd <$>) <$>) . genEDStByRanges qt . ((, -1) <$>)



genEDStSansPhaseByRanges
  :: GensymEmitterWithState sig m
  => QTy -> [Range] -> m [(Range, EmitData)]
genEDStSansPhaseByRanges = genEDStByRangesSansPhase

-- | Append the given `EmitData` to the given entry.
appendEDSt
  :: StateMayFail sig m
  => RangeOrLoc -> EmitData -> m EmitData
appendEDSt rl ed = do
  emitSt %= Map.adjust (<> ed) rl
  findED rl

-- | Update an existing `EmitData` by generating a phase from the given degree.
genEDStUpdatePhase
  :: GensymEmitterWithStateError sig m
  => Int -> RangeOrLoc -> m EmitData
genEDStUpdatePhase i rl  = errTrace "`genEDStUpdatePhase`" $ do
  (evPhaseTy, evPhaseSeqTy)  <- genPhaseTyByDegree i rl
  appendEDSt rl (mtEmitData {evPhaseTy, evPhaseSeqTy})

-- ** Getters
findED :: StateMayFail sig m => RangeOrLoc -> m EmitData
findED rl = do
  ed <- use emitSt <&> (^. at rl)
  maybe (complain =<< use emitSt) return ed
  where
    complain st = throwError @String $
      printf "%s cannot be found in emitSt!\n%s" (show rl) (show st)

-- | Find the EmitData and visit it with an accessor
visitED :: Has (Error String) sig m => (EmitData -> Maybe a) -> EmitData -> m a
visitED evF ed = do
  maybe (complain ed) return (evF ed)
  where
    complain ed' = throwError @String $
      printf "Attempting to access non-Just field in %s" (show ed')

visitEDs
  :: Has (Error String) sig m
  => (EmitData -> Maybe a) -> [EmitData] -> m [a]
visitEDs f = mapM (visitED f)

findVisitED
  :: StateMayFail sig m
  => (EmitData -> Maybe c) -> RangeOrLoc -> m c
findVisitED evF = findED >=> visitED evF

findVisitEDs
  :: StateMayFail sig m
  => (EmitData -> Maybe c) -> [RangeOrLoc] -> m [c]
findVisitEDs f = errTrace "findVisitEDs" .
  mapM (findVisitED f)


-- *** Shorthands
visitEDBasis :: Has (Error String) sig m => EmitData -> m Var
visitEDBasis = visitED evBasis

visitEDsBasis :: Has (Error String) sig m => [EmitData] -> m [Var]
visitEDsBasis = mapM visitEDBasis

findVisitEDsBasis
  :: StateMayFail sig m
  => [RangeOrLoc] -> m [Var]
findVisitEDsBasis = findVisitEDs evBasis

findEmitBasisByRange
  :: StateMayFail sig m
  => Range -> m Var
findEmitBasisByRange = findVisitED evBasis . inj

findEmitBasesByRanges
  :: StateMayFail sig m
  => [Range] -> m [Var]
findEmitBasesByRanges = findVisitEDs evBasis . (inj <$>)


-- ** Destructor
deleteED :: (Has (State TState) sig m) => RangeOrLoc -> m ()
deleteED rl = emitSt %= sans rl

deleteEDs :: (Has (State TState) sig m) => [RangeOrLoc] -> m ()
deleteEDs s = emitSt %= (`Map.withoutKeys` Set.fromList s)

deleteEDPartition :: (Has (State TState) sig m) => Loc -> [Range] -> m ()
deleteEDPartition l rs =
  deleteEDs (inj l : (inj <$> rs))
