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
    genEDStUpdatePhase , genEDStByRanges
  , genEDStSansPhaseByRanges, genEDStByRangesSansPhase
    -- * Query
  , findED, visitED, visitEDs, findVisitED, findVisitEDs
  , visitEDBasis
    -- * Deletion
  , deleteED, deleteEDs, deleteEDPartition
    -- * Update
  , appendEDSt
  )
where

import           Control.Lens
    (at, sans, (?~), (^.))
import           Control.Monad
    (liftM2, (>=>))
import           Data.Functor
    ((<&>))
import qualified Data.Map.Strict          as Map
import qualified Data.Set                 as Set
import           Data.Sum
import           Text.Printf
    (printf)

import           Control.Effect.Error
    (Error, throwError)
import           Control.Effect.Lens
import           Control.Effect.Reader
import           Control.Effect.State
import           Effect.Gensym
    (Gensym, gensym)
import           Qafny.Env
    (RangeOrLoc, TState, emitSt)
import           Qafny.Syntax.AST
import           Qafny.Syntax.EmitBinding
import           Qafny.TypeUtils
    (emitTypeFromDegree, typingPhaseEmitReprN, typingQEmit)


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
  => Int -> RangeOrLoc -> m (Maybe PhaseRef, Maybe Ty)
genPhaseRefByDegree 0 _ = return (Nothing, Nothing)
genPhaseRefByDegree n r =
  (, emitTypeFromDegree n) . Just <$>
  liftM2 mkPhaseRef (gensym (EmPhaseSeq r n)) (gensym (EmPhaseSeq r n))

-- | Generate a /complete/ 'EmitData' of a Range and manage it within the 'emitSt'
genEDStByRange :: GensymWithState sig m => QTy -> Int -> Range -> m EmitData
genEDStByRange qt i r = do
  vB  <- gensym $ EmBaseSeq r qt
  (vmP, tyP) <- genPhaseRefByDegree i (inj r)
  let ed =  EmitData { evPhase = vmP
                     , evPhaseSeqTy = tyP
                     , evBasis = Just vB
                     , evBasisTy = Just $ typingQEmit qt
                     , evAmp   = Nothing
                     }
  emitSt %= (at (inj r) ?~ ed)
  return ed


genEDStByRanges
  :: GensymWithState sig m
  => QTy -> [(Range, Int)] -> m [(Range, EmitData)]
genEDStByRanges qt ris =
  sequence [ (r,) <$> genEDStByRange qt i r | (r, i) <- ris ]

-- | Generate a /complete/ 'EmitData' of a Partition, managed 'emitSt'
--
genEDStByLoc
  :: GensymWithState sig m
  => Loc -> Int -> QTy -> [(Range, Int)] -> m (EmitData, [(Range, EmitData)])
genEDStByLoc l iLoc qt ris = do
  rAndEDs <- sequence [ (r,) <$> genEDStByRange qt i r | (r, i) <- ris ]
  (vMP, tyP) <- genPhaseRefByDegree iLoc (inj l)
  let edL = mtEmitData { evPhase = vMP, evPhaseSeqTy = tyP }
  emitSt %= (at (inj l) ?~ edL)
  return ( edL , rAndEDs )


-- | Generate an 'EmitData' w/o Phase, managed by 'emitSt'
genEDStSansPhaseByLocAndRange
  :: GensymWithState sig m
  => Loc -> QTy -> [Range] -> m (EmitData, [(Range, EmitData)])
genEDStSansPhaseByLocAndRange l qt = genEDStByLoc l 0 qt . ((, 0) <$>)

{-# INLINE genEDStByRangesSansPhase #-}
genEDStByRangesSansPhase
  :: GensymWithState sig m
  => QTy -> [Range] -> m [(Range, EmitData)]
genEDStByRangesSansPhase = genEDStSansPhaseByRanges

genEDStSansPhaseByRanges
  :: GensymWithState sig m
  => QTy -> [Range] -> m [(Range, EmitData)]
genEDStSansPhaseByRanges qt = genEDStByRanges qt . ((, 0) <$>)

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
  => Int -> RangeOrLoc -> m EmitData
genEDStUpdatePhase i rl  = do
  (evPhase, evPhaseSeqTy)  <- genPhaseRefByDegree i rl
  appendEDSt rl (mtEmitData {evPhase, evPhaseSeqTy})

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
findVisitEDs f = mapM (findVisitED f)

-- *** Shorthands
visitEDBasis :: Has (Error String) sig m => EmitData -> m Var
visitEDBasis = visitED evBasis


-- ** Destructor
deleteED :: (Has (State TState) sig m) => RangeOrLoc -> m ()
deleteED rl = emitSt %= sans rl

deleteEDs :: (Has (State TState) sig m) => [RangeOrLoc] -> m ()
deleteEDs s = emitSt %= (`Map.withoutKeys` Set.fromList s)

deleteEDPartition :: (Has (State TState) sig m) => Loc -> [Range] -> m ()
deleteEDPartition l rs =
  deleteEDs (inj l : (inj <$> rs))
