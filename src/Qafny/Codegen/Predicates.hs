--------------------------------------------------------------------------------
-- |
-- Code generation of quantum state predicates and specifications.
--------------------------------------------------------------------------------

{-# LANGUAGE
    LambdaCase
  , MultiWayIf
  , TypeFamilies
  #-}

module Qafny.Codegen.Predicates(
  codegenAssertion, codegenRequires, codegenEnsures
  ) where


import           Prelude                  hiding
    (pred)

-- Effects
import           Data.Maybe
import           Text.Printf
    (printf)

-- Qafny
import           Qafny.Effect
import           Qafny.Syntax.AST
import           Qafny.Syntax.ASTFactory
import           Qafny.Syntax.IR
import           Qafny.Typing.Typing
    (extendState, resolvePartition, typingPartitionQTy)

import           Control.Arrow
    (Arrow (second))
import           Control.Carrier.Reader
    (runReader)
import           Control.Monad
    (forM, when)
import           Data.Foldable
    (Foldable (toList), foldrM)
import           Data.Functor
    ((<&>))
import           Data.List
    (sort)
import           Qafny.Codegen.Utils
    (runWithCallStack)
import           Qafny.Syntax.EmitBinding
import           Qafny.Typing.Predicates
    (wfSignatureFromPredicate')
import           Qafny.Utils.EmitBinding
import           Qafny.Utils.Utils
    (onlyOne)


throwError'
  :: ( Has (Error String) sig m )
  => String -> m a
throwError' = throwError @String . ("[Codegen/Predicates] " ++)


-- | Take in an /assertional/ expression, perform type check and emit
-- corresponding expressions
codegenAssertion
  :: ( HasResolution sig m
     , GenConditionally sig m
     )
  => Exp' -> m [Exp']
codegenAssertion e = runWithCallStack e (codegenAssertion' e)

codegenAssertion'
  :: ( HasResolution sig m
     , GenConditionally sig m
     )
  => Exp' -> m [Exp']
codegenAssertion' (ESpec s qt espec) = do
  st@Locus{part, degrees=dgrs} <- typingPartitionQTy s qt
  -- FIXME: do something seriously when (part /= s)
  when (sort (ranges part) /= sort (ranges s)) $
    throwError' (printf "Assertion: %s is inconsistent with %s." (show part) (show s))
  (locusEd, rangesEd) <- findEmsByLocus st
  codegenSpecExp locusEd rangesEd qt espec
codegenAssertion' e = return [e]
  -- FIXME: what to do if [e] contains an assertion?



-- | Take in the emit variable corresponding to each range in the partition and the
-- partition type; with which, generate expressions (predicates)
codegenSpecExp
  :: forall sig m . ( Has (Error String) sig m, Has (Reader Bool) sig m )
  => EmitData -> [(Range, EmitData)] -> QTy -> [SpecExp] -> m [Exp']
codegenSpecExp locusEd rangesEd = go
  where
    go :: QTy -> [SpecExp] -> m [Exp']
    go TNor specs = do
      (range, ed) <- onlyOne throwError' rangesEd
      vKet <- fst <$> visitEmBasis ed
      return $ codegenSpecExpNor vKet (predFromRange range) . seNor <$> specs
    go THad specs = do
      (range, _) <- onlyOne throwError' rangesEd
      return $ case evPhaseRef locusEd of
        Nothing -> []
        Just (ref, _) ->
          concatMap (codegenSpecExpHad ref (predFromRange range) . seHad) specs
    go TEn specs = do
      (vAmp, _) <- visitEm evAmp locusEd
      let refMaybe = fst <$> evPhaseRef locusEd
          rvKets = second ((fst <$>) . evBasis) <$> rangesEd
      return $ concatMap (codegenSpecExpEn vAmp refMaybe rvKets . seEn) specs
    go TEn01 specs = do
      (vAmp, _) <- visitEm evAmp locusEd
      let refMaybe = fst <$> evPhaseRef locusEd
          rvKets = second ((fst <$>) . evBasis) <$> rangesEd
      return $ concatMap (codegenSpecExpEn01 vAmp refMaybe rvKets . seEn01) specs
  
    predFromRange r =
      let bound = Intv 0 (rangeSize r)
      in predFromIntv  bound

codegenSpecExpNor :: Var -> (Var -> Exp') -> SpecNor -> Exp'
codegenSpecExpNor vKet pred SpecNorF{norVar, norKet} =
  mkForallEq norVar pred vKet norKet

codegenSpecExpHad :: PhaseRef -> (Var -> Exp') -> SpecHad -> [Exp']
codegenSpecExpHad pr pred SpecHadF{hadVar, hadPhase} =
  codegenPhaseSpec pr hadVar pred hadPhase

codegenSpecExpEn
  :: Var -> Maybe PhaseRef -> [(Range, Maybe Var)] -> SpecEn -> [Exp']
codegenSpecExpEn vAmp prMaybe rvKets
  SpecEnF{enVarSup, enIntvSup, enAmpCoef, enPhaseCoef, enKets} =
  ampPred ++ phasePreds ++ ketPreds
  where
    predIntv = predFromIntv enIntvSup

    ampPred = [ vAmp `eEq` codegenAmpExp enAmpCoef]
    phasePreds = concat $ prMaybe <&> \pr ->
      codegenPhaseSpec pr enVarSup predIntv enPhaseCoef
    ketPreds = -- TODO: generate mod using Range
      zipWith perKetExp rvKets enKets

    perKetExp (_, v) EWildcard = EBool True
    perKetExp (_, Nothing) _   = EBool False -- EMMMMM, I should warn instead
    perKetExp (_, Just v) eKet = mkForallEq enVarSup predIntv v eKet

codegenSpecExpEn01
  :: Var -> Maybe PhaseRef -> [(Range, Maybe Var)] -> SpecEn01 -> [Exp']
codegenSpecExpEn01 vAmp prMaybe rvKets
  SpecEn01F{en01VarSup, en01IntvSup, en01AmpCoef, en01PhaseCoef
           ,en01VarQbit, en01Kets, en01IntvQbit} =
  ampPred ++ phasePreds ++ ketPreds
  where
    predIntv = predFromIntv en01IntvSup
    predIntvQ = predFromIntv en01IntvQbit

    ampPred = [ vAmp `eEq` codegenAmpExp en01AmpCoef]
    phasePreds = concat $ prMaybe <&> \pr ->
      codegenPhaseSpec pr en01VarSup predIntv en01PhaseCoef
    ketPreds = -- TODO: generate mod using Range
      zipWith perKetExp rvKets en01Kets

    perKetExp (_, v) EWildcard = EBool True
    perKetExp (_, Nothing) _   = EBool False -- EMMMMM, I should warn instead
    perKetExp (_, Just v) eKet =
      mkForallEq2 en01VarSup predIntv en01VarQbit predIntvQ v eKet



codegenAmpExp :: AmpExp -> Exp'
codegenAmpExp = undefined

-- | Generate a predicates over phases based on the phase type
codegenPhaseSpec :: PhaseRef -> Var -> (Var -> Exp') -> PhaseExp -> [Exp']
codegenPhaseSpec PhaseRef{prRepr, prBase} vIdx predIdx = go
  where
  go PhaseWildCard = [EBool True]
  go PhaseZ = [EBool True]
  go (PhaseOmega e n) =
    [ prBase `eEq` n
    , mkForallEq vIdx predIdx prRepr e ]
  go (PhaseSumOmega (Range x l r) e n) =
    [ prBase `eEq` n
    , mkForallEq2 vIdx predIdx x pred' prRepr e ]
    where
      pred' = predFromIntv (Intv l r)

-- | Generate predicates for require clauses.
--
-- This introduces constraints and knowledges into the current context.
codegenRequires
  :: forall m sig .
     ( GensymEmitterWithStateError sig m
     , GensymMeta sig m
     , Has Trace sig m
     )
  => [Exp'] -> m ([Exp'], [EmitData])
codegenRequires rqs = do
  trace "* codegenRequires"
  sigs <- catMaybes <$> forM rqs wfSignatureFromPredicate'
  foldrM go ([], []) sigs
  where
    go :: (Partition, QTy, Maybe Int, [SpecExp]) -> ([Exp'], [EmitData])
       -> m ([Exp'], [EmitData])
    go (p, qt, ds, specs) (retEs, retEds)= do
      eds <- extendState p qt (toList ds)
      es <- runReader True $ uncurry codegenSpecExp eds qt specs
      return (es ++ retEs, eraseRanges eds ++ retEds)

codegenEnsures
  :: ( Has (State TState)  sig m
     , Has (Error String) sig m
     , Has Trace sig m
     )
  => [Exp'] -> m [Exp']
codegenEnsures ens =
  concat <$> forM ens (runReader initIEnv . runReader True  . codegenAssertion)

-- | Find the representation of the given range
codegenRangeRepr
  :: ( Has (State TState) sig m
     , Has (Error String) sig m
     , Has (Reader IEnv) sig m
     , Has Trace sig m
     )
  => Range -> m (Var, Ty)
codegenRangeRepr r =
  resolvePartition (Partition [r]) >> findEmitBasisByRange r
