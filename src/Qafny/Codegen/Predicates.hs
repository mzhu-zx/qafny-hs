--------------------------------------------------------------------------------
-- |
-- Code generation of qunatum state predicates and specifications.
--------------------------------------------------------------------------------

{-# LANGUAGE
    MultiWayIf
  , TypeFamilies
  , LambdaCase
  #-}

module Qafny.Codegen.Predicates(
  codegenAssertion, codegenRequires, codegenEnsures
  ) where

-- Effects
import           Data.Functor
    ((<&>))
import           Data.Maybe
    (catMaybes)
import           Text.Printf
    (printf)

-- Qafny
import           Qafny.Effect
import           Qafny.Partial
    (Reducible (reduce))
import           Qafny.Syntax.AST
import           Qafny.Syntax.ASTFactory
import           Qafny.Syntax.IR
import           Qafny.Typing.Utils
    (isEn)
import           Qafny.Typing
    (analyzePhaseSpecDegree, extendMetaState, queryPhaseRef, resolvePartition,
    typingPartitionQTy)

import           Control.Carrier.Reader
    (runReader)
import           Control.Monad
    (MonadPlus (mzero), forM, when)
import           Data.Bifunctor
import           Qafny.Codegen.Utils
    (putOpt, runWithCallStack)
import           Qafny.Utils.EmitBinding
import           Qafny.Utils.Utils
    (haveSameLength, onlyOne)
import Data.List (sort)
import Qafny.Syntax.EmitBinding (EmitData)


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
  codegenSpecExp locusEd rangesEd espec
codegenAssertion' e = return [e]
  -- FIXME: what to do if [e] contains an assertion?



-- | Take in the emit variable corresponding to each range in the partition and the
-- partition type; with which, generate expressions (predicates)
codegenSpecExp
  :: ( Has (Error String) sig m, Has (Reader Bool) sig m )
  => EmitData -> [(Range, EmitData)] -> QTy -> [SpecExp] -> m [Exp']
codegenSpecExp locusEd rangesEd = go
  where
    go TNor specs = do
      (range, ed) <- onlyOne throwError' rangesEd
      vKet <- fst <$> visitEmBasis ed
      let size = Intv 0 (rangeSize range)
      mapM (codegenSpecExpNor vKet size . seNor)  specs

    errVariableNotFound = printf "%s variable for %s is not found."


  -- if isEn p
  -- then do
  --   when (length specs /= 1) $ throwError' $ printf "More then one specs!"
  --   pspec <- onlyOne throwError' (phase <$> specs)
  --   specPerPartition p (spec (head specs)) pspec
  -- else do
  --     -- For `nor` and `had`, one specification is given one per range
  --   haveSameLength vrs specs
  --   concat <$> mapM (specPerRange' p) (zip3 (first fst <$> vrs) specs ptys)
  -- where
  --   specPerRange' ty (vr, qspec, pty) =
  --     specPerRange ty (vr, (spec qspec, phase qspec), pty)
  --   specPerRange ty ((v, Range _ el er), (SESpecNor idx eBody, pspec), pty) |
  --     ty `elem` [TNor, THad] =
  --     -- In x[l .. r]
  --     -- @
  --     --   forall idx | 0 <= idx < (r - l) :: xEmit[idx] == eBody
  --     -- @
  --     let eSelect x = x >:@: idx
  --         eBound = Just (eIntv idx (ENum 0) (reduce (er - el)))
  --         quantifier = EForall (natB idx) eBound . ($ idx)
  --         eSize = reduce (er - el)
  --     in do
  --       ePSpec <- codegenPhaseSpec quantifier eSize pty pspec
  --       return $
  --        [ eSize `eEq` ECard (EVar v)
  --        , quantifier (const (eSelect v `eEq` eBody))
  --        ] ++ ePSpec
  --   -- specPerRange THad ((v, Range _ el er), (SESpecNor idx eBody, pspec), pty) =
  --   --   -- In x[l .. r]
  --   --   -- @
  --   --   --   forall idx | 0 <= idx < (r - l) :: xEmit[idx] == eBody
  --   --   -- @
  --   --   let eSelect x = EEmit (ESelect (EVar x) (EVar idx))
  --   --       eBound = Just (eIntv idx (ENum 0) (reduce (er - el)))
  --   --       quantifier = EForall (natB idx) eBound . ($ idx)
  --   --   in do
  --   --     ePSpec <- codegenPhaseSpec quantifier pty pspec
  --   --     return $
  --   --      [ reduce (er - el) `eEq` EEmit (ECard (EVar v))
  --   --      , quantifier (const (eSelect v `eEq` eBody))
  --   --      ] ++ ePSpec
  --   specPerRange _ (_, (SEWildcard, pspec), pty) =
  --     return []
  --   specPerRange _ e  =
  --     errIncompatibleSpec e

  --   specPerPartition TEn (SESpecEn (SpecEn01F idx (Intv l r) eValues)) pspec = do
  --     haveSameLength vrs eValues
  --     -- In x[? .. ?] where l and r bound the indicies of basis-kets
  --     -- @
  --     --   forall idx | l <= idx < r :: xEmit[idx] == eBody
  --     -- @
  --     let eBound = Just $ eIntv idx l r
  --         eSize = reduce (r - l)
  --         eSelect x = x >:@: idx
  --         quantifier = EForall (natB idx) eBound . ($ idx)
  --     pty <- onlyOne throwError' ptys
  --     ePSpec <- codegenPhaseSpec quantifier eSize pty pspec
  --     return $ ePSpec ++ concat
  --       [ [ eSize `eEq` ECard (EVar vE)
  --         , quantifier (const (EOp2 OEq (eSelect vE) eV)) ]
  --       | (((vE, _), _), eV) <- zip vrs eValues
  --       , eV /= EWildcard ]

  --   specPerPartition
  --     TEn01
  --     (SESpecEn01 idxSum (Intv lSum rSum) idxTen (Intv lTen rTen) eValues)
  --     pspec
  --      = do
  --     -- In x[l .. r]
  --     -- @
  --     --   forall idxS | lS <= idxS < rS ::
  --     --   forall idxT | 0 <= idxT < rT - lT ::
  --     --   xEmit[idxS][idxT] == eBody
  --     -- @
  --     -- todo: also emit bounds!
  --     haveSameLength vrs eValues
  --     pty <- onlyOne throwError' ptys
  --     let eBoundSum = Just $ eIntv idxSum lSum rSum
  --         eSizeSum = reduce (rSum - lSum)
  --         eForallSum = EForall (natB idxSum) eBoundSum . ($ idxSum)
  --     ePSpec <- codegenPhaseSpec eForallSum eSizeSum pty pspec
  --     return . (ePSpec ++) . concat $ do
  --       (((vE, _), Range _ el er), eV) <- bimap (second reduce) reduce<$> zip vrs eValues
  --       when (eV == EWildcard) mzero
  --       let cardSum = eSizeSum `eEq` ECard (EVar vE)
  --       let rTen' = reduce (er - el)
  --       let eBoundTen = Just $ eIntv idxTen 0 rTen'
  --       let cardTen = rTen' `eEq` ECard (vE >:@: idxSum)
  --       let eForallTen = EForall (natB idxTen) eBoundTen
  --       let eSel = vE >:@: idxSum >:@: idxTen
  --       let eBodys = [ cardTen
  --                    , EOp2 OEq eSel eV
  --                    ]
  --       return $  cardSum : (eForallSum . const . eForallTen <$> eBodys)
  --   specPerPartition _ e _ = throwError' $
  --     printf "%s is not compatible with the specification %s"
  --        (show p) (show e)

  --   errIncompatibleSpec e = throwError' $
  --     printf "%s is not compatible with the specification %s"
  --     (show p) (show e)

codegenSpecExpNor :: Var -> Intv -> SpecNor -> [Exp']
codegenSpecExpNor vKet bound SpecNorF{norVar, norKet} =
  EForall (natB norVar) bound equality
  where
    equality = (vKet >:@: norVar) `eEq` norKet

-- | Generate a predicates over phases based on the phase type
--
-- FIXME: Here's a subtlety: each range maps to one phase type which in the
-- current specification language is not supported?
codegenPhaseSpec
  :: ( Has (Error String) sig m
     )
  => ((Var -> Exp') -> Exp') -> Exp' -> Maybe (PhaseRef, Ty) ->  PhaseExp -> m [Exp']
codegenPhaseSpec _ _ Nothing pe
  | pe `elem` [ PhaseZ, PhaseWildCard ] =
      return [] 
  | otherwise =
      throwError' $ printf "%s is not a zeroth degree predicate." (show pe)
codegenPhaseSpec quantifier eSize (Just (ref, _)) (PhaseOmega eK eN) =
  let assertN = EOp2 OEq eN (EVar (prBase ref))
      assertK idx = EOp2 OEq eK (prRepr ref >:@: idx)
      assertKCard = EOp2 OEq eSize (mkCard (prRepr ref))
  in return [assertN, assertKCard, quantifier assertK ]

codegenPhaseSpec quantifier eSize (Just (ref, _)) (PhaseSumOmega (Range v l r) eK eN) =
  let assertN = EOp2 OEq eN (EVar (prBase ref))
      pLength = r - l
      -- FIXME: emit the length of the 2nd-degree range and get the inner
      -- quantifier right
      assertK idx = EForall (Binding v TNat) Nothing 
                    (eK `eEq` (prRepr ref >:@: v >:@: idx))
  in return [assertN, quantifier assertK]
codegenPhaseSpec _ _ _ e =
  throwError' $ printf "Invalid %s phase." (show e)

-- | Generate predicates for require clauses
--
-- This introduces constraints and knowledges into the current context.
codegenRequires
  :: ( GensymEmitterWithStateError sig m
     , GensymMeta sig m
     , Has Trace sig m
     )
  => [Exp'] -> m ([Exp'], [(PhaseRef, Ty)])
codegenRequires rqs = do
  trace "* codegenRequires"
  (bimap concat concat . unzip <$>) . forM rqs $ \rq ->
  -- TODO: I need to check if partitions from different `requires` clauses are
  -- indeed disjoint!
    case rq of
      ESpec s qt espec -> do
        let pspec = phase <$> espec
        let dgrs = pspec <&> analyzePhaseSpecDegree
        (vsEmit, ptys) <- extendMetaState s qt dgrs
        es <- runReader True $
          codegenSpecExp (zip vsEmit (unpackPart s)) qt espec ptys
        return (es, catMaybes ptys)
      _ -> return ([rq], [])

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


