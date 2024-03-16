{-# LANGUAGE
    CPP
  , DataKinds
  , FlexibleContexts
  , FlexibleInstances
  , IncoherentInstances
  , MultiWayIf
  , RecordWildCards
  , ScopedTypeVariables
  , TupleSections
  , TypeApplications
  , TypeFamilies
  , UndecidableInstances
  #-}

module Qafny.Codegen.Phase where

import           Control.Monad
    (forM, liftM2, when)

import           Data.Functor
    ((<&>))
import           Data.List
    (nub, uncons)
import           Data.Maybe
    (fromMaybe, maybeToList, fromJust)

import           Data.Sum
    (Injection (inj))

import           Qafny.Effect
import           Qafny.Syntax.AST
import           Qafny.Syntax.ASTFactory
import           Qafny.Syntax.ASTUtils
    (getPhaseRefN)
import           Qafny.Syntax.Emit
    (showEmit0)
import           Qafny.Syntax.EmitBinding
import           Qafny.Syntax.IR
import           Qafny.TypeUtils
import           Qafny.Typing
    (Promotion (..), PromotionScheme (..), castScheme, queryPhaseType,
    resolvePartition')
import           Qafny.Typing.Qft
    (typingQft)
import           Qafny.Utils.EmitBinding
import           Qafny.Utils.Utils
    (onlyOne)
import           Text.Printf
    (printf)
import Qafny.Syntax.EmitBinding (EmitData(evPhaseSeqTy))



-- | Phase-Related Code Generation


throwError'
  :: ( Has (Error String) sig m )
  => String -> m a
throwError' = throwError @String . ("[Codegen] " ++)

-- * Generating Phase Promotion

codegenPromotionMaybe
  :: ( Has (Gensym Emitter) sig m
     , Has (State TState) sig m
     , Has (Error String) sig m
     )
  => Maybe PromotionScheme -> m [Stmt']
codegenPromotionMaybe = (concat <$>) . mapM codegenPromotion . maybeToList

-- | Generate code for a given PromotionScheme
-- This function doesn't mutate the Emitter state.
codegenPromotion
  :: ( Has (Gensym Emitter) sig m
     , Has (State TState) sig m
     , Has (Error String) sig m
     )
  => PromotionScheme -> m [Stmt']
codegenPromotion
  PromotionScheme { psPrefs=prefs
                  , psPromotion=promotion
                  } =
  case promotion of
    Promote'0'1 (i, n) rs qt ->
      codegenPromote'0'1 qt rs prefs (i, n)

-- | Promote a 0th-degree phase to 1st-degree phase
-- This function doesn't mutate the Emitter state.
codegenPromote'0'1
  :: ( Has (Gensym Emitter) sig m
     , Has (State TState) sig m
     , Has (Error String) sig m
     )
  => QTy -> [Range] -> [PhaseRef] -> (Exp', Exp') -> m [Stmt']
codegenPromote'0'1 qt rs prefs (i, n) = do
  vRs <- findVisitEDs evBasis (inj <$> rs)
  let eCardVRs = mkCard <$> vRs
      -- use 0 here because `EMakeSeq` add an extra layer of `seq`
      ty = typingPhaseEmitReprN 0
  return . concat $
    [ [ vRepr ::=: (EEmit . EMakeSeq ty eCard . constLambda $ i)
      , vBase ::=: n
      ]
    | (pref, eCard) <- zip prefs eCardVRs
    , let vRepr = prRepr pref
          vBase = prBase pref
    ]

--------------------------------------------------------------------------------
-- * Generating PhaseLambda
--------------------------------------------------------------------------------
codegenPhaseLambda
  :: ( Has (State TState) sig m
     , Has (Error String) sig m
     )
  => Locus -> PhaseBinder -> PhaseExp -> m [Stmt']
codegenPhaseLambda st pb pe = do
  (dgrs, prefs) <- queryPhaseType st <&> unzip . getPhaseRefN
  dgrSt <- onlyOne throwError' $ nub dgrs
  concat <$> forM prefs (go dgrSt pb pe)
  where
    go 1 (PhaseOmega bi bBase) (PhaseOmega ei eBase)
      PhaseRef { prRepr=vRepr, prBase=vBase} =
      let substBase = subst [(bBase, EVar vBase)] in
        return [ vRepr ::=: callMap (simpleLambda bi (substBase ei)) vRepr
               , vBase ::=: subst [(bBase, EVar vBase)] eBase
               ]
    go dgr _ _ _ = throwError' $
      printf "At least one of the binder %s and the specficiation %s is not of degree %d."
      (showEmit0 pb) (showEmit0 pe) dgr



-- * Quantum Fourier Transformation
codegenApplyQft
  :: ( GensymEmitterWithStateError sig m
     , HasResolution sig m
     )
  => Partition -> m [Stmt']
codegenApplyQft s = do
  (locus, rsMap) <- resolvePartition' s
  case rsMap of
    [(r1, r2)] -> if r1 == r2 then go locus r1
                  else throwError' (errIncompleteRange r1 r2)
    _          ->
      throwError' "Qft may only be applied to exactly one range."
  where
    go locusS r = do
      -- ensures that bases is `EN`
      (locusS, stmtCast) <- castScheme locusS TEn
      -- ensures that phases is in 1st degree
      when (degrees locusS /= [1]) $
        throwError' "Degree not 1"
      newLocus <- typingQft r locusS
      codegenQft locusS newLocus
    errIncompleteRange r1 r2 = printf
      "The range %s is a proper subrange of %s." (showEmit0 r1) (showEmit0 r2)


-- | Generate statements for Qft and update Emit states given the original locus
-- and the expected locus promoted by Qft.
--
codegenQft
  :: GensymEmitterWithStateError sig m
  => Locus -> Locus -> m [Stmt']
codegenQft locusEn locusQft = do
  edLocus <- findED iloc      -- for amp+phase purpose
  (edRApplied, edRsRest) <-   -- for kets purpose
    ensuresNonEmptyEDs <$> findEDs (inj <$> ranges)
  (vIdxK, vIdxI) <-            -- indices
    liftM2 (,) (gensymBinding "k" TNat) (gensymBinding "i" TNat)

  vKetApplied <- visitEDBasis edRApplied
  vsKetRest   <- visitEDsBasis edRsRest

  (pRefMaybe, pReprTyMaybe) <- genPhaseTyByDegree qftDegree iloc
  
  pty <- findVisitED evPhaseTy (inj loc)
  (vPrBase, vPrRepr) <-
    case pty of
      PTN 1 PhaseRef{prBase, prRepr} -> return (prBase, prRepr)
      _ -> throwError' "It should have been promoted to 1."

  

  let edLocus' = edLocus { evPhaseTy=ptyMaybe, evPhaseSeqTy=pReprTyMaybe }

  let PhaseRef{prBase=vprBase, prRepr=vPhaseFresh} = fromJust ptyMaybe
      
  return $ codegenQftPure
    (vPhase1, vPhaseFresh) vKetApplied
    (vsKetRest, vsKetFresh) vIdxK vIdxI nQft
  where
    Locus {loc, part=Partition{ranges}, degrees=qftDegrees} = locusQft
    iloc = inj loc              -- inject to RangeOrLoc
    qftDegree = head qftDegrees -- safe to ignore the rest
    nQft =                      -- compute Qft 
      let Range _ rl rr = head ranges
      in mkPow2(rr - rl)      
    ensuresNonEmptyEDs eds = fromMaybe (error "unreachable") $ uncons eds


-- | Given a 1st degree phase repr 'vPhase' and an En typed base repr,
-- Mutate the phase representation of the En base and generate a new sequence of
-- basis kets for the tailing range.
--
-- See Proposal [hoet] for transformation.
codegenQftPure
  :: (Var, Var)     -- old (1st-degree) and new (2nd-degree) phase variables
  -> Var            -- ket variable for the applied range is re-used
  -> ([Var], [Var]) -- old and new rest variables (En -> Qft)
  -> Var            -- bind for the Qft ket "k"
  -> Var            -- bind for the inner En index "i"
  -> Exp'           -- Size of Qft
  -> [Stmt']
codegenQftPure (vPhase1, vPhaseFresh) vbApplied (vsbRest, vsbRestFresh)
  vIdxK vIdxI eSizeK =
  [ SEmit $ lhs :*:=: rhs ]
  where
    lhs = [vPhaseFresh, vbApplied] ++ vsbRestFresh
    rhs = [eNewPhase  , eNewBase ] ++ ebRestLiftByK
    -- vPhase -> seq<nat>(n, ... )
    -- vBasis -> seq<nat>(n, ... )
    -- eSizeK -> N

    -- | "seq<nat>(n, i => vPhase[i] + vBasis[i] * k)"
    eNewPhaseWithFreeK =
      natSeqLike vbApplied (vPhase1 >:@: vIdxI + (vbApplied >:@: vIdxK) >* vIdxK)
    -- | "seq<seq<nat>>(N, k => _sequence_with_free_k_)"
    eNewPhase = injAst $ EMakeSeq tySn eSizeK eNewPhaseWithFreeK
    -- | "seq<nat>(N, k => k)"
    eNewBase = injAst $ EMakeSeq TNat eSizeK (EVar vIdxI)
    -- | lift the superp of kets to the superp of kets _indexed by_ `k`
    ebRestLiftByK = mkSeqConst tySn eSizeK <$> vsbRest
