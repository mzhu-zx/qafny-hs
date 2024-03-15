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
    (forM)

import           Data.Functor
    ((<&>))
import           Data.List
    (nub)
import           Data.Maybe
    (maybeToList)

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
    (EmitData (evBasis, evPhaseTy), Emitter)
import           Qafny.Syntax.IR
import           Qafny.TypeUtils
import           Qafny.Typing
    (Promotion (..), PromotionScheme (..), queryPhaseType)
import           Qafny.Utils.EmitBinding
import           Qafny.Utils.Utils
    (onlyOne)
import           Text.Printf
    (printf)



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

codegenQft
  :: GensymEmitterWithStateError sig m
  => Locus -> m [Stmt']
codegenQft locus@Locus{loc, part=Partition{ranges}} = do
  vIdxK <- gensymBinding "k" TNat
  vIdxI <- gensymBinding "i" TNat
  vBasisReprs <- findEmitBasesByRanges ranges
  vBasisRepr <- case vBasisReprs of
    [x] -> return x
    _   -> throwError' "Qft only supports one range per locus."
    -- FIXME : Qft should support any number of ranges
  pty <- findVisitED evPhaseTy (inj loc)
  (vPrBase, vPrRepr) <- 
    case pty of
      PTN 1 PhaseRef{prBase, prRepr} -> return (prBase, prRepr)
      _ -> throwError' "It should have been promoted to 1."
  return $ codegenQftPure vPrRepr vBasisRepr vIdxK vIdxI (mkCard vBasisRepr)
  

-- | Given a 1st degree phase repr 'vPhase' and an EN typed base repr,
-- Generate statement to promote 1st degree phase to 2nd degree and perform
-- QFT operation.
--
-- The semantics is listed in [proposal/phase-amplitude].
codegenQftPure :: Var -> Var -> Var -> Var -> Exp' -> [Stmt']
codegenQftPure vPhase vBasis vIdxK vIdxI eSizeK =
  [ SEmit $ [vPhase, vBasis] :*:=: [eNewPhase, eNewBase] ]
  where
    -- vPhase -> seq<nat>(n, ... )
    -- vBasis -> seq<nat>(n, ... )
    -- eSizeK -> N

    -- | "seq<nat>(n, i => vPhase[i] + vBasis[i] * k)"
    eNewPhaseWithFreeK =
      natSeqLike vBasis (vPhase >:@: vIdxI + (vBasis >:@: vIdxK) >* vIdxK)
    -- | "seq<seq<nat>>(N, k => _sequence_with_free_k_)"
    eNewPhase = injAst $ EMakeSeq (TSeq TNat) eSizeK eNewPhaseWithFreeK
    -- | "seq<seq<nat>>(N, k => k)"
    eNewBase = injAst $ EMakeSeq TNat eSizeK (EVar vIdxI)

