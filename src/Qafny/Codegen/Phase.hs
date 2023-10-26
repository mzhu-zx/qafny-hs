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

import           Control.Effect.Error
import           Control.Effect.State
import           Control.Monad            (forM)
import           Effect.Gensym

import           Data.Functor             ((<&>))
import           Data.List                (nub)
import           Data.Maybe               (maybeToList)

import           Qafny.Env
import           Qafny.Syntax.AST
import           Qafny.Syntax.ASTFactory
    ( callMap
    , cardV
    , constLambda
    , simpleLambda
    )
import           Qafny.Syntax.ASTUtils    (getPhaseRefN)
import           Qafny.Syntax.Emit        (showEmit0)
import           Qafny.Syntax.EmitBinding
import           Qafny.TypeUtils
import           Qafny.Typing
    ( Promotion (..)
    , PromotionScheme (..)
    , queryPhaseType
    )
import           Qafny.Utils              (findEmitRangeQTy, onlyOne)
import           Text.Printf              (printf)


-- | Phase-Related Code Generation


throwError'
  :: ( Has (Error String) sig m )
  => String -> m a
throwError' = throwError @String . ("[Codegen] " ++)


first3 :: (a -> d) -> (a, b, c) -> (d, b, c)
first3 f (a, b, c) = (f a, b, c)

--------------------------------------------------------------------------------
-- * Generating Phase Promotion
--------------------------------------------------------------------------------

codegenPromotionMaybe
  :: ( Has (Gensym EmitBinding) sig m
     , Has (State TState) sig m
     , Has (Error String) sig m
     )
  => Maybe PromotionScheme -> m [Stmt']
codegenPromotionMaybe = (concat <$>) . mapM codegenPromotion . maybeToList

codegenPromotion
  :: ( Has (Gensym EmitBinding) sig m
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
codegenPromote'0'1
  :: ( Has (Gensym EmitBinding) sig m
     , Has (State TState) sig m
     , Has (Error String) sig m
     )
  => QTy -> [Range] -> [PhaseRef] -> (Exp', Exp') -> m [Stmt']
codegenPromote'0'1 qt rs prefs (i, n) = do
  vRs <- forM rs (`findEmitRangeQTy` qt)
  let eCardVRs = cardV <$> vRs
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
  => STuple -> PhaseBinder -> PhaseExp -> m [Stmt']
codegenPhaseLambda st pb pe = do
  (dgrs, prefs) <- queryPhaseType st <&> unzip . getPhaseRefN
  dgrSt <- onlyOne throwError' $ nub dgrs
  concat <$> forM prefs (go dgrSt pb pe)
  where
    go 1 (PhaseOmega bi bBase) (PhaseOmega ei eBase)
      PhaseRef { prRepr=vRepr, prBase=vBase} =
      let substBase = subst [(bBase, EVar vBase)] in
        return [ vRepr ::=: callMap (simpleLambda bi (substBase ei)) (EVar vRepr)
               , vBase ::=: subst [(bBase, EVar vBase)] eBase
               ]
    go dgr _ _ _ = throwError' $
      printf "At least one of the binder %s and the specficiation %s is not of degree %d."
      (showEmit0 pb) (showEmit0 pe) dgr
