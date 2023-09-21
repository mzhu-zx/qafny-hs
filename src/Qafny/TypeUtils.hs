{-# LANGUAGE TupleSections #-}
module Qafny.TypeUtils where

import           Qafny.Syntax.AST (QTy (..), Ty (..), PhaseTy (..))

-- | Type of the emitted value corresponding to its original quantum type.
typingQEmit :: QTy -> Ty
typingQEmit TNor  = TSeq TNat
typingQEmit THad  = TSeq TNat
typingQEmit TEN   = TSeq TNat
typingQEmit TEN01 = TSeq (TSeq TNat)
{-# INLINE typingQEmit #-}

-- | Type of an emitted phase variable
typingPhaseEmit :: PhaseTy -> Maybe (Ty, Ty)
typingPhaseEmit PT0       = Nothing -- default phase is evident
typingPhaseEmit (PTN n _) = Just . typingPhaseEmitN $ n



-- | Return the Base Type and the Repr Type for a collection of phases based on
-- the given degree of phases
typingPhaseEmitN :: Int -> (Ty, Ty)
typingPhaseEmitN n = 
  (TNat,) $ foldr ($) TNat (replicate n TSeq)

-- | Check if the given type is an 'EN'-like type.
isEN :: QTy -> Bool
isEN TEN01 = True
isEN TEN   = True
isEN _     = False
