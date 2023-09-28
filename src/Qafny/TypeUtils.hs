{-# LANGUAGE
    TupleSections
  #-}
module Qafny.TypeUtils where

-- | Pure utility functions related to types

import           Control.Lens       (over)
import           Control.Lens.Tuple
import           Qafny.Env          (STuple (..))
import           Qafny.Syntax.AST   (PhaseTy (..), QTy (..), Ty (..))



-- | Type of the emitted value corresponding to its original quantum type.
typingQEmit :: QTy -> Ty
typingQEmit TNor  = TSeq TNat
typingQEmit THad  = TSeq TNat
typingQEmit TEN   = TSeq TNat
typingQEmit TEN01 = TSeq (TSeq TNat)
{-# INLINE typingQEmit #-}

-- | Type of an emitted phase variable
-- typingPhaseEmit :: PhaseTy -> Maybe (Ty, Ty)
-- typingPhaseEmit PT0       = Nothing -- default phase is evident
-- typingPhaseEmit (PTN n _) = Just . (TNat,) . typingPhaseEmitReprN $ n


-- | Return the Repr Type for a collection of phases based on
-- the given degree of phases
typingPhaseEmitReprN :: Int -> Ty
typingPhaseEmitReprN n =
  foldr ($) TNat (replicate n TSeq)

-- | Check if the given type is an 'EN'-like type.
isEN :: QTy -> Bool
isEN TEN01 = True
isEN TEN   = True
isEN _     = False


-- | STuple
modifyPty :: ([Int] -> [Int]) -> STuple -> STuple
modifyPty f (STuple st) = STuple $ over (_3. _2) f st
