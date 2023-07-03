module Qafny.TypeUtils where

import           Qafny.AST (QTy (..), Ty (..))

-- | Type of the emitted value corresponding to its original quantum type.
typingQEmit :: QTy -> Ty
typingQEmit TNor  = TSeq TNat
typingQEmit THad  = TSeq TNat
typingQEmit TEN   = TSeq TNat
typingQEmit TEN01 = TSeq (TSeq TNat)
{-# INLINE typingQEmit #-}

