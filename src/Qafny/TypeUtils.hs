module Qafny.TypeUtils where

import           Qafny.AST (QTy (..), Ty (..))

-- | Type of the emitted value corresponding to its original quantum type.
typingQEmit :: QTy -> Ty
typingQEmit TNor  = TSeq TNat
typingQEmit THad  = TSeq TNat
typingQEmit TCH   = TSeq TNat
typingQEmit TCH01 = TSeq (TSeq TNat)
{-# INLINE typingQEmit #-}

