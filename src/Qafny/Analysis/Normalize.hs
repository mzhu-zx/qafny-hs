{-# LANGUAGE
    DefaultSignatures
  #-}

module Qafny.Analysis.Normalize where

import           Data.List
    (sort)
import           Data.Sum
import           Qafny.Analysis.Partial
import           Qafny.Syntax.AST

class Normalizable a where
  normalize :: a -> a

instance Normalizable Range where
  normalize = reduce

instance Normalizable Partition where
  normalize Partition{ranges} = Partition . sort $ normalize <$> ranges

instance Normalizable (Range :+: Loc) where
  normalize (Inl r) = Inl (reduce r)
  normalize inr     = inr
