{-# LANGUAGE
    FlexibleInstances
  , MultiParamTypeClasses
  , TypeOperators
  #-}

module Data.Sum where

data (f :+: g)
  = Inl f
  | Inr g

instance (Show f, Show g) => Show (f :+: g) where
  show (Inl f) = show f
  show (Inr g) = show g

class Injection f g where
  inj :: f -> g

instance Injection f (f :+: g) where
  inj = Inl

instance Injection g (f :+: g) where
  inj = Inr
