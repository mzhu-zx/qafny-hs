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

instance (Eq f, Eq g) => Eq (f :+: g) where
  (Inl f1) == (Inl f2) = f1 == f2
  (Inr f1) == (Inr f2) = f1 == f2
  _ == _               = False

instance (Ord f, Ord g) => Ord (f :+: g) where
  compare (Inl _) (Inr _) = LT
  compare (Inr _) (Inl _) = GT
  compare (Inl f1) (Inl f2) = compare f1 f2
  compare (Inr f1) (Inr f2) = compare f1 f2

class Injection f g where
  inj :: f -> g

instance {-# OVERLAPPABLE #-} Injection f (f :+: g) where
  inj = Inl

instance {-# OVERLAPPABLE #-} Injection f h => Injection f (h :+: g) where
  inj = Inl . inj

instance Injection g (f :+: g) where
  inj = Inr

projLeft :: (f :+: g) -> Maybe f
projLeft (Inl f) = Just f
projLeft _       = Nothing

projRight :: (f :+: g) -> Maybe g
projRight (Inr g) = Just g
projRight _       = Nothing

