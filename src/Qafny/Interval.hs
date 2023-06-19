{-# LANGUAGE FlexibleInstances #-}

module Qafny.Interval where
import           Text.Printf (printf)

-- Interval Interpreter

class Lattice a where
  isTop :: a -> Bool
  isBot :: a -> Bool
  (⊑) :: a -> a -> Bool
  (⊔) :: a -> a -> a
  (⊓) :: a -> a -> a


data Nat
  = Inf
  | Undef
  | Nat Int

instance Show Nat where
  show Inf     = "∞"
  show Undef   = "⊥"
  show (Nat i) = show i

instance Num Nat where
  a + b =
    case a of
      Undef -> Undef
      Inf   -> Inf
      Nat n -> case b of
        Undef -> Undef
        Inf   -> Inf
        Nat m -> Nat (n + m)

  a - b =
    case a of
      Undef -> Undef
      Inf   -> Inf
      Nat n -> case b of
        Undef -> Undef
        Inf   -> Inf
        Nat m -> if n - m >= 0 then Nat (n - m) else Undef
  a * b =
    case a of
      Undef -> Undef
      Inf   -> case b of
        Undef -> Undef
        Nat 0 -> Undef
        _     -> Inf
      Nat n -> case b of
        Undef -> Undef
        Inf   -> if n == 0 then Undef else Inf
        Nat m -> Nat $ n * m
  negate = undefined
  abs = undefined
  signum = undefined
  fromInteger = undefined

instance Eq Nat where
  Inf == Inf     = True
  Undef == Undef = True
  Nat n == Nat m = n == m
  _ == _         = False

instance Ord Nat where
  compare _ Inf           = LT
  compare Inf _           = GT
  compare Undef _         = LT
  compare _ Undef         = GT
  compare (Nat n) (Nat m) = compare n m

data Interval a = Interval a a

instance Show a => Show (Interval a) where
  show (Interval l r) = printf "[%s, %s]" (show l) (show r)

-- Lattice Interpretation of Concrete Nat Domain
instance Lattice (Interval Nat) where
  isTop (Interval (Nat 0) Inf) = True
  isTop _                      = False

  isBot (Interval Undef _) = True
  isBot (Interval _ Undef) = True
  isBot (Interval a b)     = a > b

  (Interval a1 b1) ⊑ (Interval a2 b2) = a1 <= a2 && b1 <= b2

  i1@(Interval a1 b1) ⊔ i2@(Interval a2 b2) =
    if (isTop i1 || isTop i2)
    then Interval (Nat 0) Inf
    else Interval (min a1 a2) (max b1 b2)

  i1@(Interval a1 b1) ⊓ i2@(Interval a2 b2) =
    if (isBot i1 || isBot i2)
    then Interval Inf Undef
    else Interval (max a1 a2) (min b1 b2)


