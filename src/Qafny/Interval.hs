{-# LANGUAGE FlexibleInstances #-}

module Qafny.Interval where
import           Text.Printf (printf)

-- Interval Interpreter
data Nat
  = Inf
  | Mt
  | Nat Int

instance Show Nat where
  show Inf     = "∞"
  show Mt   = "⊥"
  show (Nat i) = show i

instance Num Nat where
  a + b =
    case a of
      Mt -> Mt
      Inf   -> Inf
      Nat n -> case b of
        Mt -> Mt
        Inf   -> Inf
        Nat m -> Nat (n + m)

  a - b =
    case a of
      Mt -> Mt
      Inf   -> Inf
      Nat n -> case b of
        Mt -> Mt
        Inf   -> Inf
        Nat m -> if n - m >= 0 then Nat (n - m) else Mt
  a * b =
    case a of
      Mt -> Mt
      Inf   -> case b of
        Mt -> Mt
        Nat 0 -> Mt
        _     -> Inf
      Nat n -> case b of
        Mt -> Mt
        Inf   -> if n == 0 then Mt else Inf
        Nat m -> Nat $ n * m
  negate = undefined
  abs = undefined
  signum = undefined
  fromInteger = undefined


--------------------------------------------------------------------------------
-- | Partial Ordering
--------------------------------------------------------------------------------
class PartialOrd a where
  (≤) :: a -> a -> Bool
  -- (≤) :: a -> a -> Maybe Bool

instance PartialOrd Nat where
  _       ≤ Inf     = True
  Inf     ≤ _       = False
  Mt      ≤ _       = True
  _       ≤ Mt      = False
  (Nat n) ≤ (Nat m) = n <= m

-- | anti-symmetry
(≡) :: PartialOrd a => a -> a -> Bool
a ≡ b = a ≤ b && b ≤ a



data Interval a = Interval a a

instance Show a => Show (Interval a) where
  show (Interval l r) = printf "[%s, %s]" (show l) (show r)

--------------------------------------------------------------------------------
-- | Lattice
--------------------------------------------------------------------------------
class Lattice a where
  isTop :: a -> Bool
  isBot :: a -> Bool
  (⊑) :: a -> a -> Bool
  (⊔) :: a -> a -> a
  (⊓) :: a -> a -> a


instance Lattice Nat where
  isTop = (≡ Inf)
  isBot = (≡ Mt)
  (⊑) = (≤)
  (⊔) a b = if a ≤ b then b else a
  (⊓) a b = if a ≤ b then a else b

-- Lattice Interpretation of Concrete Nat Domain
instance Lattice (Interval Nat) where
  isTop (Interval (Nat 0) Inf) = True
  isTop (Interval a b)         = False

  isBot (Interval a b) = not (a ≤ b)

  (Interval a1 b1) ⊑ (Interval a2 b2) = a1 ⊑ a2 && b1 ⊑ b2

  i1@(Interval a1 b1) ⊔ i2@(Interval a2 b2) =
    Interval (a1 ⊓ a2) (b1 ⊔ b2)

  i1@(Interval a1 b1) ⊓ i2@(Interval a2 b2) =
    Interval (a1 ⊔ a2) (b1 ⊓ b2)


