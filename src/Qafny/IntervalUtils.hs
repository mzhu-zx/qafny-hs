module Qafny.IntervalUtils where

import           Debug.Trace    (trace)
import           Qafny.AST      (Exp (..), Op2 (OAdd, OSub), Range (..))
import           Qafny.Interval
import           Text.Printf    (printf)

type NInt = Interval Nat

expToNat :: Exp -> Nat
expToNat (ENum a)          = if a >= 0 then Nat a else Mt
expToNat (EVar _)          = Inf       -- overapproximate variables to infinity
expToNat (EOp2 OAdd e1 e2) = expToNat e1 + expToNat e2
expToNat (EOp2 OSub e1 e2) = expToNat e1 - expToNat e2
expToNat _ = Inf

rangeToNInt :: Range -> NInt
rangeToNInt r@(Range _ n m) =
  let i = case (expToNat n, expToNat m - 1) of
            (Inf, Inf) -> Interval (Nat 0) Inf -- overapproximate
            (x, y)     -> Interval x y
  in trace (printf "[rangeToNInt]: %s ← %s " (show i) (show r)) i
