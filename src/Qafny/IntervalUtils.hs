module Qafny.IntervalUtils where

import           Debug.Trace    (trace)
import           Qafny.AST      (ExpK (..), Exp (..), Range (..))
import           Qafny.Interval
import           Text.Printf    (printf)

type NInt = Interval Nat

expToNat :: Exp -> Nat
expToNat (ENum a) = if a >= 0 then Nat a else Mt
expToNat (EVar _) = Inf       -- overapproximate variables to infinity
expToNat _        = Inf       -- there could be some Op2 here, overapprox!

rangeToNInt :: Range -> NInt
rangeToNInt r@(Range _ n m) =
  let i = case (expToNat n, expToNat m) of
            (Inf, Inf) -> Interval (Nat 0) Inf -- overapproximate
            (x, y)     -> Interval x y
  in trace (printf "[rangeToNInt]: %s ← %s " (show i) (show r)) i
