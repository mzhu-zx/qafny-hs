module Qafny.IntervalUtils where

-- import           Debug.Trace    (trace)
import           Qafny.AST      (Exp (..), Op2 (OAdd, OSub), Range (..), fVars)
import           Qafny.Interval
import           Text.Printf    (printf)

trace :: String -> a -> a
trace _ i = i
{-# INLINE trace #-}

expToNat :: Exp -> Nat
expToNat (ENum a)          = if a >= 0 then Nat a else Mt
expToNat (EVar _)          = Inf       -- overapproximate variables to infinity
expToNat (EOp2 OAdd e1 e2) = expToNat e1 + expToNat e2
expToNat (EOp2 OSub e1 e2) = expToNat e1 - expToNat e2
expToNat _ = Inf

rangeToNInt :: Range -> NatInterval
rangeToNInt r@(Range _ n m) =
  let i = case (expToNat n, expToNat m - 1) of
            (Inf, Inf) -> Interval (Nat 0) Inf -- overapproximate
            (x, y)     -> Interval x y
  in trace (printf "[rangeToNInt]: %s ← %s " (show i) (show r)) i

γRange :: String -> NatInterval -> Maybe Range
γRange x intv@(Interval (Nat i) (Nat j)) =
  if isBot intv then Nothing
  else Just $ Range x (ENum i) (ENum (j + 1))
γRange _ _                          = Nothing


-- TODO: Implement an OnePoint analysis to conclude that
-- @
--   q[i .. i + 1] 
-- @
-- is a domain with exactly one element.

-- expToPoint :: Exp -> String -> PointInt
-- expToPoint x e =
--   case e of
--     ENum x

data Analysis
  = OnePoint PointInt
  | NatOnly NatInterval
  | Simple

-- TODO: Implement an classification that takes one or two expressions and
-- decide which analysis to run.
-- Observation: 
--   1) If two Exp's are both in N, then it suffices to solve with NatOnly
--   2) If two Exp's are both in P(x), use PointInt and emit a check to make the
--      the entire Point interval a Nat
--   3) Half-and-Half, this requires a constraint reasoning. 
--   4) Otherwise, we conclude "NO" and defer to the future SMT approach

-- classify :: Exp -> Analysis
-- classify e =
--   case fVars e of
--     [] -> NatOnly (expToNat e)
--     [x] -> OnePoint (projectTo)
