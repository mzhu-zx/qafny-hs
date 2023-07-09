module Qafny.IntervalUtils where

-- import           Debug.Trace    (trace)
import           Data.Bool        (bool)
import           Qafny.AST
    ( Exp (..)
    , Op2 (OAdd, OSub)
    , Range (..)
    , fVars
    )
import           Qafny.ASTFactory (eSub)
import           Qafny.Domain
import           Qafny.Interval
import           Qafny.Partial
import           Text.Printf      (printf)

trace :: String -> a -> a
trace _ i = i
{-# INLINE trace #-}


-- -- | Phantom type for expressions to be evaluated to a 'Nat' through 'PEval'
-- newtype NatExp = NatExp { unNE :: Exp }

-- -- Partial Evaluation Engine grants better precision at the cost of failure
-- -- when the result contains residue.
-- instance PartialOrd NatExp where
--   a ≤ b =  (>= 0) <$> valueOf (interpExp (unNE b `eSub` unNE a))

-- -- αPEval :: PEval Int -> Nat
-- -- αPEval p = case pEval p of
-- --   ([], a) -> Nat a
-- --   _       -> Inf

expToNat :: Exp -> Nat
expToNat (ENum a)          = if a >= 0 then Nat a else Mt
expToNat (EVar _)          = Inf       -- overapproximate variables to infinity
expToNat (EOp2 OAdd e1 e2) = expToNat e1 + expToNat e2
expToNat (EOp2 OSub e1 e2) = expToNat e1 - expToNat e2
expToNat _                 = Inf

rangeToNInt :: Range -> NatInterval
rangeToNInt r@(Range _ n m) =
  let i = case (expToNat n, expToNat m - 1) of
            (Inf, Inf) -> Interval (Nat 0) Inf -- overapproximate
            (x, y)     -> Interval x y
  in trace (printf "[rangeToNInt]: %s ← %s " (show i) (show r)) i

γRange :: String -> NatInterval -> Maybe Range
γRange x intv@(Interval (Nat i) (Nat j)) =
  isBot intv >>= bool (Just $ Range x (ENum i) (ENum (j + 1))) Nothing
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

-- data Analysis
--   = OnePoint PointInt
--   | NatOnly NatInterval
--   | Simple

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
