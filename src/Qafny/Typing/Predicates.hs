module Qafny.Typing.Predicates where

-- Effects
import           Qafny.Effect

-- Qafny
import           Data.Maybe
    (mapMaybe)
import           Qafny.Syntax.AST
import           Qafny.Typing.Phase hiding
    (throwError')
import Qafny.TypeUtils (assertPartQTyArity)


-- | Collect entanglement type signature from predicate-ish clauses
-- without checking the well-formedness of the predicate.
signatureFromPredicate :: Exp' -> Maybe (Partition, QTy, [Int])
signatureFromPredicate (ESpec s qt pexp) =
  let degrees = mapMaybe analyzeSpecDegree pexp
  in Just (s, qt, degrees)
signatureFromPredicate _                 = Nothing


-- | Check if a specification expression has correct corresponding types.
assertSpecWf :: QTy -> SpecExp -> Bool
assertSpecWf TNor  SESpecNor{}  = True
assertSpecWf THad  SESpecHad{}  = True
assertSpecWf TEn   SESpecEn{}   = True
assertSpecWf TEn01 SESpecEn01{} = True
assertSpecWf _     SEWildcard   = True
assertSpecWf _     _            = False

assertAssertionWf :: Exp' -> Bool
assertAssertionWf (ESpec part qty es) =
  assertPartQTyArity part qty && all (assertSpecWf qty) es
assertAssertionWf _ = True
