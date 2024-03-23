module Qafny.Typing.Predicates where

-- Effects

-- Qafny
import           Qafny.Syntax.AST
import           Qafny.Typing.Phase         hiding
    (throwError')


-- Utils


-- | Collect entanglement type signature from predicate-ish clauses
-- without checking the well-formedness of the predicate.

signatureFromPredicate :: Exp' -> Maybe (Partition, QTy, [Maybe Int])
signatureFromPredicate (ESpec s qt pexp) =
  let degrees = analyzeSpecDegree <$> pexp
  in Just (s, qt, degrees)
signatureFromPredicate _                 = Nothing
