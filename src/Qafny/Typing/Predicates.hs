-- | Specification and predicate typechecking
module Qafny.Typing.Predicates(
  wfSignatureFromPredicate
  ) where

-- Effects
import           Qafny.Effect

-- Qafny
import           Control.Monad
    (unless)
import           Data.Maybe
    (catMaybes, listToMaybe)
import           Qafny.Syntax.AST
import           Qafny.Syntax.Emit
    (showEmit0)
import           Qafny.Typing.Utils
    (assertPartQTyArity)
import           Qafny.Typing.Phase hiding
    (throwError')
import           Qafny.Utils
import           Text.Printf
    (printf)


throwError'
  :: ( Has (Error String) sig m )
  => String -> m a
throwError' = throwError @String . ("[Typing/Predicates] " ++)

--------------------------------------------------------------------------------
-- | Check if a specification expression has correct corresponding types.
assertSpecWf :: QTy -> SpecExp -> Bool
assertSpecWf TNor  SESpecNor{}  = True
assertSpecWf THad  SESpecHad{}  = True
assertSpecWf TEn   SESpecEn{}   = True
assertSpecWf TEn01 SESpecEn01{} = True
assertSpecWf _     SEWildcard   = True
assertSpecWf _     _            = False


-- | Collect entanglement type signature from predicate-ish clauses
-- without checking the well-formedness of the predicate.
wfSignatureFromPredicate
  :: Has (Error String) sig m
  => Exp' -> m (Maybe (Partition, QTy, Maybe Int))
wfSignatureFromPredicate e@(ESpec part qty es) = do
  unless isWf $
    throwError' (printf "Specification is not well formed.\n%s" (showEmit0 e))
  return $ Just (part, qty, degree)
  where
    degrees = analyzeSpecDegree <$> es
    isWf =
      assertPartQTyArity part qty  -- repr arity matches with qtype
      && all (assertSpecWf qty) es -- all specs are wf w.r.t. qtype
      && hasNoDup degrees          -- all phases have the same degree
    degree = listToMaybe $ catMaybes degrees
wfSignatureFromPredicate _ = return Nothing
