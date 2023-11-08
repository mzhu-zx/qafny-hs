module Qafny.Error where

import qualified Data.Map.Strict   as Map

import           Qafny.Syntax.AST  (Loc, MTy, Partition, Range, Var)
import           Qafny.Syntax.Emit (showEmitI)
import           Text.Printf       (printf)

data QError = UnknownVariableError Var (Map.Map Var MTy)
            | UnknownPartitionError Partition
            | UnknownRangeError Range
            | UnknownLocError Loc

instance Show QError where
  show (UnknownVariableError v env) =
    printf "Variable [%s] is not in the scope!\n\nCurrent environment:\n%s" v (showEmitI 4 env)
  show (UnknownPartitionError s) =
    printf "Partition [%s] is not in the scope!" (show s)
  show (UnknownRangeError r) =
    printf "Range [%s] is not in the scope!" (show r)
  show (UnknownLocError l) =
    printf "Loc [%s] is not in the scope!" (show l)

