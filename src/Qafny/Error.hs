module Qafny.Error where

import qualified Data.Map.Strict as Map

import           Qafny.AST
import           Text.Printf     (printf)

data QError = UnknownVariableError Var (Map.Map Var Ty)
            | UnknownPartitionError Partition
            | UnknownRangeError Range
            | UnknownLocError Loc
  deriving Eq

instance Show QError where
  show (UnknownVariableError v env) =
    printf "Variable [%s] is not in the scope!\n%s" v (show env)
  show (UnknownPartitionError s) =
    printf "Partition [%s] is not in the scope!" (show s)
  show (UnknownRangeError r) =
    printf "Range [%s] is not in the scope!" (show r)
  show (UnknownLocError l) =
    printf "Loc [%s] is not in the scope!" (show l)
