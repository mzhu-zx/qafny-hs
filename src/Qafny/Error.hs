module Qafny.Error where

import qualified Data.Map.Strict   as Map

import           Qafny.Syntax.AST
    (Loc, Partition, Range, Var)
import           Qafny.Syntax.Emit
    (showEmitI, showEmit0, byLineT)
import           Qafny.Syntax.IR
    (MTy)
import           Text.Printf
    (printf)

data QError = UnknownVariableError Var (Map.Map Var MTy)
            | UnknownPartitionError Partition
            | UnknownRangeError Range
            | UnknownLocError Loc
            | AmbiguousRange Range [(Range, Loc)]

instance Show QError where
  show (UnknownVariableError v env) =
    printf "Variable [%s] is not in the scope!\n\nCurrent environment:\n%s" v (showEmitI 4 env)
  show (UnknownPartitionError s) =
    printf "Partition [%s] is not in the scope!" (show s)
  show (UnknownRangeError r) =
    printf "Range [%s] is not in the scope!" (showEmit0 r)
  show (UnknownLocError l) =
    printf "Loc [%s] is not in the scope!" (show l)
  show (AmbiguousRange r rs) =
    printf "Range %s is a subrange of multiple ranges: %s"
    (showEmit0 r) (showEmit0 (byLineT  rs))
