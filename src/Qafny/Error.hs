module Qafny.Error where

import qualified Qafny.AST   as AST
import           Text.Printf (printf)

data QError = UnknownVariableError AST.Var
           | UnknownSessionError AST.Session
           | UnknownRangeError AST.Range
  deriving Eq

instance Show QError where
  show (UnknownVariableError v) =
    printf "Variable [%s] is not in the scope!" v
  show (UnknownSessionError s) =
    printf "Session [%s] is not in the scope!" (show s)
  show (UnknownRangeError r) = 
    printf "Range [%s] is not in the scope!" (show r)
