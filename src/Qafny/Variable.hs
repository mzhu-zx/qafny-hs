{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

module Qafny.Variable where

import Qafny.AST (Ty(..), typeTag) 

class Variable s where
  variable :: s -> String

instance Variable String where
  variable = id

instance Variable Ty where
  variable = typeTag

instance Variable Int where
  variable = show

instance (Variable a, Variable b) => Variable (a, b) where
  variable (a, b) = variable a ++ "__" ++ variable b
