{-# LANGUAGE FlexibleInstances, TypeSynonymInstances #-}

module Qafny.Variable where

import           Qafny.AST (Binding (..), Ty (..), typeTag, Loc (..))

class Variable s where
  variable :: s -> String

instance Variable String where
  variable = id

instance Variable Ty where
  variable = typeTag

instance Variable Int where
  variable = show

instance Variable Binding where
  variable (Binding s t) = variable (s, t)

instance Variable Loc where
  variable = ("loc__" ++) . deref

instance (Variable a, Variable b) => Variable (a, b) where
  variable (a, b) = variable a ++ "__" ++ variable b
