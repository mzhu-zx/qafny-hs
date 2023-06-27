{-# LANGUAGE FlexibleInstances, TypeSynonymInstances, UndecidableInstances #-}

module Qafny.Variable where

import           Qafny.AST

class Variable s where
  variable :: s -> String

instance Variable (f (Mu f)) => Variable (Mu f) where
  variable = (variable .$)

instance Variable String where
  variable = id

instance Variable Ty where
  variable = typeTag

instance Variable Int where
  variable = show

instance Variable Binding where
  variable (Mu (Binding s t)) = variable (s, t)

instance Variable Loc where
  variable = ("loc__" ++) . deref

instance (Variable a, Variable b) => Variable (a, b) where
  variable (a, b) = variable a ++ "__" ++ variable b
