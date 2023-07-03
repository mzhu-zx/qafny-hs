{-# LANGUAGE
    FlexibleInstances
  , TypeSynonymInstances
  #-}

module Qafny.Variable where

import           Qafny.AST
    ( Binding (..)
    , Exp (..)
    , Loc (..)
    , Op2 (..)
    , Range (..)
    , Ty (..)
    , typeTag
    )
import           Text.Printf (printf)

class Variable s where
  variable :: s -> String

instance Variable String where
  variable = id

instance Variable Ty where
  variable = typeTag

instance Variable Int where
  variable = show

instance Variable Op2 where
  variable OAdd = "_add_"
  variable OSub = "_sub_"
  variable _    = undefined

instance Variable Exp where
  variable (ENum n) = variable n
  variable (EVar v) = variable v
  variable (EOp2 op e1 e2) =
    printf "l_%s_%s_%s_r" (variable e1) (variable op) (variable e2)
  variable _        = undefined

instance Variable Range where
  variable (Range x l r) =
    printf "%s_%s_%s" (variable x) (variable l) (variable r)


instance Variable Binding where
  variable (Binding s t) = variable (s, t)

instance Variable Loc where
  variable = ("loc__" ++) . deref

instance (Variable a, Variable b) => Variable (a, b) where
  variable (a, b) = variable a ++ "__" ++ variable b
