{-# LANGUAGE
    FlexibleInstances
  , TypeOperators
  , TypeSynonymInstances
  #-}

module Qafny.Variable where

import           Data.Sum
import           Qafny.Syntax.AST
import           Qafny.Syntax.EmitBinding
import           Qafny.TypeUtils  (typingQEmit)
import           Text.Printf      (printf)

class Variable s where
  variable :: s -> String

instance Variable String where
  variable = id

instance Variable Ty where
  variable = if True then typeTag' else typeTag
    where
      typeTag' :: Ty -> String
      typeTag' TNat     = "nat"
      typeTag' TInt     = "int"
      typeTag' TBool    = "bool"
      typeTag' (TSeq t) = "seq'" ++ typeTag' t ++ "'"
      typeTag' _        = "unsupported"


instance Variable Int where
  variable = show

instance Variable Op2 where
  variable OAdd = "_add_"
  variable OSub = "_sub_"
  variable _    = undefined

instance Variable (Exp ()) where
  variable (ENum n) = variable n
  variable (EVar v) = variable v
  -- TODO: I need a way to specify compact vs full spec
  variable (EOp2 op e1 e2) =
    if True
    then "compact"
    else  printf "l_%s_%s_%s_r" (variable e1) (variable op) (variable e2)
  variable _        = undefined

instance Variable Range where
  variable (Range x l r) =
    if True
    then variable x
    else printf "%s_%s_%s" (variable x) (variable l) (variable r)

instance Variable (Binding ()) where
  variable (Binding s t) = variable (s, t)

instance Variable PhaseTy where
  variable PT0       = "phase_0_"
  variable (PTN n _) = variablePhaseN n

variablePhaseN :: Int -> String
variablePhaseN n = printf "phase_%d_" n

instance Variable QTy where
  variable = variable . typingQEmit

instance (Variable a, Variable b) => Variable (a :+: b) where
  variable (Inl l) = variable l
  variable (Inr r) = variable r

-- instance Variable EmitBinding where
--   variable (RBinding r) = variable r
--   variable (BBinding b) = variable b
--   variable (LBinding v) = variable v

instance Variable Loc where
  variable = ("loc__" ++) . deref

instance (Variable a, Variable b) => Variable (a, b) where
  variable (a, b) =
    if True
    then variable a ++ "_" ++ variable b
    else variable a ++ "__" ++ variable b

instance Variable Emitter where
  variable (EmBaseSeq r qt) = variable (r, qt)
  variable (EmPhaseSeq b i) = variable (b, variablePhaseN i)
  variable EmAmplitude = "amplitude"
