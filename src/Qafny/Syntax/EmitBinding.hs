{-# LANGUAGE
    FlexibleInstances
  , TypeOperators
  #-}

module Qafny.Syntax.EmitBinding where


import qualified Data.Map.Strict  as Map
import           Data.Sum
import           Qafny.Syntax.AST

-- * EmitBinding related functions

data EmitBinding
  = RBinding (Range, QTy :+: Int) -- range-based bindings
  | BBinding (Range :+: Loc, Int) -- phase binding of bases
  | LBinding (Loc, Int)           -- loc-based bindings
  deriving (Eq, Ord)

instance Substitutable EmitBinding where
  subst a (RBinding (r, t))     = RBinding (subst a r, t)
  subst a (BBinding (Inl r, t)) = BBinding (inj (subst a r), t)
  subst a b                     = b

  fVars (RBinding (r, _))     = fVars r
  fVars (BBinding (Inl r, _)) = fVars r
  fVars _                     = []

instance Substitutable (Map.Map EmitBinding Var) where
  subst = substMapKeys
  fVars = fVarMapKeys

instance Show EmitBinding where
  show (RBinding t) = "R" ++ show t
  show (BBinding t) = "B" ++ show t
  show (LBinding t) = "L" ++ show t


