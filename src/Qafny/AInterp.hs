{-# LANGUAGE TupleSections #-}

module Qafny.AInterp where
import           Control.Algebra
import           Control.Effect.State (State, modify, put)

import           Control.Applicative  (Applicative (liftA2))
import           Control.Arrow        (Arrow (first))
import           Qafny.AST
-- | Arithemetic Expression Reduction
-- reduce an airth expression as much as possible!

flipOp :: Op2 -> Op2
flipOp OAdd = OSub
flipOp OSub = OAdd

flipStack :: [(Op2, Var)] -> [(Op2, Var)]
flipStack = fmap $ first flipOp

reduceExp :: Exp -> Exp
reduceExp e =
  let (ops, i) = interpExp e
  in foldr (\(op, v) ys -> EOp2 op ys (EVar v)) (ENum i) ops

interpExp :: Exp -> ([(Op2, Var)], Int)
interpExp = interpExpEnv []

interpExpEnv :: [(Var, Int)] -> Exp -> ([(Op2, Var)], Int)
interpExpEnv _   (ENum i) = ([], i)
interpExpEnv env (EVar v) = ([(OAdd, v)], 0) `maybe` ([],) $ lookup v env
interpExpEnv env (EOp2 OAdd e1 e2) =
  let (op1, i1) = interpExpEnv env e1
      (op2, i2) = interpExpEnv env e2
  in (op1 ++ op2, i1 + i2)
interpExpEnv env (EOp2 OSub e1 e2) =
  let (op1, i1) = interpExpEnv env e1
      (op2, i2) = interpExpEnv env e2
  in (op1 ++ flipStack op2, i1 - i2)

