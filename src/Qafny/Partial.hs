{-# LANGUAGE
    GeneralizedNewtypeDeriving
  , TupleSections
  #-}

module Qafny.Partial where
import           Control.Applicative (Applicative (liftA2))
import           Control.Arrow       (Arrow (first))
import           Qafny.AST

--------------------------------------------------------------------------------
-- $doc
-- 'Qafny.Partial' module implements the partial evaluation strategy of
-- expressions, (linear) arithmetic expressions and ranges in particular.
--
-- The goal is to reduce an expression with uninterpreted variables /as much as/
-- possible.
--
-- $doc
--------------------------------------------------------------------------------

newtype PEval a = PEval { pEval :: ([(Op2, Var)], a) }
  deriving (Functor)

instance Applicative PEval where
  pure = PEval . ([], )
  liftA2 f (PEval (l1, a1)) (PEval (l2, a2)) = PEval (l1 ++ l2, f a1 a2)

instance Monad PEval where
  (PEval (l1, a1)) >>= f =
    let (l2, a2) = pEval $ f a1
    in PEval (l1 ++ l2, a2)  

flipSign :: PEval a -> PEval a
flipSign = PEval . first flipStack . pEval

flipStack :: [(Op2, Var)] -> [(Op2, Var)]
flipStack = fmap $ first flipOp

flipOp :: Op2 -> Op2
flipOp OAdd = OSub
flipOp OSub = OAdd
flipOp _    = undefined

pushVar :: Var -> PEval Int
pushVar v = PEval ([(OAdd, v)], 0)

interpExpEnv :: [(Var, Exp)] -> Exp -> PEval Int
interpExpEnv env = interpExp . substE env

reduceExp :: Exp -> Exp
reduceExp e =
  let (ops, i) = pEval $ interpExp e
  in foldr (\(op, v) ys -> EOp2 op ys (EVar v)) (ENum i) ops

-- | Compute a (linear) arithmatic expression by reducing it as the combination of
-- one single constant and several pair of uninterpreted variables and their
-- symbols.
interpExp :: Exp -> PEval Int
interpExp (ENum i) = return i
interpExp (EVar v) = pushVar v
interpExp (EOp2 OAdd e1 e2) =
  liftA2 (+) (interpExp e1) (interpExp e2)
interpExp (EOp2 OSub e1 e2) =
  liftA2 (-) (interpExp e1) (flipSign $ interpExp e2)
interpExp _ = undefined

reduceP :: Partition -> Partition
reduceP = Partition . (reduceR <$>) . unpackPart 

reduceR :: Range -> Range
reduceR (Range x el er) = Range x (reduceExp el) (reduceExp er)

pevalP :: [(Var, Exp)] -> Partition -> Partition
pevalP env = reduceP . substP env
