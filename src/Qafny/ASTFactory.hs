module Qafny.ASTFactory where

import           Qafny.AST
import           Qafny.Partial (reduce)

--------------------------------------------------------------------------------
-- | AST Constants
-------------------------------------------------------------------------------
wild :: Var
wild =  "_"

constExp :: Exp' -> EmitExp
constExp = ELambda wild

qComment :: String -> Stmt'
qComment = SDafny . ("// " ++)


--------------------------------------------------------------------------------
-- * Special Constructors
--------------------------------------------------------------------------------
natB :: Var -> Binding'
natB = (`Binding` TNat)

-- | Construct an interval guard over a variable
-- @
--   l <= x < r
-- @
eIntv :: Var -> Exp' -> Exp' -> Exp'
eIntv x l r = EEmit (EOpChained l [(OLe, EVar x), (OLt, r)])

ands :: [Exp'] -> Exp'
ands []       = EBool True
ands (x : xs) = EEmit (EOpChained x [ (OAnd, x') | x' <- xs ])

-- | Make a chained, left-associated expression
--
-- This is done in different fashion from 'ands' because the constant fold
-- doesn't work with the 'EmitExp's.
--
joinArith :: Op2 -> Exp' -> [Exp'] -> Exp'
joinArith _ e [] = e
joinArith op _ (x : xs) =
  foldr inner id xs x
  where
    inner y f = f . (EOp2 op `flip` y)

eAt :: Exp' -> Exp' -> Exp'
eAt e1 e2 = EEmit (ESelect (reduce e1) (reduce e2))

eEq :: Exp' -> Exp' -> Exp'
eEq = EOp2 OEq

sliceV :: Var -> Exp' -> Exp' -> Exp'
sliceV x l r = EEmit (ESlice (EVar x) (reduce l) (reduce r))


callMap :: Exp' -> Exp' -> Exp'
callMap f e = EEmit (ECall "Map" [f, e])


cardV :: Var -> Exp'
cardV = EEmit . ECard . EVar
