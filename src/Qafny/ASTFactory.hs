module Qafny.ASTFactory where

import Qafny.AST

--------------------------------------------------------------------------------
-- | AST Constants
-------------------------------------------------------------------------------
wild :: Var
wild =  "_"

constExp :: Exp -> EmitExp
constExp = ELambda wild

qComment :: String -> Stmt
qComment = SDafny . ("// " ++)


--------------------------------------------------------------------------------
-- * Special Constructors
--------------------------------------------------------------------------------
natB :: Var -> Binding
natB = (`Binding` TNat)

-- | Construct an interval guard over a variable
-- @
--   l <= x < r
-- @
eIntv :: Var -> Exp -> Exp -> Exp
eIntv x l r = EEmit (EOpChained l [(OLe, EVar x), (OLt, r)])

eSub :: Exp -> Exp -> Exp
eSub = EOp2 OSub

ands :: [Exp] -> Exp
ands [] = EBool True
ands (x : xs) = EEmit (EOpChained x [ (OAnd, x') | x' <- xs ])

eAt :: Exp -> Exp -> Exp
eAt e1 e2 = EEmit (ESelect e1 e2)