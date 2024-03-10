module Qafny.Syntax.ASTFactory where

import           Qafny.Partial    (reduce)
import           Qafny.Syntax.AST

--------------------------------------------------------------------------------
-- | AST Constants
-------------------------------------------------------------------------------
wild :: Var
wild =  "_"

-- | An Oracle term that always returns a constant.
constLambda :: Exp' -> Exp'
constLambda = simpleLambda wild

{-# DEPRECATED constExp "Use constLambda instead" #-}
constExp :: Exp' -> Exp'
constExp = constLambda

qComment :: String -> Stmt'
qComment = SDafny . ("// " ++)

-- | An Oracle term w/o phase specification.
simpleLambda :: Var -> Exp' -> Exp'
simpleLambda v e = ELambda $
  LambdaF PhaseWildCard [v] Nothing [e]

multiLambda :: [Var] -> Exp' -> Exp'
multiLambda v = EEmit . EMultiLambda v


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

callMaps :: Exp' -> [Exp'] -> Exp'
callMaps f es = EEmit (ECall "Map" (f : es))



cardV :: Var -> Exp'
cardV = EEmit . ECard . EVar

mkAssignment ::  Var -> Var -> Stmt'
mkAssignment v1 v2 = v1 ::=: EVar v2

mkDAssignment :: Ty -> Var -> Var -> Stmt'
mkDAssignment t v1 v2 = SVar (Binding v1 t) (Just (EVar v2))


-- Erase phase arguments in a lambda term
lambdaUnphase :: Exp' -> Exp'
lambdaUnphase (ELambda l) = ELambda
  l{ bPhase = PhaseWildCard, ePhase = Nothing }
lambdaUnphase _           = error "Internal"
