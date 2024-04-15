{-# LANGUAGE
    TypeFamilies
  #-}

module Qafny.Codegen.Common where

import           Data.Function
    (on)
import           Qafny.Syntax.AST
import           Qafny.Syntax.EmitBinding
--------------------------------------------------------------------------------
-- * EmitData Utils
--------------------------------------------------------------------------------
codegenAssignEmitData :: [(EmitData, EmitData)] -> [Stmt']
codegenAssignEmitData eds = uncurry go `concatMap` eds 
  where
    go = zipWith perVar `on` extractEmitables
    perVar (v1, _) (v2, _) = v1 ::=: EVar v2

codegenAssignEmitData' :: [(EmitData, EmitData)] -> [(Stmt', Var)]
codegenAssignEmitData' eds = uncurry go `concatMap` eds 
  where
    go = zipWith perVar `on` extractEmitables
    perVar (v1, _) (v2, _) = (v1 ::=: EVar v2, v1)

