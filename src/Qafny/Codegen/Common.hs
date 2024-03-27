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
codegenAssignEmitData :: [EmitData] -> [EmitData] -> [Stmt']
codegenAssignEmitData eds1 eds2 =
  concat $ zipWith go eds1 eds2
  where
    go = zipWith perVar `on` extractEmitables
    perVar (v1, _) (v2, _) = v1 ::=: EVar v2
