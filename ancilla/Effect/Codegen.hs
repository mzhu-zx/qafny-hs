{-# LANGUAGE
    GADTs
  #-}

module Qafny.Effect.Codegen where


import           Control.Algebra
import           Data.Kind       (Type)
import           Qafny.AST


-- | Effects for generating statements and blocks


data Codegen (m :: Type -> Type) ans where
  GenCoercion :: [Stmt'] -> Codegen m ()
  GenCode     :: [Stmt'] -> Codegen m ()
  Reset       :: Codegen m [Stmt']
                               
genCoercion :: Has Codegen sig m => [Stmt'] -> m ()
genCoercion = send . GenCoercion

genCode :: Has Codegen sig m => [Stmt'] -> m ()
genCode = send . GenCode

reset :: Has Codegen sig m => m [Stmt']
reset = send Reset

genBlock :: Has Codegen sig m => m () -> m ()
genBlock m = do
  pre <- reset
  block <- m >> reset
  genCode $ pre ++ [SEmit . SBlock . Block $ block]
