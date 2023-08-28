{-# LANGUAGE
    GADTs
  #-}

module Qafny.Carrier.Codegen where


import           Control.Algebra
import           Control.Carrier.State.Strict
import           Data.Kind                    (Type)
import           Qafny.AST
import           Qafny.Effect.Codegen


-- | Effects for generating statements and blocks

newtype CodegenFullC m a = CodegenFullC { runFullCodegenC :: StateC Stmt' m a }

