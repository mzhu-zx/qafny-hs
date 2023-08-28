{-# LANGUAGE
    GADTs
  #-}

module Qafny.Carrier.Codegen where


import           Control.Algebra
import           Data.Kind            (Type)
import           Qafny.AST
import           Qafny.Effect.Codegen


-- | Effects for generating statements and blocks

newtype CodegenC m a = 
  CodegenC { runCodegenC ::  }
