{-# LANGUAGE
    ConstraintKinds
  , FlexibleContexts
  , NamedFieldPuns
  , TupleSections
  , TypeApplications
  , TypeOperators
  #-}

module Qafny.Codegen.Bindings where

import           Qafny.Effect
import           Qafny.Syntax.AST
import           Qafny.Utils.EmitBinding


-- * Functions related to Bindings for the Codegen phase
findEmitBindingsFromPartition
  :: StateMayFail sig m
  => Partition -> QTy -> m [Binding']
findEmitBindingsFromPartition Partition{ranges} qt = do
  vqEmits <- findEmitBasesByRanges ranges
  return (uncurry Binding <$> vqEmits)
