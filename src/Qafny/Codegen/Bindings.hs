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
    (StateMayFail)
import           Qafny.Syntax.AST
import           Qafny.TypeUtils
    (typingQEmit)
import           Qafny.Utils.EmitBinding


-- * Functions related to Bindings for the Codegen phase
findEmitBindingsFromPartition
  :: StateMayFail sig m
  => Partition -> QTy -> m [Binding']
findEmitBindingsFromPartition Partition{ranges} qt = do
  vqEmits <- ((, typingQEmit qt) <$>) <$> findEmitBasesByRanges ranges
  return (uncurry Binding <$> vqEmits)
