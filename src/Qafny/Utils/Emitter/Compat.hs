{-# LANGUAGE
    ConstraintKinds
  , FlexibleContexts
  , NamedFieldPuns
  , TupleSections
  , TypeApplications
  , TypeOperators
  #-}


module Qafny.Utils.Emitter.Compat
  (findEmitRanges)
where

-- eff
import           Control.Algebra
    (Has)
import           Control.Effect.Error
import           Control.Effect.State

-- Qafny
import           Data.Sum
    (Injection (inj))
import           Qafny.Env
import           Qafny.Syntax.AST
    (Range, Var)
import           Qafny.Syntax.EmitBinding
import           Qafny.Utils.EmitBinding

-- | Backward compatibility to previous EmitBinding queries

type StateMayFail sig m =
  (Has (Error String) sig m , Has (State TState) sig m)

{-# DEPRECATED findEmitRanges  "Use 'findVisitED' instead" #-}
findEmitRanges
  :: StateMayFail sig m
  => [Range] -> m [Var]
findEmitRanges = findVisitEDs evBasis . (inj <$>)
