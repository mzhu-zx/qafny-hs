module Qafny.Effect
  ( module Control.Effect.Reader
  , module Control.Effect.Error
  , module Control.Effect.Catch
  , module Control.Effect.State
  , module Control.Effect.Trace
  , module Control.Effect.Lens
  , module Control.Algebra
  , module Effect.Gensym
  , GensymEmitterWithState, GensymEmitterWithStateError, StateMayFail
  ) where

-- | Re-export useful effects to avoid cluttered imports in other modules

import           Control.Algebra
    (Has)
import           Control.Effect.Catch
import           Control.Effect.Error
import           Control.Effect.Lens
import           Control.Effect.Reader
import           Control.Effect.State
import           Control.Effect.Trace
import           Effect.Gensym
    (Gensym, gensym)
import           Qafny.Syntax.EmitBinding
import           Qafny.Syntax.IR


type GensymEmitterWithState sig m =
  (Has (Gensym Emitter) sig m , Has (State TState) sig m)

type GensymEmitterWithStateError sig m =
  (GensymEmitterWithState sig m, Has (Error String) sig m)

type StateMayFail sig m =
  (Has (Error String) sig m , Has (State TState) sig m)
