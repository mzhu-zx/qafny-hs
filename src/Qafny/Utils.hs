{-# LANGUAGE TypeApplications #-}
module Qafny.Utils where

--
import           Control.Carrier.State.Church (State)
import           Control.Effect.Error         (Error, Has, throwError)
import           Control.Effect.Lens
import           Control.Lens                 (at, (?~))

--
import           Effect.Gensym                (Gensym, gensym)

--
import qualified Data.Map.Strict              as Map
import qualified Data.Set                     as Set
import           Qafny.AST                    (Binding, Loc (..))
import           Qafny.Transform              (TState, emitSt)
import           Qafny.Variable               (Variable (variable))
import           Text.Printf                  (printf)


-- catchMaybe
--   :: Has (Error e) sig m
--   => m (Maybe a)
--   -> m a
--   -> m a
-- catchMaybe mayFail fail' =
--   mayFail >>= maybe fail' return

-- | Catch the error in the Maybe and rethrow it as an Error
rethrowMaybe
  :: Has (Error e) sig m
  => m (Maybe a)
  -> e
  -> m a
rethrowMaybe mayFail err =
  mayFail >>= maybe (throwError err) return


gensymLoc
  :: ( Has (Gensym String) sig m )
  => String -> m Loc
gensymLoc = (Loc <$>) . gensym . variable . Loc

-- | Generate a new symbol for emit variable and add it to emitSt
gensymEmit
  :: ( Has (Gensym Binding) sig m
     , Has (State TState) sig m
     )
  => Binding -> m String
gensymEmit b = do
  name <- gensym b
  emitSt %= (at b ?~ name)
  return name

-- | Lookup for emitted symbols in emitSt
findEmitSym
  :: ( Has (State TState) sig m
     , Has (Error String) sig m
     )
  => Binding -> m String
findEmitSym b = do
  rethrowMaybe @String
    (use (emitSt . at b)) $
    printf "the binding `%s` cannot be found in the renaming state." (show b)


-- | Remove bindings from emitSt
removeEmitBindings
  :: ( Has (State TState) sig m)
  => [Binding] -> m ()
removeEmitBindings bs = do
  emitSt %= (`Map.withoutKeys` Set.fromList bs)
