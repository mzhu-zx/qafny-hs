{-# LANGUAGE TypeApplications #-}
module Qafny.Gensym(runGensym) where

import qualified Carrier.Gensym.Emit as GEmit
import qualified Carrier.Gensym.Meta as GMeta
import           Qafny.AST           (Ty, Binding(..), Bindings)

runGensym
  :: Functor m
  => GMeta.GensymC String (GEmit.GensymC Binding m) a
  -> m (Int, Bindings, (Int , a))
runGensym = GEmit.runGensymEmit . GMeta.runGensymMeta @String
