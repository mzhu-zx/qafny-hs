{-# LANGUAGE TypeApplications #-}
module Qafny.Gensym(runGensym) where

import qualified Carrier.Gensym.Emit as GEmit
import qualified Carrier.Gensym.Meta as GMeta
import           Qafny.AST           (Ty)

runGensym
  :: Functor m
  => GMeta.GensymC String (GEmit.GensymC (String, Ty) m) a
  -> m (Int, [(String, Ty)], (Int , a))
runGensym = GEmit.runGensymEmit . GMeta.runGensymMeta @String
