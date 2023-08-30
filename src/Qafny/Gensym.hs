{-# LANGUAGE TypeApplications #-}
module Qafny.Gensym(resumeGensym) where

import qualified Carrier.Gensym.Emit as GEmit
import qualified Carrier.Gensym.Meta as GMeta
import           Qafny.Syntax.AST           (RBinding)

-- runGensym
--   :: Monad m
--   => GMeta.GensymC String (GEmit.GensymC Binding m) a
--   -> m (Int, [(Binding, String)], (Int , a))
-- runGensym = GEmit.runGensymEmit . GMeta.runGensymMeta @String

-- | Execute 2 nested 'Gensym' computation in sequence and outputs the generated
-- emit symbols from both computation separately.
-- The emit symbol list in the latter execution is emptied but the counter is
-- carried over to it.
resumeGensym
  :: Monad m
  => GEmit.GensymC RBinding (GMeta.GensymC String m) a
  -> GEmit.GensymC RBinding (GMeta.GensymC String m) b
  -> m (Int, (Int, ([(RBinding, String)], [(RBinding, String)]), (a, b)))
resumeGensym comp1 comp2 =
  GMeta.runGensymMeta @String $ do
    (i, s', a) <- GEmit.runGensymEmit comp1
    (j, s, b) <- GEmit.startGensymEmitWith i comp2
    return (j, (s', s), (a, b))

