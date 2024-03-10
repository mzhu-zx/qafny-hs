module Qafny.Codegen.Utils where

import           Control.Algebra
import           Control.Effect.Error
import           Control.Effect.Reader
import           Data.Bool
    (bool)
import           Qafny.Syntax.AST

--------------------------------------------------------------------------------
-- * Splits
--
-- In a conditional, the portion of the states satisfying the condition should
-- not be changed. Therefore, an easy way is to produce two for each loop such
-- that one block has state-changing statements emitted, another has those
-- statements as no-ops.
--
-- putPure and putOpt are used to flag which ones are state-changing, and which
-- are not.
--------------------------------------------------------------------------------
-- put Stmt's anyway
putPure :: Has (Reader Bool) sig m
        => [Stmt'] -> m [Stmt']
putPure = pure

-- put Stmt's only if it's allowed
putOpt :: Has (Reader Bool) sig m => m [a] -> m [a]
putOpt s = do
  bool (pure []) s =<< ask
