module Qafny.Syntax.Builder where

import           Control.Monad.Reader
import qualified Data.Text.Lazy.Builder as TB

-- {-# INLINE t #-}
-- t :: TB.Builder -> TB.Builder
-- t x = x

newtype Builder_ a = Builder { doBuild :: Reader (Int, Bool) a }
  deriving (Functor, Applicative, Monad, (MonadReader (Int, Bool)))
type Builder = Builder_ TB.Builder

-- {-# INLINE rt #-}
-- rt :: TB.Builder -> Builder
-- rt = return

instance Semigroup Builder where
  (<>) = liftM2 (<>)

instance Monoid Builder where
  mempty = return mempty


