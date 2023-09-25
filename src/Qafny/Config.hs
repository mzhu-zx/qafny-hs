module Qafny.Config where

import           Control.Lens.TH

data Configs = Configs
  { stdlibPath :: String --
  , depth :: Int         -- the relative depth between the root and the file
  }

defaultConfigs :: Configs
defaultConfigs = Configs
  { stdlibPath = "../../external/"
  , depth = 0
  }

