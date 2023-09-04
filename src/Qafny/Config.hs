module Qafny.Config where

import           Control.Lens.TH

data Configs = Configs { stdlibPath :: String }

defaultConfigs :: Configs
defaultConfigs = Configs { stdlibPath = "../../external/" }

