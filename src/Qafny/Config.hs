{-# LANGUAGE TemplateHaskell #-}
module Qafny.Config where

import           Control.Lens.TH

data Configs = Configs
  { _stdlibPath :: String
  }

$(makeLenses ''Configs)
