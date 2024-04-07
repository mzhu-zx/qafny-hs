module Qafny.Config where

data Mode
  = Verify
  | Format

data Configs = Configs
  { stdlibPath :: String --
  , depth      :: Int    -- the relative depth between the root and the file
  , mode       :: Mode
  }

defaultConfigs :: Configs
defaultConfigs = Configs
  { stdlibPath = "../../external/"
  , depth      = 0
  , mode       = Verify
  }

