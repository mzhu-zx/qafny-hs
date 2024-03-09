{-# LANGUAGE
    RankNTypes
  , TemplateHaskell
  #-}

module Qafny.Utils.TraceF where

import           Control.Effect.Trace
    (Has, Trace, trace)
import           Text.Printf
    (PrintfArg, printf)

-- TODO: This is really hard to solve.
-- tracef :: (PrintfArg r, Has Trace sig m) => String -> [r] -> m ()
-- tracef s [] = trace s
-- tracef s (r1 : rs) = trace $ go (printf s) rs 
--   where
--     go f [] = f r1 :: String
--     go f (x : xs) = go (f x) xs

