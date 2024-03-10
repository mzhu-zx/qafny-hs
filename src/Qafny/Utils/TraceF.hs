{-# LANGUAGE
    FlexibleContexts
  , FlexibleInstances
  , RankNTypes
  , UndecidableInstances
  #-}

module Qafny.Utils.TraceF where

import           Control.Effect.Trace
    (Has, Trace, trace)
import           Text.Printf
    (PrintfArg, printf)

class Traceable r where
  tracef :: String -> r

instance Has Trace sig m => Traceable (m ()) where
  tracef = trace

instance ( PrintfArg a
         , Has Trace sig m
         )
         => Traceable (a -> m ()) where
  tracef s a = trace $ printf s a

instance ( PrintfArg a
         , PrintfArg b
         , Has Trace sig m
         )
         => Traceable (a -> b -> m ())  where
  tracef s a b = trace $ printf s a b

instance ( PrintfArg a
         , PrintfArg b
         , PrintfArg c
         , Has Trace sig m
         )
         => Traceable (a -> b -> c -> m ()) where
  tracef s a b c = trace $ printf s a b c

instance ( PrintfArg a
         , PrintfArg b
         , PrintfArg c
         , PrintfArg d
         , Has Trace sig m
         )
         => Traceable (a -> b -> c -> d -> m ()) where
  tracef s a b c d = trace $ printf s a b c d

instance ( PrintfArg a
         , PrintfArg b
         , PrintfArg c
         , PrintfArg d
         , PrintfArg e
         , Has Trace sig m
         )
         => Traceable (a -> b -> c -> d -> e -> m ()) where
  tracef s a b c d e = trace $ printf s a b c d e

instance ( PrintfArg a
         , PrintfArg b
         , PrintfArg c
         , PrintfArg d
         , PrintfArg e
         , PrintfArg f
         , Has Trace sig m
         )
         => Traceable (a -> b -> c -> d -> e -> f -> m ()) where
  tracef s a b c d e f = trace $ printf s a b c d e f
