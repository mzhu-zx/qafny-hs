{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -fprint-explicit-foralls #-}
module Qafny.Utils where

import           Control.Effect.Error           (Error, Has)

catchMaybe
  :: Has (Error e) sig m
  => m (Maybe a)
  -> m a
  -> m a
catchMaybe mayFail fail' = 
  mayFail >>= maybe fail' return  
