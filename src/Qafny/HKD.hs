{-# LANGUAGE TypeFamilies, FlexibleContexts, FlexibleInstances #-}

module Qafny.HKD where

import           Control.Monad.Identity

type family HKD f a where
  HKD Identity a = a
  HKD f a        = f a
