{-# LANGUAGE TemplateHaskell #-}
module Qafny.Codegen where

import Qafny.AST
import Data.Map
import Data.Functor.Identity

import Control.Lens.TH

type Session = Var

data TState = TState
  { _kEnv :: Map Var Ty
  , _sEnv :: Map Session QTy
  }

$(makeLenses ''TState)

type Gen a = Identity a
gen :: AST -> Gen AST
gen = return

-- Compute types of methods from the toplevel
collectMethodTypes :: AST -> [Ty]
collectMethodTypes a = [ TMethod idt (bdTypes ins) (bdTypes outs)
                       | QMethod idt ins outs _ _ _ <- a]

bdTypes :: Bindings -> [Ty]
bdTypes b = [t | Binding _ t <- b]

runGen :: Identity a -> a
runGen = runIdentity 
