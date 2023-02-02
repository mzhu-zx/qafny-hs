module Qafny.Codegen where

import Qafny.AST
import Data.Functor.Identity

type Gen a = Identity a
gen :: AST -> Gen AST
gen = return

runGen :: Identity a -> a
runGen = runIdentity 
