{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}

module Qafny.Codegen where

import Qafny.AST
import Data.Map
import Data.Functor.Identity
import Control.Monad.State
import Control.Monad.Except
import Control.Lens.TH
import Control.Lens

import Data.Bifunctor

-- type Session = Var

data TState = TState
  { _kEnv :: Map Var Ty
  , _sEnv :: Map Var QTy
  }
  deriving Show

initTState :: TState
initTState = TState { _kEnv = mempty, _sEnv = mempty }  

$(makeLenses ''TState)

type Gen a = ExceptT String (StateT TState Identity) a

class Codegen a where
  gen :: a -> Gen a

instance Codegen AST where  
  gen = return

-- Compute types of methods from the toplevel
collectMethodTypes :: AST -> [Ty]
collectMethodTypes a = [ TMethod idt (bdTypes ins) (bdTypes outs)
                       | QMethod idt ins outs _ _ _ <- a]

bdTypes :: Bindings -> [Ty]
bdTypes b = [t | Binding _ t <- b]

runGen :: Gen a -> (Either String a, TState)
runGen = fuseError . runIdentity . flip runStateT initTState . runExceptT
  where
    fuseError :: (Either String a, TState) -> (Either String a, TState)
    fuseError (e, st) = (first (++ "\nCodeGen State:\n" ++ show st) e, st)
