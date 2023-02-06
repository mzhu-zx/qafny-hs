{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}

module Qafny.Codegen where

import           Qafny.AST
import           Data.Functor.Identity
import           Control.Monad.State
import           Control.Monad.Except
import           Control.Lens.TH
import           Control.Lens
import           Data.Bifunctor
import qualified Data.Map.Strict as Map 

data TState = TState
  { _kEnv :: Map.Map Var Ty
  , _sEnv :: Map.Map Session QTy
  }

$(makeLenses ''TState)

instance Show TState where
  show st = "  Kind Environment" ++ show (st ^. kEnv) ++
            "\n  Session Environment" ++ show (st ^. sEnv)

initTState :: TState
initTState = TState { _kEnv = mempty, _sEnv = mempty }  

type Gen a = ExceptT String (StateT TState Identity) a

class Codegen a where
  gen :: a -> Gen a

instance Codegen AST where  
  gen ast = do kEnv .= Map.fromList (collectMethodTypes ast)
               return ast 

-- Compute types of methods from the toplevel
collectMethodTypes :: AST -> [(Var, Ty)]
collectMethodTypes a = [ (idt, TMethod (bdTypes ins) (bdTypes outs))
                       | QMethod idt ins outs _ _ _ <- a]

bdTypes :: Bindings -> [Ty]
bdTypes b = [t | Binding _ t <- b]

runGen :: Gen a -> (Either String a, TState)
runGen = fuseError . runIdentity . flip runStateT initTState . runExceptT
  where
    fuseError :: (Either String a, TState) -> (Either String a, TState)
    fuseError (e, st) = (first (++ "Codegen terminted with an error! States:"
                                ++ show st) e, st)
