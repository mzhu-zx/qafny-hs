{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}

module Qafny.Codegen where

import           Qafny.AST
import           Data.Functor.Identity
import           Control.Monad.RWS
import           Control.Monad.Except
import           Control.Lens.TH
import           Control.Lens
import           Data.Bifunctor
import qualified Data.Map.Strict as Map 

data TEnv = TEnv
  { _kEnv :: Map.Map Var Ty
  }

data TState = TState
  {_sEnv :: Map.Map Session QTy
  }

$(makeLenses ''TState)
$(makeLenses ''TEnv)

instance Show TState where
  show st = "  Kind Environment" ++ show (st ^. sEnv)

instance Show TEnv where
  show st = "  Session Environment" ++ show (st ^. kEnv)
            

initTEnv :: TEnv
initTEnv = TEnv { _kEnv = mempty }  

initTState :: TState
initTState = TState { _sEnv = mempty }  

--------------------------------------------------------------------------------
-- General 
--------------------------------------------------------------------------------
type Transform a = ExceptT String (RWS TEnv () TState) a

--------------------------------------------------------------------------------
-- Codegen 
--------------------------------------------------------------------------------

class Codegen a where
  gen :: a -> Transform a

instance Codegen AST where  
  gen ast = do let kEnv = Map.fromList (collectMethodTypes ast)
               return ast 

-- Compute types of methods from the toplevel
collectMethodTypes :: AST -> [(Var, Ty)]
collectMethodTypes a = [ (idt, TMethod (bdTypes ins) (bdTypes outs))
                       | QMethod idt ins outs _ _ _ <- a]

bdTypes :: Bindings -> [Ty]
bdTypes b = [t | Binding _ t <- b]

--------------------------------------------------------------------------------
-- Typing 
--------------------------------------------------------------------------------

class Typing a t where
  typing :: a -> Transform t

instance Typing Exp Ty where
  typing (ENum _)  = return TNat
  typing (EVar x)  =
    do k <- asks (view $ kEnv . at x)
       maybe (unknownVariableError x) return k 
  typing e = throwError $ "Typing for "  ++ show e ++ " is unimplemented!"


--------------------------------------------------------------------------------
-- Error Reporting
--------------------------------------------------------------------------------
unknownVariableError :: String -> Transform a
unknownVariableError s = throwError $ "Variable " ++ s ++ " is not in the environemnt"


--------------------------------------------------------------------------------
-- Wrapper
--------------------------------------------------------------------------------
runTransform :: Transform a -> (Either String a, TState, ())
runTransform = fuseError . (\x -> runRWS x initTEnv initTState) . runExceptT
  where
    fuseError :: (Either String a, TState, ()) -> (Either String a, TState, ())
    fuseError comp = _1 %~ first (++ "Codegen terminted with an error! States:" ++ show st) $ comp
      where st = comp ^. _3
