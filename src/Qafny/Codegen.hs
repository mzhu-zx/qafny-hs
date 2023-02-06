{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE LambdaCase #-}

module Qafny.Codegen where

import           Qafny.AST
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
  { _sSt :: Map.Map Session QTy,
    _kSt :: Map.Map Var Ty
  }

$(makeLenses ''TState)
$(makeLenses ''TEnv)

instance Show TState where
  show st = "  Kind State" ++ show (st ^. kSt) ++
            "\n  Session State" ++ show (st ^. kSt)

instance Show TEnv where
  show st = "  Kind Environment" ++ show (st ^. kEnv)

initTEnv :: TEnv
initTEnv = TEnv { _kEnv = mempty }  

initTState :: TState
initTState = TState { _sSt = mempty, _kSt = mempty }  

--------------------------------------------------------------------------------
-- General 
--------------------------------------------------------------------------------
type Transform a = ExceptT String (RWS TEnv () TState) a

--------------------------------------------------------------------------------
-- Codegen 
--------------------------------------------------------------------------------

class Codegen a where
  -- | Augmentation: perform typecheck over `a` and rewrite `a` into `[a]`
  aug :: a -> Transform [a]

instance Codegen AST where  
  aug ast = do let k = Map.fromList (collectMethodTypes ast)
               local (kEnv %~ Map.union k) $ foldr go (return []) ast
    where go :: Toplevel -> Transform [AST] -> Transform [AST]
          go top next = do top' <- aug top
                           rst' <- next
                           return $ top' : rst'
instance Codegen Toplevel where
  aug q@(QMethod v bds rts rqs ens block) =
    do tEnv <- asks $ appkEnvWithBds bds
       blk <- head <$> aug block
       return [q]
  aug q@(QDafny _) = return [q] 

instance Codegen Block where
  aug (Block stmts) =
    do kSt' <- use kSt      -- push a kindSt
       kSt .= kSt'          -- restore when exiting the block
       return [Block stmts] -- return the result of the block
  
instance Codegen Stmt where
  aug (SVar bds Nothing) = undefined
  aug s = return [s]



-- | Helpers 
 
only1 :: Show a => Transform [a] -> Transform a
only1 = (=<<) $
  \case [x] -> return x
        e   -> throwError $ show e ++ "is not a singleton"


--------------------------------------------------------------------------------
-- Typing 
--------------------------------------------------------------------------------

-- Compute types of methods from the toplevel
collectMethodTypes :: AST -> [(Var, Ty)]
collectMethodTypes a = [ (idt, TMethod (bdTypes ins) (bdTypes outs))
                       | QMethod idt ins outs _ _ _ <- a]

appkEnvWithBds :: Bindings -> TEnv -> TEnv
appkEnvWithBds bds = kEnv %~ appBds
  where appBds = Map.union $ Map.fromList [(v, t) | Binding v t <- bds]

bdTypes :: Bindings -> [Ty]
bdTypes b = [t | Binding _ t <- b]


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

codegen :: AST -> (Either String AST, TState, ())
codegen = (_1 %~ fmap concat) . runTransform . aug
