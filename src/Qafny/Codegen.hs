{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}

module Qafny.Codegen where

import           Qafny.AST
import           Qafny.Transform
import           Qafny.Typing

import           Control.Monad.RWS
import           Control.Monad.Except
import           Control.Lens
import qualified Data.Map.Strict as Map 

--------------------------------------------------------------------------------
-- | Codegen 
--------------------------------------------------------------------------------

class Codegen a where
  -- | Augmentation: perform typecheck over `a` and rewrite `a` into `[a]`
  aug :: a -> Transform [a]

instance Codegen AST where  
  aug ast = do let k = Map.fromList (collectMethodTypes ast)
               local (kEnv %~ Map.union k) $ mapM aug ast

instance Codegen Toplevel where
  aug q@(QMethod v bds rts rqs ens block) =
    do tEnv <- asks $ appkEnvWithBds bds
       -- sync kState with kEnv because when handling Stmts, environment becomes
       -- a state!
       kSt .= tEnv ^. kEnv
       block' <- only1 $ local (const tEnv) $ aug block
       return [QMethod v bds rts rqs ens block']
  aug q@(QDafny _) = return [q] 

instance Codegen Block where
  aug (Block stmts) =
    do kSt' <- use kSt                -- push a kindSt
       stmts' <- mapM aug stmts
       kSt .= kSt'                    -- restore when exiting the block
       return [Block $ concat stmts'] -- return the result of the block
  
instance Codegen Stmt where
  aug s@(SVar (Binding v t) eM) = 
    kSt %= Map.insert v t >> doE eM
    where 
      doE :: Maybe Exp -> Transform [Stmt]
      doE Nothing = return [s]
      doE (Just e) =
        do te <- typing e
           checkSubtype t te -- check if `t` agrees with the type of `e`
           es <- aug e 
           t' <- aug t
           when (length t' == length es) $
             throwError "augmented type and expressions are of differnt type"
           vs <- gensymN (length t') v
           undefined
  aug s = return [s]

instance Codegen Exp where
  aug (EOp2 op2 e1 e2) =
    do top <- typing op2
       t1 <- typing e1
       t2 <- typing e2
       _ <- checkSubtype2 top t1 t2
       return augNor op2
       where augNor ONor = EDafny "seq"
  aug e = return [e]

instance Codegen Ty where
  aug (TQ TNor) = return [TSeq TNat] -- TODO complete the phase type here
  aug e = return [e]

--------------------------------------------------------------------------------
-- | Helpers 
--------------------------------------------------------------------------------

only1 :: Show a => Transform [a] -> Transform a
only1 = (=<<) $
  \case [x] -> return x
        e   -> throwError $ "[only1]: " ++ show e ++ "is not a singleton"


--------------------------------------------------------------------------------
-- | Wrapper 
--------------------------------------------------------------------------------


codegen :: AST -> (Either String AST, TState, ())
codegen = (_1 %~ fmap concat) . runTransform . aug
