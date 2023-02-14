{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE LambdaCase #-}

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
    do
      kSt %= Map.insert v t
      extendSession t
      doE eM
   where
    extendSession :: Ty -> Transform ()
    extendSession (TQ qty) = sSt %= Map.insert (session1 v) qty
    extendSession _        = pure ()
    doE :: Maybe Exp -> Transform [Stmt]
    doE Nothing = return [s]
    doE (Just e) =
      do
        te <- typing e
        checkSubtype t te -- check if `t` agrees with the type of `e`
        es <- aug e
        ts <- aug t
        unless (length ts == length es) $
          throwError $
            "augmented type and expressions are of differnt length"
              ++ "\n  Types: "
              ++ show ts
              ++ "\n  Expression: "
              ++ show es
        vs <- gensymTys ts v
        return $ zipWith3 mkSVar vs ts es
     where
      mkSVar :: Var -> Ty -> Exp -> Stmt
      mkSVar v' t' = SVar (Binding v' t') . Just
  aug (SApply s e) =
    do t <- typing s
    where
      findCastOp :: QTy -> Transform String
      findCastOp TNor = 
  aug s = return [s]

instance Codegen Exp where
  -- note: the type checking of `Exp` is caller's responsibility
  -- probably I need some nice type to enforce this
  aug e@(EOp2 op2 e1 e2) =
    do return $
         case op2 of
           ONor -> [ EEmit $ EMakeSeq TNat e1 (ELambda wild e2)
                   ] -- todo : create the sequence/whatever for phase
           _    -> [e] 
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
