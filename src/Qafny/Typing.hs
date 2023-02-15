{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}

module Qafny.Typing where

import           Qafny.AST
import           Qafny.Transform
import           Control.Lens
import           Control.Monad.RWS
import           Control.Monad.Except
import qualified Data.Map.Strict as Map 

--------------------------------------------------------------------------------
-- | Helpers 
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

sub :: Ty -> Ty -> Bool
sub = (==)

checkSubtype :: Ty -> Ty -> Transform ()
checkSubtype t1 t2 =
  unless (sub t1 t2) $
  throwError $
  "Type mismatch: `" ++ show t1 ++ "` is not a subtype of `" ++ show t2 ++ "`"
     

checkSubtype2 :: (Ty, Ty, Ty) -> Ty -> Ty -> Transform Ty
checkSubtype2 (top1, top2, tret) t1 t2 =
  do checkSubtype top1 t1
     checkSubtype top2 t2
     return tret


--------------------------------------------------------------------------------
-- | Typing 
--------------------------------------------------------------------------------
class Typing a t where
  typing :: a -> Transform t

instance Typing Session QTy where
  typing s =
    do t <- use (sSt . at s)
       maybe (unknownSessionError s) return t
       
instance Typing Exp Ty where
  typing (ENum _)  = return TNat
  typing (EVar x)  =
    do k <- use (kSt . at x)
       maybe (unknownVariableError x) return k 
  typing (EOp2 op2 e1 e2) =
    do top <- typing op2
       t1 <- typing e1
       t2 <- typing e2
       checkSubtype2 top t1 t2 
  typing e = throwError $ "Typing for "  ++ show e ++ " is unimplemented!"

instance Typing Op2 (Ty, Ty, Ty) where
  typing OAnd = return (TBool, TBool, TBool)
  typing OOr = return (TBool, TBool, TBool)
  -- We might need to solve the issue of nat vs int 0
  typing OAdd = return (TNat, TNat, TNat) 
  typing OMod = return (TNat, TNat, TNat) 
  typing OMul = return (TNat, TNat, TNat)
  typing ONor = return (TNat, TNat, TQ TNor)
  

instance Typing QTy [Ty] where
  typing TNor = return [TSeq TNat]
  typing THad = return [TSeq TNat]
  typing TCH  = return [TSeq TNat]
