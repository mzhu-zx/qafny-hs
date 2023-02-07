{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}

module Qafny.Codegen where

import           Qafny.AST
import           Control.Monad.RWS
import           Control.Monad.Except
import           Control.Lens.TH
import           Control.Lens
import           Data.Bifunctor
import qualified Data.Map.Strict as Map 
import Data.List (intercalate)


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
  show st = "  Kind State:\n    " ++
            (intercalate "\n    " . map show . Map.toList) (st ^. kSt) ++
            "\n  Session State:\n    " ++
            (intercalate "\n    " . map show . Map.toList) (st ^. sSt)

instance Show TEnv where
  show st = "  Kind Environment" ++
            (intercalate "\n    " . map show . Map.toList) (st ^. kEnv)

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
           es <- aug e 
           t' <- aug t
           let b = length t' == length es
           when b $ throwError "augmented type and expressions are of differnt type"
           vs <- throwError "I need a way to generate free variables here"
           let g = doSubtype t te -- (zipWith es t')
           undefined
  aug s = return [s]

instance Codegen Exp where
  aug (EOp2 op2 e1 e2) =
    do top <- typing op2
       t1 <- typing e1
       t2 <- typing e2
       (tr, a) <- doSubtype2 top t1 t2 (throwError "sthhere")
       return [e1]
  aug e = return [e]

instance Codegen Ty where
  aug (TQ TNor) = return [TSeq TNat] -- TODO complete the phase type here
  aug e = return [e]

-- | Helpers 

only1 :: Show a => Transform [a] -> Transform a
only1 = (=<<) $
  \case [x] -> return x
        e   -> throwError $ "[only1]: " ++ show e ++ "is not a singleton"

doSubtype :: Ty -> Ty -> Transform a -> Transform a
doSubtype t1 t2 m =
  if sub t1 t2
  then m
  else throwError $
       "Type mismatch: `" ++ show t1 ++
       "` is not a subtype of `" ++ show t2 ++ "`"

doSubtype2 :: (Ty, Ty, Ty) -> Ty -> Ty -> Transform a -> Transform (Ty, a)
doSubtype2 (top1, top2, tret) t1 t2 m =
  doSubtype top1 t1 $
  doSubtype top2 t2 $
  fmap (tret ,) m

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

sub :: Ty -> Ty -> Bool
sub = (==)

class Typing a t where
  typing :: a -> Transform t

instance Typing Exp Ty where
  typing (ENum _)  = return TNat
  typing (EVar x)  =
    do k <- asks (view $ kEnv . at x)
       maybe (unknownVariableError x) return k 
  typing e = throwError $ "Typing for "  ++ show e ++ " is unimplemented!"

instance Typing Op2 (Ty, Ty, Ty) where
  typing OAnd = return (TBool, TBool, TBool)
  typing OOr = return (TBool, TBool, TBool)
  -- We might need to solve the issue of nat vs int 
  typing OAdd = return (TNat, TNat, TNat) 
  typing OMod = return (TNat, TNat, TNat) 
  typing OMul = return (TNat, TNat, TNat)
  typing ONor = return (TNat, TNat, TQ TNor)
  
--------------------------------------------------------------------------------
-- Error Reporting
--------------------------------------------------------------------------------
unknownVariableError :: String -> Transform a
unknownVariableError s = throwError $ "Variable `" ++ s ++ "` is not in the environemnt"


--------------------------------------------------------------------------------
-- Wrapper
--------------------------------------------------------------------------------
runTransform :: Transform a -> (Either String a, TState, ())
runTransform = fuseError . (\x -> runRWS x initTEnv initTState) . runExceptT
  where
    fuseError :: (Either String a, TState, ()) -> (Either String a, TState, ())
    fuseError comp = _1 %~ first (++ "\ESC[0m\nCodegen terminted with an error!\n" ++ show st) $ comp
      where st = comp ^. _2

codegen :: AST -> (Either String AST, TState, ())
codegen = (_1 %~ fmap concat) . runTransform . aug
