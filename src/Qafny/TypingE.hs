{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, TypeApplications #-}

module Qafny.TypingE where

-- | Typing though Fused Effects

-- Effects
import           Control.Effect.Catch
import           Control.Effect.Error           (Error, throwError)
import           Control.Effect.Labelled
import           Control.Effect.Lens            (use)
import           Control.Effect.Reader
import qualified Control.Effect.Reader.Labelled as L
import           Control.Effect.State           (State)
import           Effect.Gensym                  (Gensym)

-- Qafny
import           Qafny.AST
import           Qafny.Transform

-- Utils
import           Control.Lens                   (at)
import           Control.Monad                  (unless)
import qualified Data.List                      as List
import qualified Data.Map.Strict                as Map
import qualified Data.Set                       as Set
import           Qafny.Error                    (QError (..))
import qualified Qafny.Utils
import           Text.Printf                    (printf)

catchMaybe
  :: Has (Error String) sig m
  => m (Maybe a)
  -> m a
  -> m a
catchMaybe = Qafny.Utils.catchMaybe @String

-- | Compute the type of the given expression
typingExp
  :: ( Has (State TState) sig m
     , Has (Error String) sig m
     )
  => Exp -> m Ty
typingExp (ENum _)  = return TNat
typingExp (EVar x)  =
  use (kSt . at x) `catchMaybe` (throwError . show . UnknownVariableError) x
typingExp (EOp2 op2 e1 e2) =
  do let top = typingOp2 op2
     t1 <- typingExp e1
     t2 <- typingExp e2
     checkSubtype2 top t1 t2
-- typing e = throwError $ "Typing for "  ++ show e ++ " is unimplemented!"


typingOp2 :: Op2 -> (Ty, Ty, Ty)
typingOp2 OAnd = (TBool, TBool, TBool)
typingOp2 OOr  = (TBool, TBool, TBool)
  -- We might need to solve the issue of nat vs int 0
typingOp2 OAdd = (TNat, TNat, TNat)
typingOp2 OMod = (TNat, TNat, TNat)
typingOp2 OMul = (TNat, TNat, TNat)
typingOp2 ONor = (TNat, TNat, TQ TNor)
typingOp2 OLt  = (TNat, TNat, TBool)
typingOp2 OLe  = (TNat, TNat, TBool)

checkSubtype
  :: Has (Error String) sig m
  => Ty -> Ty -> m ()
checkSubtype t1 t2 =
  unless (sub t1 t2)
    (throwError @String $
      printf "Type mismatch: `%s` is not a subtype of `%s`"
      (show t1)
      (show t2))

checkSubtype2
  :: Has (Error String) sig m
  => (Ty, Ty, Ty) -> Ty -> Ty -> m Ty
checkSubtype2 (top1, top2, tret) t1 t2 =
  do checkSubtype top1 t1
     checkSubtype top2 t2
     return tret


sub :: Ty -> Ty -> Bool
sub = (==)
