module Qafny.Direct where

{- Experiment: Type-directed Compilation
   - Pass 1. Typing: traverse the AST and produce type derivation at each step
   - Pass 2. Compilation: traverse the derivation to produce codegen
   - Fuse: traverse and produce derivation in postorder and call the compiler on
     each step  
-}

import           Qafny.AST
import           Qafny.Typing
import           Qafny.Transform
import           Data.Maybe (maybeToList)

data Derivation f
  = DIf f f f
  -- deriving Functor

inferStmt :: Stmt -> Transform ()
inferStmt (SIf e seps b) =
  inferGuardExp e 
inferStmt _ = undefined

inferGuardExp :: Exp -> Transform ()
inferGuardExp (ESession s) =
  inferSession s TCH
inferGuardExp _ = undefined

inferSession :: Session -> QTy -> Transform ()
inferSession s@(Session rs) qt = 
  do
    sCtx <- resolveSession s
    qtCtx <- getSessionType sCtx
    inferSub s qt sCtx qtCtx 
    return ()


-- | Compute the derivation from expected type to the current type 
-- Here are two level subtypings
-- 1. Subrange
-- 2. QTy Subtying
-- Subrange should be resolved first, followed by QTy, because splitting enables
-- potential QTy casts
inferSub :: Session -> QTy -> Session -> QTy -> Transform ()
inferSub (Session [r@(Range x l h)]) qt sCtx@(Session rsCtx) qtCtx =
  return ()
  where
    rsRelavent = [r'' | r' <- rsCtx
                      , r'' <- maybeToList $ subRange r' r ]
inferSub s qt sCtx qtCtx = undefined


