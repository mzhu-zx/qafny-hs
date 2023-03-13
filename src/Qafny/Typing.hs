{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TupleSections #-}

module Qafny.Typing where

import           Qafny.AST
import           Qafny.Transform
import           Control.Lens
import           Control.Monad.RWS
import           Control.Monad.Except
import qualified Data.Map.Strict as Map 
import qualified Data.Set as Set 
import qualified Data.List as List

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

-- TODO: make `sub` a typeclass?
subQ :: QTy -> QTy -> Bool
subQ _    TCH  = True
subQ THad THad = True
subQ TNor TNor = True
subQ _     _   = False
  
checkSubtype2 :: (Ty, Ty, Ty) -> Ty -> Ty -> Transform Ty
checkSubtype2 (top1, top2, tret) t1 t2 =
  do checkSubtype top1 t1
     checkSubtype top2 t2
     return tret

checkSubtypeQ :: QTy -> QTy -> Transform ()
checkSubtypeQ t1 t2 =
  unless (subQ t1 t2) $
  throwError $
  "Type mismatch: `" ++ show t1 ++ "` is not a subtype of `" ++ show t2 ++ "`"


--------------------------------------------------------------------------------
-- | Typing 
--------------------------------------------------------------------------------
class Typing a t where
  typing :: a -> Transform t

-- | resolve the typing of a coarse session
instance Typing Session QTy where
  typing se@(Session s) = resolveSession se >>= getSessionType

instance Typing Exp Ty where
  typing (ENum _)  = return TNat
  typing (EVar x)  =
    handleWith (unknownVariableError x) $ use (kSt . at x)
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


-- | Gather sessions used in the guard
typingGuard :: Exp -> Transform (Session, QTy)
typingGuard (ESession s) = 
  handleWith (unknownSessionError s) (uses (sSt . at s) ((s, ) <$>))
typingGuard e = throwError $ "Unsupported guard: " ++ show e

-- | Find the type of the emitted term
typingEmit :: Session -> Transform [Ty]
typingEmit s = (typing s :: Transform QTy) >>= typing

-- | Find the emitted symbol by the range name and quantum type
-- TODO: this should probably be refactored to return a list of symbols
findSymByRangeQTy :: Range -> QTy -> Transform Var
findSymByRangeQTy (Range v _ _) qt = only1 (typing qt) >>= findSym v

-- | Dealloc an orphan variable
deallocOrphan :: Var -> Ty -> Transform ()
deallocOrphan vMeta tyEmit =
  rbSt %= (`Map.withoutKeys` Set.singleton (vMeta, tyEmit))
    

-- | Change the type of a session and returns something
retypeSession :: Session -> QTy -> Transform ([Var], Ty, [Var], Ty)
retypeSession s qtNow =
  do
    qtPrev <- typing s
    when (qtNow == qtPrev) $
      throwError $
        "Session `" ++ show s ++ "` is of type `" ++ show qtNow ++ "`. No retyping can be done."
    let vMetas = varFromSession s
    tOldEmit <- only1 $ typing qtPrev
    vOldEmits <- mapM (`findSym` tOldEmit) vMetas
    -- update states
    -- update with new ones
    sSt %= (at s ?~ qtNow)
    -- update the kind state for each (probably not necessary)
    foldM_ (\_ v -> kSt %= (at v ?~ TQ qtNow)) () vMetas
    rbSt %= (`Map.withoutKeys` (Set.fromList $ map (,tOldEmit) vMetas))
    tNewEmit <- only1 $ typing qtNow
    vNewEmits <- mapM (`gensym` tNewEmit) vMetas
    return (vOldEmits, tOldEmit, vNewEmits, tOldEmit)

retypeSession1 :: Session -> QTy -> Transform (Var, Ty, Var, Ty)
retypeSession1 s qtNow =
  do
    qtPrev <- typing s
    when (qtNow == qtPrev) $
      throwError $
        "Session `" ++ show s ++ "` is of type `" ++ show qtNow ++ "`. No retyping can be done."
    vMeta <- only1 $ return $ varFromSession s
    tOldEmit <- only1 $ typing qtPrev
    vOldEmit <- vMeta `findSym` tOldEmit
    -- update states
    -- update with new ones
    sSt %= (at s ?~ qtNow)
    -- update the kind state for each (probably not necessary)
    kSt %= (at vMeta ?~ TQ qtNow)
    rbSt %= (`Map.withoutKeys` Set.singleton (vMeta ,tOldEmit))
    tNewEmit <- only1 $ typing qtNow
    vNewEmit <- vMeta `gensym` tNewEmit
    return (vOldEmit, tOldEmit, vNewEmit, tOldEmit)

-- | Merge two sessions and update the typing state
mergeSessionType :: Session -> Session -> Transform ()
mergeSessionType sMain@(Session rsMain) sAux@(Session rsAux) =
  do
    qtMain <- handleWith (unknownSessionError sMain) $ use (sSt . at sMain)
    qtAux <- handleWith (unknownSessionError sAux) $ use (sSt . at sAux)
    unless (qtMain == qtAux && qtAux == TCH) $
      throwError $
        "Session `"
          ++ show sMain
          ++ "` and session `"
          ++ show sAux
          ++ "` are of type `"
          ++ show qtMain
          ++ "` and `"
          ++ show qtAux
          ++ "`, which are not CH."
    -- start merge
    let newSession = Session $ rsMain ++ rsAux
    let vMetasMain = varFromSession sMain 
    let vMetasAux =  varFromSession sAux
    let refNewMain = Map.fromList $ (, newSession) <$> vMetasMain 
    let refNewAux  = Map.fromList $ (, newSession) <$> vMetasAux 
    -- update range reference 
    xSt %= ((refNewMain `Map.union` refNewAux) `Map.union`)
    -- update session type state
    sSt %= (`Map.withoutKeys` Set.fromList [sMain, sAux])
    sSt %= (at newSession ?~ TCH)
    -- surprisingly, I don't need to change the rest
    -- TODO: what should I return to avoid computation?
    return ()


-- | Resolve session: compute the super session of one session
resolveSession :: Session -> Transform Session
resolveSession se@(Session rs) =
    do
      sesRange <-
        (`mapM` rs)
          ( \r@(Range name _ _) ->
              handleWith (unknownRangeError r) $ use (xSt . at name)
          )
      case List.nub sesRange of
        [] -> throwError "Internal Error? An empty session has no type!"
        [x] -> return x
        ss ->
          throwError $
            "`"
              ++ show se
              ++ "` is not a sub-session, counterexample: "
              ++ show ss

-- | Resolve session: compute the super session of several sessions
resolveSessions :: [Session] -> Transform Session
resolveSessions =
  resolveSession . Session . concatMap (\(Session rs) -> rs)

-- | Compute the quantum type of a session
getSessionType :: Session -> Transform QTy
getSessionType s =
  handleWith
    ( throwError $
        "Internal Error? Session`"
          ++ show s
          ++ "` is not in the type state"
    )
    $ use (sSt . at s)
