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

collectMethodTypesM :: AST -> Map.Map Var Ty
collectMethodTypesM = Map.fromList . collectMethodTypes

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
-- | Range SMT 
--------------------------------------------------------------------------------
-- we first have a simple decision procedure
-- assume that the subrange function takes in a triple of list of predicates
-- Bound = Num | Var + Num 
-- each list in the triple is a list of (Bound,Bound)
-- the first means Bound = Bound, second means Bound <= Bound and the third means Bound < Bound
-- we first have a function to check the validity of the predicates

-- checkValid p = checks the validity of p. Output is either p is valid/not-valid or None (meaning that no enough info).
-- algorithm : for p = (l1,l2,l3), we first use l1 to generate substitutions, and then substitute l2 and l3. 
-- then, for each variable x, we check its circlarity in l2 to see if there is an bound x + n <= x + m,
-- if so, we can check n <= m, otherwise, the formula is not valid.
-- for l3 we check if x + n < x + m. 

-- genP : for an exp, based on predicate p, we gen predicates to make the exp + p is valid.
-- the exp can be x + n < y, x + n = y, and x + n <= y, where x and y are C vars, and n is an int.
-- for any exp, we can gen a bound pair, and check if p has the bound pair already, 
-- if so, not need to add to p, otherwise, the result is add the new bound pair with p.

-- the following is to cut a range into two ranges in a for-loop.
-- observation1: only for-loop requires a range cut (or user-defined range-cut-op, but let's workout for-loop first).
-- observation2: only three types of quantum-bools are allowed: x[i], u = v @ x[i], u < v @ x[i]
-- in the first kind, x is Q, i is C; second/third kind: u is Q and it is a range u[0,n) (n could be C), x is Q, v is C, i is C.
-- x and u must be variable only. while i could be bounds, and v could be C-kind exp, 
-- observation3: in all these three kinds, the range cut only applies on x[i] part, and it has no relation with u = v or u < v part.
-- for u part, we require that the u[0,n) the range stored in tenv must appear in the input session.
-- for example, if a session is {u[0,s),x[0,m)}, then s must equal to n. let's say that they are syntactic equal now.
-- so function rangeCut x[i], [a,b), (y[c,d)) finds i places in [c,d), where i is given in the range [a,b),
-- x and y are two Q var and i,a,b,c,d are bounds. qnum(x) = m, qnum(y) = s
-- the output is a Maybe, None --> cut is not valid. Just ([c,i),[i,d), p), 
-- where p is a new predicate set including the predicates to make the cut to be true.
-- [c,i),[i,d) is the two range cut results, and it is always [c,i), and [i,d)
-- first, x must equal to y. this is a check, if not, then None, meaning that the rangeCut is no meaning.
-- then 0 <= c <= a < b <= d is the predicates we need to generate. We do not allow the case when b > d.
-- Another predicate is that a <= i < b, which should be included in the input predicates.

-- We now deal with stmt "if x[i] (or u = v @ x[i], u < v @ x[i]) then e", we do not need to cut ranges, but to validRange
-- In a session having x, we know that x[c,d) is in the session, let's say that x has [0,n) in tenv.
-- First, notice that in e, it must not have any mention of i. this can be a type check. 
-- Second, i must be in [c,d) range. In this case, c might be arbitary bounds,
-- but we can generate predicate 0 <= c <= i < d < n
-- we can also allow users to set up increasing and decreasing flags.
-- increasing means that in e, any mention of x[j], j must be greater than i
-- decreasing means that in e, any mention of x[j], j must be less than i
-- if these two are set, then the range x[c,d) can then change, 
-- for increasing, other than the predicate 0 <= c <= i < d < n, we also have x[i+1,d) range inside e,
-- and once the if is finished, x[i,d) is recovered to x[c,d)
-- for increasing, other than the predicate 0 <= c <= i < d < n, we also have x[c,i) range inside e,
-- and once the if is finished, x[c,i) is recovered to x[c,d)

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
  typing OLt  = return (TNat, TNat, TBool)
  typing OLe  = return (TNat, TNat, TBool)


instance Typing QTy [Ty] where
  typing TNor = return [TSeq TNat]
  typing THad = return [TSeq TNat]
  typing TCH  = return [TSeq TNat]


-- | Gather sessions used in the guard
typingGuard :: Exp -> Transform (Session, QTy)
typingGuard (ESession s') = 
  do 
    s <- resolveSession s'
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
-- retyping doesn't emit a new session symbol 
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

-- | Assemble the session from a session from the guard and the upper and the
-- lower bound of the loop and emit a check
-- Precondition: Split has been performed at the subtyping stage so that it's
-- guaranteed that only one range can be in the session
-- Reason: (was from `augByGuardType`)
--   `sGuard` is likely to be in `x [i .. i + 1]` form,
--   there should be a around of resolution that resolves to the session
--   `x[l .. h]` and do the emission at that place 
loopSession :: Session -> Exp -> Exp -> Transform (Session, Exp)
loopSession (Session [Range r sl sh]) l h =
  return
    ( Session [Range r l h]
    , EEmit (EOpChained l [(OLe, sl), (OLt, sh), (OLe, h)])
    )
loopSession s _ _ =
  throwError $
    "Session `"
      ++ show s
      ++ "` contains more than 1 range, this should be resolved at the typing stage"
