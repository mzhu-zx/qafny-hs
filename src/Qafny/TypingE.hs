{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses, TupleSections,
             TypeApplications #-}

module Qafny.TypingE where

-- | Typing though Fused Effects

-- Effects
import           Control.Effect.Catch
import           Control.Effect.Error           (Error, throwError)
import           Control.Effect.Labelled
import           Control.Effect.Lens
import           Control.Effect.Reader
import qualified Control.Effect.Reader.Labelled as L
import           Control.Effect.State           (State)
import           Effect.Gensym                  (Gensym)

-- Qafny
import           Qafny.AST
import           Qafny.Transform

-- Utils
import           Control.Lens                   (_2, _3, at, (%~), (?~), (^.))
import           Control.Monad                  (forM, unless, when)
import           Data.Functor                   ((<&>))
import qualified Data.List                      as List
import qualified Data.Map.Strict                as Map
import qualified Data.Set                       as Set
import           Effect.Cache                   (Cache, drawDefault)
import           Qafny.Error                    (QError (..))
import           Qafny.Utils
    ( findEmitSym
    , gensymEmit
    , removeEmitBindings
    , rethrowMaybe
    )
import           Text.Printf                    (printf)





-- | Compute the type of the given expression
typingExp
  :: ( Has (State TState) sig m
     , Has (Error String) sig m
     )
  => Exp -> m Ty
typingExp (ENum _)  = return TNat
typingExp (EVar x)  =
  use (kSt . at x) `rethrowMaybe` (show . UnknownVariableError) x
typingExp (EOp2 op2 e1 e2) =
  do let top = typingOp2 op2
     t1 <- typingExp e1
     t2 <- typingExp e2
     checkSubtype2 top t1 t2
-- typing e = throwError $ "Typing for "  ++ show e ++ " is unimplemented!"

-- | Compute the quantum type of a given (possibly incomplete) session
--
-- For example, a session `s = { x [0..1], y [0..1]}` can be treated as the
-- composition of `s1 ⊠ s2 = s`. Therefore, when dereferencing `s1`, it should
-- resolve and give me `s` instead of `s1` as the session itself is inseparable!
--
typingSession
  :: ( Has (State TState) sig m
     , Has (Error String) sig m
     , Has (Cache STuple) sig m -- Session info
     )
  => Session -> m QTy
typingSession se@(Session s) = do
  tup <- drawDefault $ resolveSession se
  return $ tup ^. _3

-- | Examine each Range in a given Session and resolve to a STuple
resolveSession
  :: ( Has (State TState) sig m
     , Has (Error String) sig m
     )
  => Session -> m STuple
resolveSession se@(Session rs) = do
  locs <- forM rs $ \r@(Range name _ _) ->
    use (xSt . at name) `rethrowMaybe` (show . UnknownRangeError) r
  case List.nub locs of
    [] -> throwError "Internal Error? An empty session has no type!"
    [x] -> (use (sSt . at x) `rethrowMaybe` (show . UnknownLocError) x)
      <&> uncurry (x,,)
    ss ->
      throwError @String $ printf "`%s` is not a sub-session, counterexample: %s"
        (show se) (show ss)

resolveSessions
  :: ( Has (State TState) sig m
     , Has (Error String) sig m
     )
  => [Session] -> m STuple
resolveSessions =
  resolveSession . Session . concatMap unpackSession

-- | Type of the emitted value corresponding to its original quantum type.
typingQEmit :: QTy -> Ty
typingQEmit TNor = TSeq TNat
typingQEmit THad = TSeq TNat
typingQEmit TCH  = TSeq TNat
{-# INLINE typingQEmit #-}

-- | Types of binary operators
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

typingGuard
  :: ( Has (State TState) sig m
     , Has (Error String) sig m
     )
  => Exp -> m STuple
typingGuard (ESession s') = resolveSession s'
typingGuard e             = throwError $ "Unsupported guard: " ++ show e


--------------------------------------------------------------------------------
-- | Subtyping
--------------------------------------------------------------------------------
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


--------------------------------------------------------------------------------
-- | QSubtyping
--------------------------------------------------------------------------------
subQ :: QTy -> QTy -> Bool
subQ _    TCH  = True
subQ THad THad = True
subQ TNor TNor = True
subQ _     _   = False

checkSubtypeQ
  :: Has (Error String) sig m
  => QTy -> QTy -> m ()
checkSubtypeQ t1 t2 =
  unless (subQ t1 t2) $
  throwError $
  "Type mismatch: `" ++ show t1 ++ "` is not a subtype of `" ++ show t2 ++ "`"


--------------------------------------------------------------------------------
-- | Type Manipulation
--------------------------------------------------------------------------------


retypeSession1
  :: ( Has (Error String) sig m
     , Has (State TState) sig m
     , Has (Gensym Binding) sig m
     , Has (Cache STuple) sig m
     )
  => Session -> QTy -> m (Var, Ty, Var, Ty)
retypeSession1 s' qtNow = do
  (vsPrev, tPrev, vsNow, tNow) <- retypeSession s' qtNow
  case (vsPrev, vsNow) of
    ([vPrev], [vNow]) ->
      return (vPrev, tPrev, vNow, tNow)
    _ ->
      throwError @String $ printf "%s and %s contains more than 1 session!"
        (show vsPrev) (show vsNow)

-- | Cast the type of a session to a given qtype, modify the typing state and
-- emit variable.
--
-- However, retyping doesn't generate a new meta variable
retypeSession
  :: ( Has (Error String) sig m
     , Has (State TState) sig m
     , Has (Gensym Binding) sig m
     , Has (Cache STuple) sig m
     )
  => Session -> QTy -> m ([Var], Ty, [Var], Ty)
retypeSession s' qtNow = do
  (locS, sResolved, qtPrev) <- drawDefault $ resolveSession s'
  when (qtNow == qtPrev) $
    throwError @String  $ printf
     "Session `%s` is of type `%s`. No retyping need to be done."
     (show sResolved) (show qtNow)
  -- Get info based on its previous type!
  let vsSession = varFromSession sResolved
  let tOldEmit = typingQEmit qtPrev
  let bdsOld = [ Binding v tOldEmit | v <- vsSession ]
  vsOldEmit <- bdsOld `forM` findEmitSym
  removeEmitBindings bdsOld
  let tNewEmit = typingQEmit qtNow
  sSt %= (at locS ?~ (sResolved, qtNow))
  vsNewEmit <- vsSession `forM` (gensymEmit . (`Binding` tOldEmit))
  return (vsOldEmit, tOldEmit, vsNewEmit, tNewEmit)


-- Merge two given session tuples if both of them are of CH type.
mergeSTuples
  :: ( Has (State TState) sig m
     , Has (Error String) sig m
     )
  => STuple -> STuple -> m ()
mergeSTuples
  stM@(locMain, sMain@(Session rsMain), qtMain)
  stA@(locAux, sAux@(Session rsAux), qtAux) =
  do
    -- Sanity Check
    unless (qtMain == qtAux && qtAux == TCH) $
      throwError @String $ printf "%s and %s have different Q types!"
        (show stM) (show stA)
    -- start merge
    let newSession = Session $ rsMain ++ rsAux
    let vsMetaAux =  varFromSession sAux
    let newAuxLocs = Map.fromList $ [(v, locMain) | v <- vsMetaAux]
    xSt %= Map.union newAuxLocs -- use Main's loc for aux
    sSt %=
      (`Map.withoutKeys` Set.singleton locAux) . -- GC aux's loc
      (at locMain ?~ (newSession, TCH))          -- update main's state
    return ()

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

