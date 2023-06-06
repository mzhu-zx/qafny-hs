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
import           Control.Lens                   (at, (%~))
import           Control.Monad                  (unless, when)
import qualified Data.List                      as List
import qualified Data.Map.Strict                as Map
import           Qafny.Error                    (QError (..))
import           Qafny.Utils                    (rethrowMaybe, findEmitSym)
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
     )
  => Session -> m QTy
typingSession se@(Session s) =
  snd <$> resolveSession se 


-- | Examine each Range in a given Session and
resolveSession
  :: ( Has (State TState) sig m
     , Has (Error String) sig m
     )
     => Session -> m (Session, QTy)
resolveSession se@(Session rs) =
    do
      locs <-
        (`mapM` rs)
          ( \r@(Range name _ _) ->
              use (xSt . at name) `rethrowMaybe` (show . UnknownRangeError) r
          )
      case List.nub locs of
        [] -> throwError "Internal Error? An empty session has no type!"
        [x] -> use (sSt . at x) `rethrowMaybe` (show . UnknownLocError) x
        ss ->
          throwError @String $ printf "`%s` is not a sub-session, counterexample: %s"
            (show se) (show ss)

typingQEmit :: QTy -> Ty
typingQEmit TNor = TSeq TNat
typingQEmit THad = TSeq TNat
typingQEmit TCH  = TSeq TNat


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


-- | Cast the type of a session to another, modify the typing state and generate
-- new emission variable. 
-- 
-- However, retyping doesn't generate a new meta variable
retypeSession
  :: ( Has (Error String) sig m
     , Has (State TState) sig m
     , Has (Gensym Binding) sig m
     )
  => Session -> QTy -> m (Var, Ty, Var, Ty)
retypeSession s qtNow = do
    (locS, qtPrev) <- resolveSession s
    when (qtNow == qtPrev) $
      throwError @String  $ printf
       "Session `%s` is of type `%s`. No retyping need to be done."
       (show s) (show qtNow)
    -- Get info based on its previous type!
    tOldEmit <- typingQEmit qtPrev
    vOldEmits <- findEmitSym (Binding ())
    undefined
    -- let vMetas = varFromSession s
    -- tOldEmit <- only1 $ typing qtPrev
    -- vOldEmits <- mapM (`findSym` tOldEmit) vMetas
    -- -- update states
    -- -- update with new ones
    -- sSt %= (at s ?~ qtNow)
    -- -- update the kind state for each (probably not necessary)
    -- foldM_ (\_ v -> kSt %= (at v ?~ TQ qtNow)) () vMetas
    -- rbSt %= (`Map.withoutKeys` (Set.fromList $ map (,tOldEmit) vMetas))
    -- tNewEmit <- only1 $ typing qtNow
    -- vNewEmits <- mapM (`gensym` tNewEmit) vMetas
    -- return (vOldEmits, tOldEmit, vNewEmits, tOldEmit)

  -- do
  --   qtPrev <- typing s
  --   when (qtNow == qtPrev) $
  --     throwError $
  --       "Session `" ++ show s ++ "` is of type `" ++ show qtNow ++ "`. No retyping can be done."
  --   let vMetas = varFromSession s
  --   tOldEmit <- only1 $ typing qtPrev
  --   vOldEmits <- mapM (`findSym` tOldEmit) vMetas
  --   -- update states
  --   -- update with new ones
  --   sSt %= (at s ?~ qtNow)
  --   -- update the kind state for each (probably not necessary)
  --   foldM_ (\_ v -> kSt %= (at v ?~ TQ qtNow)) () vMetas
  --   rbSt %= (`Map.withoutKeys` (Set.fromList $ map (,tOldEmit) vMetas))
  --   tNewEmit <- only1 $ typing qtNow
  --   vNewEmits <- mapM (`gensym` tNewEmit) vMetas
  --   return (vOldEmits, tOldEmit, vNewEmits, tOldEmit)

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

