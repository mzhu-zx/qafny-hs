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
import           Qafny.Env

-- Utils
import           Control.Lens                   (at, (%~), (?~), (^.))
import           Control.Monad                  (forM, unless, when)
import           Data.Functor                   ((<&>))
import qualified Data.List                      as List
import qualified Data.Map.Strict                as Map
import qualified Data.Set                       as Set
import           Debug.Trace                    (traceM, traceStack)
import           GHC.Stack                      (HasCallStack)
import           Qafny.Error                    (QError (..))
import           Qafny.Interval                 (Lattice (..))
import           Qafny.IntervalUtils            (rangeToNInt)
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
     , Has (Reader TEnv) sig m
     , Has (Error String) sig m
     , HasCallStack
     )
  => Exp -> m Ty
typingExp (ENum _)  = return TNat
typingExp (EVar x)  = do
  env <- view kEnv
  return (env ^. at x) `rethrowMaybe` (show $ UnknownVariableError x env)
typingExp (EOp2 op2 e1 e2) =
  do let top = typingOp2 op2
     t1 <- typingExp e1
     t2 <- typingExp e2
     checkSubtype2 top t1 t2
-- typing e = throwError $ "Typing for "  ++ show e ++ " is unimplemented!"


-- | Compute the quantum type of a given (possibly incomplete) partition
--
-- For example, a partition `s = { x [0..1], y [0..1]}` can be treated as the
-- composition of `s1 ⊠ s2 = s`. Therefore, when dereferencing `s1`, it should
-- resolve and give me `s` instead of `s1` as the partition itself is inseparable!
--
-- Examine each Range in a given Partition and resolve to a STuple
resolvePartition
  :: ( Has (State TState) sig m
     , Has (Error String) sig m
     )
  => Partition -> m STuple
resolvePartition se@(Partition rs) = do
  locs <- forM rs $ \r@(Range name _ _) -> do
    rlocs <- use (xSt . at name) `rethrowMaybe` (show . UnknownRangeError) r
    return [ loc |  (r', loc) <- rlocs, rangeToNInt r ⊑ rangeToNInt r' ]
  case List.nub . concat $ locs of
    [] -> throwError "Internal Error? An empty partition has no type!"
    [x] -> (use (sSt . at x) `rethrowMaybe` (show . UnknownLocError) x)
      <&> STuple . uncurry (x,,)
    ss ->
      throwError @String $ printf "`%s` is not a sub-partition, counterexample: %s"
        (show se) (show ss)

resolvePartitions
  :: ( Has (State TState) sig m
     , Has (Error String) sig m
     )
  => [Partition] -> m STuple
resolvePartitions =
  resolvePartition . Partition . concatMap unpackPartition

--------------------------------------------------------------------------------
-- | Split Typing 
--------------------------------------------------------------------------------
-- | Given a fully resolved partition and a potentially sub-range of it,
-- return a partition scheme if it's indeed a sub-range. 
--  
-- Otherwise (e.g. the partition is exact or there's no partition scheme
-- available), return `Nothing` to hint the caller to use the full partition.
splitScheme
  :: ( Has (Error String) sig m
     , Has (Error String) sig n
     )
  => STuple
  -> Range
  -> m (Maybe (n STuple))
splitScheme s@(STuple (loc, p, qt)) rx@(Range x _ _) = do
  let intX = rangeToNInt rx
  if isBot intX
    then return Nothing
    else undefined  
  where
    matched = [ intX ⊓ rangeToNInt ry
              | ry@(Range y _ _) <- unpackPartition p
              , x == y
              , intX ⊑ rangeToNInt ry ]
--------------------------------------------------------------------------------
-- | Aux Typing 
--------------------------------------------------------------------------------

-- | Type of the emitted value corresponding to its original quantum type.
typingQEmit :: QTy -> Ty
typingQEmit TNor = TSeq TNat
typingQEmit THad = TSeq TNat
typingQEmit TCH  = TSeq TNat
typingQEmit TCH01  = TSeq (TSeq TNat)
{-# INLINE typingQEmit #-}

-- | Types of binary operators
typingOp2 :: Op2 -> (Ty, Ty, Ty)
typingOp2 OAnd = (TBool, TBool, TBool)
typingOp2 OOr  = (TBool, TBool, TBool)
  -- We might need to solve the issue of nat vs int 0
typingOp2 OAdd = (TNat, TNat, TNat)
typingOp2 OMod = (TNat, TNat, TNat)
typingOp2 OMul = (TNat, TNat, TNat)
typingOp2 OLt  = (TNat, TNat, TBool)
typingOp2 OLe  = (TNat, TNat, TBool)
typingOp2 _    = undefined

typingGuard
  :: ( Has (State TState) sig m
     , Has (Error String) sig m
     )
  => Exp -> m STuple
typingGuard (EPartition s') = resolvePartition s'
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
subQ THad TCH01 = True
subQ TNor TCH01 = True
subQ TNor TNor = True
subQ _     _   = False

checkSubtypeQ
  :: Has (Error String) sig m
  => QTy -> QTy -> m ()
checkSubtypeQ t1 t2 =
  unless (subQ t1 t2) $
  traceStack "" . throwError $
  "Type mismatch: `" ++ show t1 ++ "` is not a subtype of `" ++ show t2 ++ "`"


--------------------------------------------------------------------------------
-- | Type Manipulation
--------------------------------------------------------------------------------


retypePartition1
  :: ( Has (Error String) sig m
     , Has (State TState) sig m
     , Has (Gensym Binding) sig m
     )
  => STuple -> QTy -> m (Var, Ty, Var, Ty)
retypePartition1 st qtNow = do
  (vsPrev, tPrev, vsNow, tNow) <- retypePartition st qtNow
  case (vsPrev, vsNow) of
    ([vPrev], [vNow]) ->
      return (vPrev, tPrev, vNow, tNow)
    _ ->
      throwError @String $ printf "%s and %s contains more than 1 partition!"
        (show vsPrev) (show vsNow)

-- | Cast the type of a partition to a given qtype, modify the typing state and
-- emit variable.
--
-- However, retyping doesn't generate a new meta variable
retypePartition
  :: ( Has (Error String) sig m
     , Has (State TState) sig m
     , Has (Gensym Binding) sig m
     )
  => STuple -> QTy -> m ([Var], Ty, [Var], Ty)
retypePartition st qtNow = do
  let STuple(locS, sResolved, qtPrev) = st
  when (qtNow == qtPrev) $
    throwError @String  $ printf
     "Partition `%s` is of type `%s`. No retyping need to be done."
     (show sResolved) (show qtNow)
  -- Get info based on its previous type!
  let vsPartition = varFromPartition sResolved
  let tOldEmit = typingQEmit qtPrev
  let bdsOld = [ Binding v tOldEmit | v <- vsPartition ]
  vsOldEmit <- bdsOld `forM` findEmitSym
  removeEmitBindings bdsOld
  let tNewEmit = typingQEmit qtNow
  sSt %= (at locS ?~ (sResolved, qtNow))
  vsNewEmit <- vsPartition `forM` (gensymEmit . (`Binding` tOldEmit))
  return (vsOldEmit, tOldEmit, vsNewEmit, tNewEmit)


-- Merge two given partition tuples if both of them are of CH type.
mergeSTuples
  :: ( Has (State TState) sig m
     , Has (Error String) sig m
     )
  => STuple -> STuple -> m ()
mergeSTuples
  stM@(STuple (locMain, sMain@(Partition rsMain), qtMain))
  stA@(STuple (locAux, sAux@(Partition rsAux), qtAux)) =
  do
    -- Sanity Check
    unless (qtMain == qtAux && qtAux == TCH) $
      traceStack "" $
      throwError @String $ printf "%s and %s have different Q types!"
        (show stM) (show stA)
    -- start merge
    let newPartition = Partition $ rsMain ++ rsAux
    -- let vsMetaAux =  varFromPartition sAux
    -- let newAuxLocs = Map.fromList $ [(v, locMain) | v <- vsMetaAux]
    -- xSt %= Map.union newAuxLocs -- use Main's loc for aux
    xSt %= Map.map
      (\rLoc -> [ (r, loc')
                | (r, loc) <- rLoc,
                  let loc' = if loc == locAux then locMain else loc])
    sSt %=
      (`Map.withoutKeys` Set.singleton locAux) . -- GC aux's loc
      (at locMain ?~ (newPartition, TCH))          -- update main's state
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
