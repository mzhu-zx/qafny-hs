{-# LANGUAGE
    FlexibleContexts
  , FlexibleInstances
  , MultiParamTypeClasses
  , ScopedTypeVariables
  , TupleSections
  , TypeApplications
  #-}

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
import           Qafny.Error                    (QError (..))
import           Qafny.Interval
    ( Interval (Interval)
    , Lattice (..)
    , NatInterval
    )
import           Qafny.IntervalUtils            (rangeToNInt, γRange)
import           Qafny.TypeUtils
import           Qafny.Utils
    ( exp2AExp
    , findEmitRangeQTy
    , findEmitSym
    , gensymEmit
    , gensymEmitRangeQTy
    , gensymLoc
    , removeEmitBindings
    , removeEmitRangeQTys
    , rethrowMaybe
    )

-- Utils
import           Control.Lens                   (at, non, (%~), (?~), (^.))
import           Control.Monad                  (forM, unless, when)
import           Data.Functor                   ((<&>))
import           Data.IntMap                    (partition)
import qualified Data.List                      as List
import qualified Data.Map.Strict                as Map
import           Data.Maybe                     (listToMaybe, maybeToList)
import qualified Data.Set                       as Set
import           Debug.Trace                    (traceM, traceStack)
import           GHC.Stack                      (HasCallStack)
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
  do top <- typingOp2 op2
     t1 <- typingExp e1
     t2 <- typingExp e2
     checkSubtype2 top t1 t2
  where
    -- typingOp2 :: Op2 -> m (Ty, Ty, Ty)
    -- | Types of binary operators
    typingOp2 OAnd = return (TBool, TBool, TBool)
    typingOp2 OOr  = return (TBool, TBool, TBool)
    -- We might need to solve the issue of nat vs int 0
    typingOp2 OAdd = return (TNat, TNat, TNat)
    typingOp2 OMod = return (TNat, TNat, TNat)
    typingOp2 OMul = return (TNat, TNat, TNat)
    typingOp2 OLt  = return (TNat, TNat, TBool)
    typingOp2 OLe  = return (TNat, TNat, TBool)
    typingOp2 ONor = exp2AExp e1 >>= \ae -> return (TNat, TNat, TQReg ae)

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
  rsResolved <- rs `forM` resolveRange
  let locs = [ loc | (_, _, True, loc) <- concat rsResolved ]
  let related = printf "Related:%s" $
        concatMap (("\n\t" ++) . showRel) [ (r1, r2, b) | (r1, r2, b, _) <- concat rsResolved ]
  case List.nub locs of
    [] ->  throwError $ errInternal related
    [x] -> (use (sSt . at x) `rethrowMaybe` (show . UnknownLocError) x)
      <&> STuple . uncurry (x,,)
    ss -> throwError $ errNonunique ss related
  where
    errNonunique :: [Loc] -> String -> String
    errNonunique ss = printf
      ("Type Error: " ++
       "`%s` is not the sub-partition of a unique partition.\n" ++
       "Counterexample: %s\n%s")
        (show se) (show ss)
    errInternal :: String -> String
    errInternal = printf
      ("Type Error: " ++
       "The partition `%s` is not a sub-partition of any existing ones!\n%s")
      (show se)
    showRel :: (Range, Range, Bool) -> String
    showRel (r1, r2, True)  = printf "%s ⊑ %s" (show r1) (show r2)
    showRel (r1, r2, False) = printf "%s ⋢ %s" (show r1) (show r2)

resolveRange
  :: ( Has (State TState) sig m
     , Has (Error String) sig m
     )
  => Range -> m [(Range, Range, Bool, Loc)]
resolveRange r@(Range name _ _) = do
  rlocs <- use (xSt . at name) `rethrowMaybe` (show . UnknownRangeError) r
  return [ (r, r', rangeToNInt r ⊑ rangeToNInt r', loc) |  (r', loc) <- rlocs ]


resolvePartitions
  :: ( Has (State TState) sig m
     , Has (Error String) sig m
     )
  => [Partition] -> m STuple
resolvePartitions =
  resolvePartition . Partition . concatMap unpackPart

--------------------------------------------------------------------------------
-- | Split Typing
--------------------------------------------------------------------------------
-- | Given a partition and a range, compute a split scheme if the range is a
-- part of the partition. Return 'Nothing' if no split needs to be performed,

splitScheme
  :: ( Has (Error String) sig m
     , Has (Gensym String) sig m
     , Has (State TState) sig m
     )
  => STuple
  -> Range
  -> m (Maybe SplitScheme)
splitScheme s@(STuple (loc, p, qt)) rx@(Range x _ _) = do
  when (isBot intX) $ throwError errBotRx
  case matched of
    Nothing -> throwError errImproperRx
    Just (intL, _, intY, ry)  ->
      let rs = γ intL ++ γ intY -- the list of ranges to be broken
          rsMain = (rs ++) . List.delete ry $ unpackPart p
          rsAux  = [rx]
          pMain  = Partition rsMain
          pAux   = Partition rsAux
      in case rsMain of
        [] -> return Nothing -- no split actually needs to be done
        _  -> do             -- split actually happens here:
          locAux <- gensymLoc x
          let sMain' = (loc, pMain, qt)   -- the part that's splited _from_
          let sAux'  = (locAux, pAux, qt) -- the part that's splited _to_
          sSt %= (at loc ?~ (pMain, qt)) . (at locAux ?~ (pAux, qt))
          xRangeLocs <- use (xSt . at x) `rethrowMaybe` errXST
          let xrl =
                [ (rAux, locAux) | rAux <- rsAux ] ++ -- "new range -> new loc"
                [ (rMainNew, loc) | rMainNew <- rs ] ++ -- "broken ranges -> old loc"
                List.filter ((/= rx) . fst) xRangeLocs -- "the rest with the old range removed"
          xSt %= (at x ?~ xrl)
          return . Just $ SplitScheme
            { schROrigin = ry
            , schRTo = rx
            , schRsRem = rs
            , schQty = qt
            , schSMain = STuple sMain'
            , schSAux  = STuple sAux'
            }
  where
    errXST = printf "No range beginning with %s cannot be found in `xSt`" x
    errBotRx :: String = printf "The range %s contains no qubit!" $ show rx
    errImproperRx :: String = printf
      "The range %s is not a part of the partition %s!" (show rx) (show s)
    intX@(Interval xl xr) = rangeToNInt rx
    matched = listToMaybe -- logically, there should be at most one partition!
      [ (Interval yl xl, intX, Interval xr yr, ry)
      | ry@(Range y _ _) <- unpackPart p
      , x == y                -- must be in the same register file!
      , intX ⊑ rangeToNInt ry -- must be a sub-interval
      , let (Interval yl yr) = rangeToNInt ry
      ]
    γ :: NatInterval -> [Range]  = (maybeToList .: γRange) x


--------------------------------------------------------------------------------
-- | Aux Typing
--------------------------------------------------------------------------------

typingGuard
  :: ( Has (State TState) sig m
     , Has (Error String) sig m
     )
  => Exp -> m STuple
typingGuard (EPartition s') = resolvePartition s'
typingGuard e               = throwError $ "Unsupported guard: " ++ show e


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
subQ _    TCH   = True
subQ THad THad  = True
subQ THad TCH01 = True
subQ TNor TCH01 = True
subQ TNor TNor  = True
subQ _     _    = False

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
  let tOldEmit = typingQEmit qtPrev
  let rqsOld = (, qtPrev) <$> unpackPart sResolved
  vsOldEmit <- rqsOld `forM` uncurry findEmitRangeQTy
  removeEmitRangeQTys rqsOld
  let tNewEmit = typingQEmit qtNow
  sSt %= (at locS ?~ (sResolved, qtNow))
  vsNewEmit <- unpackPart sResolved `forM` (`gensymEmitRangeQTy` qtNow)
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
