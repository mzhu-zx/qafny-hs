{-# LANGUAGE
    FlexibleContexts
  , FlexibleInstances
  , LambdaCase
  , MultiParamTypeClasses
  , ScopedTypeVariables
  , TupleSections
  , TypeApplications
  #-}

module Qafny.Typing where

-- | Typing though Fused Effects

-- Effects
-- import           Control.Effect.Labelled
-- import qualified Control.Effect.Reader.Labelled as L
import qualified Control.Carrier.State.Strict as State
import           Control.Effect.Catch
import           Control.Effect.Error         (Error, throwError)
import           Control.Effect.Lens
import           Control.Effect.Reader
import           Control.Effect.State         (State)
import           Effect.Gensym                (Gensym)


-- Qafny
import           Qafny.AST
import           Qafny.Domain                 (NatInterval)
import           Qafny.Env
import           Qafny.Error                  (QError (..))
import           Qafny.Interval
import           Qafny.IntervalUtils          (rangeToNInt, γRange)
import           Qafny.TypeUtils
import           Qafny.Utils
    ( exp2AExp
    , findEmitRangeQTy
    , gensymEmitRangeQTy
    , gensymLoc
    , removeEmitRangeQTys
    , rethrowMaybe
    , throwError'
    )

-- Utils
import           Control.Effect.Trace
import           Control.Lens                 (at, (%~), (.~), (?~), (^.))
import           Control.Monad                (forM, forM_, unless, when)
import           Data.Bool                    (bool)
import           Data.Function                ((&))
import           Data.Functor                 ((<&>))
import qualified Data.List                    as List
import qualified Data.Map.Strict              as Map
import           Data.Maybe                   (listToMaybe, maybeToList)
import qualified Data.Set                     as Set
import           Data.Sum
import           GHC.Stack                    (HasCallStack)
import           Text.Printf                  (printf)

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
-- composition of `s1 ⊎ s2 = s`. Therefore, when dereferencing `s1`, it should
-- resolve and give me `s` instead of `s1` as the partition itself is
-- inseparable!
--
-- Examine each Range in a given Partition and resolve to a STuple
resolvePartition
  :: ( Has (State TState) sig m
     , Has (Error String) sig m
     , Has Trace sig m
     )
  => Partition -> m STuple
resolvePartition se@(Partition rs) = do
  rsResolved <- rs `forM` resolveRange
  let locs = [ loc | (_, _, Just True, loc) <- concat rsResolved ]
  let related = printf "Related:%s" $
        concatMap (("\n\t" ++) . showRel)
        [ (r1, r2, b) | (r1, r2, b, _) <- concat rsResolved ]
  trace $ "[resolvePartition] " ++ related
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
    showRel :: (Range, Range, Maybe Bool) -> String
    showRel (r1, r2, Just True)  = printf "%s ⊑ %s" (show r1) (show r2)
    showRel (r1, r2, Just False) = printf "%s ⋢ %s" (show r1) (show r2)
    showRel (r1, r2, Nothing)    = printf "%s ?⊑? %s" (show r1) (show r2)

-- | Query all ranges related to the given range.
resolveRange
  :: ( Has (State TState) sig m
     , Has (Error String) sig m
     )
  => Range -> m [(Range, Range, Maybe Bool, Loc)]
resolveRange r@(Range name _ _) = do
  rlocs <- use (xSt . at name) `rethrowMaybe` (show . UnknownRangeError) r
  return [ (r, r', r ⊑ r', loc) |  (r', loc) <- rlocs ]


resolvePartitions
  :: ( Has (State TState) sig m
     , Has (Error String) sig m
     , Has Trace sig m
     )
  => [Partition] -> m STuple
resolvePartitions =
  resolvePartition . Partition . concatMap unpackPart

--------------------------------------------------------------------------------
-- | Split Typing
--------------------------------------------------------------------------------
-- | Given a partition and a range, compute a split scheme if the range is a
-- part of the partition.
--
-- The returned 'STuple' is the partition covering the range
--
-- For the optional return value, return 'Nothing' if no split needs **on a specific
-- range** needs to be performed, i.e. no codegen needs to be done.
splitScheme
  :: ( Has (Error String) sig m
     , Has (Gensym String) sig m
     , Has (State TState) sig m
     , Has (Gensym RBinding) sig m
     , Has Trace sig m
     )
  => STuple
  -> Range
  -> m (STuple, Maybe SplitScheme)
splitScheme s r = do
  ans <- splitScheme' s r
  -- trace $ printf "[splitScheme]\n\tIn: %s %s\n\tOut: %s"
  --   (show s) (show r) (show ans)
  return ans

-- | Remove range if it is equivalent to the bottom
contractRange
  :: ( Has (Error String) sig m )
  => Range -> m [Range]
contractRange r =
  maybe err (return . bool [r] []) $ isBot r
  where
    err = throwError' $ printf "Cannot decide if %s is empty." (show r)

-- TODO1: Pass in an environment and perform substitution before doing value
-- checking
-- TODO2: Use 'NonDeterm' effects instead.
splitScheme'
  :: ( Has (Error String) sig m
     , Has (Gensym String) sig m
     , Has (State TState) sig m
     , Has (Gensym RBinding) sig m
     , Has Trace sig m
     )
  => STuple
  -> Range
  -> m (STuple, Maybe SplitScheme)
splitScheme' s@(STuple (loc, p, qt)) rSplitTo@(Range to rstL rstR) = do
  case isBot rSplitTo of
    Just True -> throwError errBotRx
    Nothing   -> throwError' $ printf "Cannot decide if %s is empty." (show rSplitTo)
    _         -> return ()
  -- trace infoSS
  case matched of
    Nothing -> throwError errImproperRx
    Just (rRemL, _, rRemR, rOrigin)  -> do
      rsRem <- (++) <$> contractRange rRemL <*> contractRange rRemR
      let rsRest = List.delete rOrigin $ unpackPart p
          -- the ranges except the chosen one + the quotient ranges
          rsMain = rsRem ++ rsRest
          rsAux  = [rSplitTo]
          pMain  = Partition rsMain
          pAux   = Partition rsAux
      case rsMain of
        [] -> return (s, Nothing) -- no split at all!
        _  -> do
          -- ^ Split in partition or in both partition and a range
          -- 1. Allocate partitions, break ranges and move them around
          locAux <- gensymLoc to
          let sMain' = (loc, pMain, qt)   -- the part that's splited _from_
          let sAux'  = (locAux, pAux, qt) -- the part that's splited _to_
          sSt %= (at loc ?~ (pMain, qt)) . (at locAux ?~ (pAux, qt))
          -- use sSt >>= \s' -> trace $ printf "sSt: %s" (show s')
          xRangeLocs <- use (xSt . at to) `rethrowMaybe` errXST
          let xrl =
                -- "new range -> new loc"
                [ (rAux, locAux) | rAux <- rsAux ] ++
                -- "split ranges -> old loc"
                [ (rMainNew, loc) | rMainNew <- rsRem ] ++
                -- "the rest with the old range removed"
                List.filter ((/= rOrigin) . fst) xRangeLocs
          -- trace (printf "State Filtered by %s: %s" (show rSplitTo) (show xrl))
          xSt %= (at to ?~ xrl)
          -- 2. Generate emit symbols for split ranges
          case rsRem of
            [] -> return (STuple sAux', Nothing) -- only split in partition but not in a range
            _  -> do
              (vEmitR, rSyms) <- case qt of
                t | t `elem` [ TNor, THad, TEN01 ] -> do
                  -- locate the original range
                  vEmitR <- findEmitRangeQTy rOrigin qt
                  -- delete it from the record
                  removeEmitRangeQTys [(rOrigin, qt)]
                  -- gensym for each split ranges
                  rSyms <- (rSplitTo : rsRem) `forM` (`gensymEmitRangeQTy` qt)
                  return (vEmitR, rSyms)
                _    -> throwError $ errUnsupprtedTy ++ "\n" ++ infoSS
              let ans = SplitScheme
                    { schROrigin = rOrigin
                    , schRTo = rSplitTo
                    , schRsRem = rsRem
                    , schQty = qt
                    , schSMain = STuple sMain'
                    , schVEmitOrigin = vEmitR
                    , schVsEmitAll = rSyms
                    }
              -- trace $ printf "[splitScheme (post)] %s" (show ans)
              return (STuple sAux', Just ans)
  where
    infoSS :: String = printf "[splitScheme] from (%s) to (%s)" (show s) (show rSplitTo)
    errUnsupprtedTy :: String
    errUnsupprtedTy = printf "Splitting a %s partition is unsupported." (show qt)
    errXST = printf "No range beginning with %s cannot be found in `xSt`" to
    errBotRx :: String
    errBotRx = printf "The range %s contains no qubit!" $ show rSplitTo
    errImproperRx :: String
    errImproperRx = printf
      "The range %s is not a part of the partition %s!" (show rSplitTo) (show s)
    matched = listToMaybe -- logically, there should be at most one partition!
      [ (Range y yl rstL, rSplitTo, Range y rstR yr, rRef)
      | rRef@(Range y yl yr) <- unpackPart p  -- choose a range in the environment
      , to == y                               -- must be in the same register file!
      , True <- maybeToList $ rSplitTo ⊑ rRef -- must be a sub-interval
      ]
    -- γ :: NatInterval -> [Range]  = (maybeToList .: γRange) to



-- | Compute, in order to split the given range from a resolved partition, which
-- range in the partition needs to be split as well as the resulting quotient
-- ranges.
getRangeSplits
  :: ( Has (Error String) sig m
     , Has Trace sig m
     )
  => STuple
  -> Range
  -> m (Range, [Range])
getRangeSplits s@(STuple (loc, p, qt)) rSplitTo@(Range to rstL rstR) = do
  case isBot rSplitTo of
    Just False -> throwError errBotRx
    Nothing    -> throwError' $ printf "Cannot decide if %s is empty." (show rSplitTo)
    _          -> return ()
  trace infoSS
  case matched of
    Nothing -> throwError errImproperRx
    Just (rRemL, _, rRemR, rOrigin)  -> do
      rsRem <- (++) <$> contractRange rRemL <*> contractRange rRemR
      return (rOrigin, rsRem)
  where
    infoSS :: String = printf "[checkScheme] from (%s) to (%s)" (show s) (show rSplitTo)
    errBotRx :: String
    errBotRx = printf "The range %s contains no qubit!" $ show rSplitTo
    errImproperRx :: String
    errImproperRx = printf
      "The range %s is not a part of the partition %s!" (show rSplitTo) (show s)
    matched = listToMaybe -- logically, there should be at most one partition!
      [ (Range y yl rstL, rSplitTo, Range y rstR yr, rRef)
      | rRef@(Range y yl yr) <- unpackPart p  -- choose a range in the environment
      , to == y                               -- must be in the same register file!
      , True <- maybeToList $ rSplitTo ⊑ rRef -- must be a sub-interval
      ]


-- | Cast a partition of type 'qt1' to 'qt2' and perform a split before the
-- casting if needed.  return 'Nothing' if no cast is required.
splitThenCastScheme
  :: ( Has (Gensym String) sig m
     , Has (Gensym RBinding) sig m
     , Has (State TState) sig m
     , Has Trace sig m
     , Has (Error String) sig m
     )
  => STuple
  -> QTy
  -> Range
  -> m ( STuple             -- the finally resolved partition
       , Maybe SplitScheme  -- May split if cast or not
       , Maybe CastScheme   -- May cast or not
       )
splitThenCastScheme s'@(STuple (loc, p, qt1)) qt2 rSplitTo =
  case (qt1, qt2) of
    (_, _) | isEN qt1 && qt1 == qt2 -> do
      -- same type therefore no cast needed,
      -- do check to see if split is also not needed
      (rOrigin, rsRem) <- getRangeSplits s' rSplitTo
      case rsRem of
        [] -> return (s', Nothing, Nothing)
        _  -> throwError $ errSplitEN rOrigin rsRem
    (_ , _) | not (isEN qt1) && isEN qt2 -> do
      -- casting a smaller type to a larger type
      (sSplit, maySchemeS) <- splitScheme s' rSplitTo
      (sCast, schemeC) <- castScheme sSplit qt2
      return (sCast, maySchemeS, Just schemeC)
    (_, _) | qt1 == qt2 -> do
      -- the same type, therefore, only try to compute a split scheme
      (sSplit, maySchemeS) <- splitScheme s' rSplitTo
      return (sSplit, maySchemeS, Nothing)
    _ ->
      throwError errUndef
   where
     errUndef :: String = printf
       "split-then-cast-scheme is undefined for %s to %s type"
       (show qt1) (show qt2)
     errSplitEN :: Range -> [Range] -> String
     errSplitEN rO rsR = printf
       "Splitting a 'EN' partition (%s) from (%s) into (%s) which is not advised."
       (show s') (show rO) (show (rSplitTo : rsR))



--------------------------------------------------------------------------------
-- * Aux Typing
--------------------------------------------------------------------------------

-- | Extract relevant partitions from guard expression and resolve its type.
typingGuard
  :: ( Has (State TState) sig m
     , Has (Error String) sig m
     , Has Trace sig m
     )
  => Exp -> m STuple
typingGuard (EPartition s') = resolvePartition s'
typingGuard e               = throwError $ "Unsupported guard: " ++ show e


--------------------------------------------------------------------------------
-- * Subtyping
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
subQ _    TEN   = True
subQ THad THad  = True
subQ THad TEN01 = True
subQ TNor TEN01 = True
subQ TNor TNor  = True
subQ _     _    = False

checkSubtypeQ
  :: Has (Error String) sig m
  => QTy -> QTy -> m ()
checkSubtypeQ t1 t2 =
  unless (subQ t1 t2) $
  -- traceStack "" .
  throwError $
  "Type mismatch: `" ++ show t1 ++ "` is not a subtype of `" ++ show t2 ++ "`"
-------------------------------------------------------------------------------
-- | Type Manipulation
--------------------------------------------------------------------------------
retypePartition1
  :: ( Has (Error String) sig m
     , Has (State TState) sig m
     , Has (Gensym RBinding) sig m
     )
  => STuple -> QTy -> m (Var, Ty, Var, Ty)
retypePartition1 st qtNow = do
  schemeC <- retypePartition st qtNow
  let CastScheme{ schVsOldEmit=vsPrev
                , schTOldEmit=tPrev
                , schVsNewEmit=vsNow
                , schTNewEmit=tNow
                } = schemeC
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
castScheme
  :: ( Has (Error String) sig m
     , Has (State TState) sig m
     , Has (Gensym RBinding) sig m
     )
  => STuple -> QTy -> m (STuple, CastScheme)
castScheme st qtNow = do
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
  return ( STuple (locS, sResolved, qtNow)
         , CastScheme { schVsOldEmit=vsOldEmit
                      , schTOldEmit=tOldEmit
                      , schVsNewEmit=vsNewEmit
                      , schTNewEmit=tNewEmit
                      , schQtOld=qtPrev
                      , schQtNew=qtNow
                      , schRsCast=unpackPart sResolved
                      })

-- | The same as 'castScheme', for compatibility
retypePartition
  :: ( Has (Error String) sig m
     , Has (State TState) sig m
     , Has (Gensym RBinding) sig m
     )
  => STuple -> QTy -> m CastScheme
retypePartition = (snd <$>) .: castScheme

-- Merge two given partition tuples if both of them are of EN type.
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
    unless (qtMain == qtAux && qtAux == TEN) $
      -- traceStack "" $
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
      (at locMain ?~ (newPartition, TEN))          -- update main's state
    return ()




--------------------------------------------------------------------------------
-- | Helpers
--------------------------------------------------------------------------------
-- Compute types of methods from the toplevel
collectMethodTypes :: AST -> [(Var, Ty)]
collectMethodTypes a = [ (idt, TMethod (bdTypes ins) (bdTypes outs))
                       | Toplevel (Inl (QMethod idt ins outs _ _ _)) <- a]

collectMethodTypesM :: AST -> Map.Map Var Ty
collectMethodTypesM = Map.fromList . collectMethodTypes

appkEnvWithBds :: Bindings -> TEnv -> TEnv
appkEnvWithBds bds = kEnv %~ appBds
  where appBds = Map.union $ Map.fromList [(v, t) | Binding v t <- bds]

bdTypes :: Bindings -> [Ty]
bdTypes b = [t | Binding _ t <- b]



-- | Construct from ascratch a new TState containing the given partitons.
tStateFromPartitionQTys
  :: ( Has (Gensym RBinding) sig m
     , Has (Gensym Var) sig m
     )
  => [(Partition, QTy)] -> m TState
tStateFromPartitionQTys pqts = State.execState initTState $ do
  forM_ pqts $ uncurry extendTState

-- | Extend the typing state with a partition and its type, generate emit
-- symbols for every range in the partition and return all emitted symbols in
-- the same order as those ranges.
extendTState
  :: ( Has (Gensym RBinding) sig m
     , Has (Gensym Var) sig m
     , Has (State TState) sig m
     )
  => Partition -> QTy -> m [Var]
extendTState p  qt = do
  sLoc <- gensymLoc "requires"
  sSt %= (at sLoc ?~ (p, qt))
  let xMap = [ (v, [(r, sLoc)]) | r@(Range v _ _) <- unpackPart p ]
  vsREmit <- unpackPart p `forM` (\r -> (,r) <$> r `gensymEmitRangeQTy` qt)
  xSt %= Map.unionWith (++) (Map.fromListWith (++) xMap)
  return $ fst <$> vsREmit
