{-# LANGUAGE
    FlexibleContexts
  , FlexibleInstances
  , LambdaCase
  , MultiParamTypeClasses
  , MultiWayIf
  , ScopedTypeVariables
  , TupleSections
  , TypeApplications
  , TypeFamilies
  #-}

module Qafny.Typing where

-- | Typing though Fused Effects

import qualified Debug.Trace                as Trace


-- Effects
import           Control.Carrier.Reader     (runReader)
import           Control.Carrier.State.Lazy (execState)
import           Control.Effect.Catch
import           Control.Effect.Error       (Error, throwError)
import           Control.Effect.Lens
import           Control.Effect.NonDet
import           Control.Effect.Reader
import           Control.Effect.State       (State, get, modify)
import           Effect.Gensym              (Gensym, gensym)

-- Qafny
import           Qafny.Env
import           Qafny.Error                (QError (..))
import           Qafny.Interval
import           Qafny.Syntax.AST
import           Qafny.TypeUtils
import           Qafny.Utils
    ( checkListCorr
    , exp2AExp
    , findEmitRangeQTy
    , findEmitVarsFromPartition
    , gensymEmitRB
    , gensymEmitRangeQTy
    , gensymLoc
    , gensymRangeQTy
    , projEmitBindingRangeQTy
    , removeEmitPartitionQTys
    , removeEmitRangeQTys
    , rethrowMaybe
    , uncurry3, gensymEmitRangePTyRepr, findEmitRangeDegree, gensymEmitLocDegree, onlyOne, gensymEmitRangeDegree, findEmitLocDegree
    )

-- Utils
import           Control.Carrier.State.Lazy (evalState, runState)
import           Control.Effect.Trace
import           Control.Lens
    ( Identity (runIdentity)
    , at
    , (%~)
    , (?~)
    , (^.)
    )
import           Control.Lens.Tuple
import           Control.Monad
    ( forM
    , forM_
    , mapAndUnzipM
    , unless
    , void
    , when
    , zipWithM
    )
import           Data.Bifunctor             (Bifunctor (second))
import           Data.Bool                  (bool)
import           Data.Functor               ((<&>))
import qualified Data.List                  as List
import           Data.List.NonEmpty         (NonEmpty (..))
import qualified Data.List.NonEmpty         as NE
import qualified Data.Map.Strict            as Map
import           Data.Maybe
    ( catMaybes
    , fromJust
    , fromMaybe
    , isJust
    , listToMaybe
    , mapMaybe
    , maybeToList
    )
import qualified Data.Set                   as Set
import           Data.Sum
import           Data.Sum                   (projLeft)
import           Data.Text                  (unpack)
import           GHC.Stack                  (HasCallStack)
import           Qafny.Partial              (Reducible (reduce))
import           Qafny.Syntax.Emit
    ( DafnyPrinter (build)
    , byComma
    , byLineT
    , showEmit0
    , showEmitI
    )
import           Text.Printf                (printf)


throwError'
  :: ( Has (Error String) sig m )
  => String -> m a
throwError' = throwError @String . ("[Typing] " ++)

-- | Compute the simple type of the given expression
typingExp
  :: ( Has (State TState) sig m
     , Has (Reader TEnv) sig m
     , Has (Error String) sig m
     , HasCallStack
     )
  => Exp' -> m Ty
typingExp (ENum _)  = return TNat
typingExp (EVar x)  = do
  env <- view kEnv
  return ((env ^. at x) >>= projTy) `rethrowMaybe` (show $ UnknownVariableError x env)
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
typingExp e = throwError' $
  printf "Expression %s has no proper type." (showEmitI 0 e)


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
     , Has (Reader IEnv) sig m
     , Has Trace sig m
     )
  => Partition -> m STuple
resolvePartition = (fst <$>) . resolvePartition'

resolvePartition'
  :: ( Has (State TState) sig m
     , Has (Error String) sig m
     , Has (Reader IEnv) sig m
     , Has Trace sig m
     )
  => Partition -> m (STuple, [(Range, Range)])
resolvePartition' se' = do
  rsResolved <- rs `forM` resolveRange
  let locs = [ ((rSe, rSt), loc) | (rSe, rSt, ans, loc) <- concat rsResolved, included ans ]
  constraints <- ask @IEnv
  let related = concatMap ("\n\t" ++) . concat $
                [ showRel r1 r2 b | (r1, r2, b, _) <- concat rsResolved ]
  trace $ printf "[resolvePartition] (%s) with %s %s" (show se) (show constraints) related
  case List.nub (snd <$> locs) of
    [] ->  throwError $ errInternal related
    [x] -> do
      (p, qt) <- use (sSt . at x) `rethrowMaybe` (show . UnknownLocError) x
      trace (printf "Resolved: %s ∈ %s" (show se) (show p))
      return (STuple (x, p, qt), fst <$> locs)
    ss -> throwError $ errNonunique ss related
  where
    se@(Partition rs) = reduce se'
    included :: NonEmpty (Maybe Bool, AEnv) -> Bool
    included = all ((== Just True) . fst)
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
      (showEmitI 2 se)
    mkRelOp :: Maybe Bool -> String
    mkRelOp (Just True)  = " ⊑ "
    mkRelOp (Just False) = " ⋢ "
    mkRelOp Nothing      = "?⊑?"
    showRel :: Range -> Range -> NonEmpty (Maybe Bool, AEnv) -> [String]
    showRel r1 r2 ne = NE.toList $ ne
      <&> \(rel, env) ->
            printf "%s %s %s at %s" (showEmitI 0 r1) (mkRelOp rel) (showEmitI 0 r2) (showEmitI 0 $ byComma env)


removeTStateBySTuple
  :: (Has (State TState) sig m)
  => STuple -> m ()
removeTStateBySTuple st@(STuple (loc, p, (qt, _))) = do
  sSt %= flip Map.withoutKeys (Set.singleton loc)
  xSt %= Map.map (filter ((/= loc) . snd))
  removeEmitPartitionQTys p qt

-- | Query all ranges related to the given range.
resolveRange
  :: ( Has (State TState) sig m
     , Has (Error String) sig m
     , Has (Reader IEnv) sig m
     )
  => Range -> m [(Range, Range, NonEmpty (Maybe Bool, AEnv), Loc)]
resolveRange r@(Range name _ _) = do
  (⊑//) <- (⊑/)
  rlocs <- use (xSt . at name) `rethrowMaybe` (show . UnknownRangeError) r
  return [ (r, r', r ⊑// r', loc)
         | (r', loc) <- rlocs ]


resolvePartitions
  :: ( Has (State TState) sig m
     , Has (Error String) sig m
     , Has (Reader IEnv) sig m
     , Has Trace sig m
     )
  => [Partition] -> m STuple
resolvePartitions =
  resolvePartition . Partition . concatMap unpackPart


inferRangeTy
  :: ( Has (State TState) sig m
     , Has (Error String) sig m
     , Has (Reader IEnv) sig m
     , Has Trace sig m)
  => Range -> m (QTy, [Int])
inferRangeTy r = (^. _3) . unSTup <$> resolvePartition (Partition [r])

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
     , Has (Gensym EmitBinding) sig m
     , Has (Reader IEnv) sig m
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


-- | Rationale: there's no good reason to split a partition with multiple ranges
-- in entanglement. So, we're safe to reject non-singleton partitions for now.
splitSchemePartition
  :: ( Has (Error String) sig m
     , Has (Gensym String) sig m
     , Has (State TState) sig m
     , Has (Gensym EmitBinding) sig m
     , Has (Reader IEnv) sig m
     , Has Trace sig m
     )
  => STuple
  -> Partition
  -> m (STuple, Maybe SplitScheme)
splitSchemePartition st p =
  case unpackPart p of
    [r] -> splitScheme st r
    _   -> throwError' $
      printf "Partition %s contains multiple ranges for split, which is likely to be a bug!" (showEmitI 0 p)


-- | Remove range if it is equivalent to the bottom
contractRange
  :: ( Has (Error String) sig m
     , Has (Reader IEnv) sig m
     )
  => Range -> m (Maybe Range)
contractRange r = do
  botHuh <- ($ r) <$> isBotI
  case botHuh of
    _ | all (== Just True) botHuh -> return Nothing
    _ | all isJust botHuh         ->
        -- may or may not be, therefore leave it there
        return (Just r)
    _                             -> err botHuh
  where
    err reason = do
      ienv <- ask @IEnv
      throwError' $ printf "Cannot decide if %s is empty; context: %s"
        (show r) (show ienv)

-- TODO1: Pass in an environment and perform substitution before doing value
-- checking
-- TODO2: Use 'NonDeterm' effects instead.
splitScheme'
  :: ( Has (Error String) sig m
     , Has (Gensym String) sig m
     , Has (State TState) sig m
     , Has (Gensym EmitBinding) sig m
     , Has (Reader IEnv) sig m
     , Has Trace sig m
     )
  => STuple
  -> Range
  -> m (STuple, Maybe SplitScheme)
splitScheme' s@(STuple (loc, p, xt@(qt, ptys))) rSplitTo@(Range to rstL rstR) = do
  -- FIXME: Type checking of `qt` should happen first because splitting an EN
  -- typed partition should not be allowed.
  -- TODO: Is this correct?
  when (isEN qt) $ throwError'' errSplitEN
  RangeSplits { rsRsRest=rsRest
              , rsDsRest=dgrsRest
              , rsRLeft=rLMaybe
              , rsRRight=rRMaybe
              , rsRFocused=rOrigin
              , rsDFocused=dgrOrigin
              , rsRsRem = rsRem
              } <- getRangeSplits s rSplitTo
  let -- the ranges except the chosen one + the quotient ranges
      rsMain = rsRem ++ rsRest
      rsAux  = [rSplitTo]
      pMain  = Partition rsMain
      pAux   = Partition rsAux
  -- generate
  ~(vReprPTyMaybesSplit : vReprPTyMaybesRem) <-
    forM (rSplitTo : rsRem) (`gensymEmitRangePTyRepr` dgrOrigin)
  ptysRest <- forM (zip rsRest dgrsRest) (uncurry findEmitRangeDegree)
  let ptysRem = vReprPTyMaybesRem
      ptySplitTo = vReprPTyMaybesSplit
      ptysMain = ptysRem ++ ptysRest
      dgrsMain = (dgrOrigin <$ rsRem) ++ dgrsRest
  case rsMain of
    [] ->
      -- ^ No need to split at all, so we're safe regardless of the qtype
      --
      return (s, Nothing) -- no split at all!

    _  -> do
      -- ^ Split in partition or in both partition and a range
      -- There's a need for split.
      --
      -- 1. Allocate partitions, break ranges and move them around
      locAux <- gensymLoc to
      sSt %= (at loc ?~ (pMain, (qt, dgrsMain))) . (at locAux ?~ (pAux, (qt, [dgrOrigin])))
      -- use sSt >>= \s' -> trace $ printf "sSt: %s" (show s')
      xRangeLocs <- use (xSt . at to) `rethrowMaybe` errXST
      let xrl =
            -- "new range -> new loc"
            [ (rAux, locAux) | rAux <- rsAux ] ++
            -- "split ranges -> old loc"
            [ (rMainNew, loc) | rMainNew <- rsRem ] ++
            -- "the rest with the old range removed"
            List.filter ((/= rOrigin) . fst) xRangeLocs
      xSt %= (at to ?~ xrl)
      -- 2. Generate emit symbols for split ranges
      let sMain' = (loc, pMain, (qt, dgrsMain)) -- the part that's splited _from_
      case rsRem of
        [] -> case qt of
          t | t `elem` [ TEN, TEN01 ] ->
              throwError'' errSplitEN
          _ ->
            -- only split in partition but not in a range,
            -- therefore, no need to duplicate the range-based phases
            let sAux' = (locAux, pAux, xt)
            in return (STuple sAux', Nothing)
        _  -> do
          (vEmitR, rSyms, rPhReprs) <- case qt of
            t | t `elem` [ TNor, THad ] -> do
              -- locate the original range
              vEmitR <- findEmitRangeQTy rOrigin qt
              -- delete it from the record
              removeEmitRangeQTys [(rOrigin, qt)]
              -- gensym for each split ranges
              rSyms <- (rSplitTo : rsRem) `forM` (`gensymEmitRangeQTy` qt)
              return (vEmitR, rSyms, (ptySplitTo : ptysRem))
            _    -> throwError'' $ errUnsupprtedTy ++ "\n" ++ infoSS
          let sAux' = (locAux, pAux, (qt, [dgrOrigin]))
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
    throwError'' = throwError' . ("[split] " ++)
    errUnsupprtedTy = printf "Splitting a %s partition is unsupported." (show qt)
    errXST = printf "No range beginning with %s cannot be found in `xSt`" to
    errSplitEN = "Splitting an EN partition is disallowed!"

-- | Duplicate a phase type by allocating a new reference to its Repr if
-- necessary.
--
-- duplicatePhaseTy
--   :: ( Has (Gensym EmitBinding) sig m
--      )
--   => Loc -> QTy -> PhaseTy
--   -> m PhaseTy
-- duplicatePhaseTy _ _ PT0 = return PT0
-- duplicatePhaseTy v qt pty@(PTN i (PhaseRef { prBase=vBase, prRepr=_ })) = do
--   -- allocate a new repr variable without allocating a new base one
--   vRepr <- gensym (LBinding (deref v, inj pty))
--   return (PTN i (PhaseRef { prBase=vBase, prRepr=vRepr }))


data RangeSplits = RangeSplits
  { rsRLeft    :: Maybe Range -- | left remainder
  , rsRRight   :: Maybe Range -- | right remainder
  , rsRSplit   :: Range       -- | the split range
  , rsRFocused :: Range       -- | the original range
  , rsDFocused :: Int         -- | the degree of the original range
  , rsRsRest   :: [Range]     -- | other ranges untouched
  , rsDsRest   :: [Int]       -- | The degrees of ....
  , rsRsRem    :: [Range]     -- | all remainders (left + right)
  }

-- | Compute, in order to split the given range from a resolved partition, which
-- range in the partition needs to be split as well as the resulting quotient
-- ranges.
getRangeSplits
  :: ( Has (Error String) sig m
     , Has (Reader IEnv) sig m
     )
  => STuple -> Range -> m RangeSplits
getRangeSplits s@(STuple (loc, p, (qty, dgrs))) rSplitTo@(Range to rstL rstR) = do
  botHuh <- ($ rSplitTo) <$> isBotI
  case botHuh of
    _ | all (== Just True)  botHuh -> throwError' errBotRx
    _ | all (== Just False) botHuh -> return ()
    _ -> do ienv <- ask @IEnv
            throwError' $ printf "Cannot decide if %s is empty.\nEnv: %s" (show rSplitTo) (show ienv)
  (⊑??) <- (⊑?)
  case matched (⊑??) of
    Nothing -> throwError' errImproperRx
    Just (rRemL, _, rRemR, rOrigin, idx)  -> do
      rRemLeft <- contractRange rRemL
      rRemRight <- contractRange rRemR
      let psRest = if isEN qty then [] else removeNth idx dgrs
          rsRest = removeNth idx (unpackPart p)
      return $ RangeSplits
        { rsRLeft = rRemLeft
        , rsRRight = rRemRight
        , rsRSplit = rSplitTo
        , rsRFocused = rOrigin
        , rsDFocused = head dgrs
        , rsRsRest = rsRest
        , rsDsRest = psRest
        , rsRsRem = catMaybes [rRemLeft, rRemRight]
        }
  where
    removeNth n l = let (a, b) = splitAt n l in a ++ tail b
    nRange = length . unpackPart $ p
    -- infoSS :: String = printf "[checkScheme] from (%s) to (%s)" (show s) (show rSplitTo)
    errBotRx = printf "The range %s contains no qubit!" $ show rSplitTo
    errImproperRx = printf
      "The range %s is not a part of the partition %s!" (show rSplitTo) (show s)
    matched (⊑??) = listToMaybe -- logically, there should be at most one partition!
      [ (Range y yl rstL, rSplitTo, Range y rstR yr, rRef, idx)
      | (rRef@(Range y yl yr), idx) <- zip (unpackPart p) [0..]
        -- ^ choose a range in the environment
      , to == y           -- | must be in the same register file!
      , rSplitTo ⊑?? rRef -- | must be a sub-interval
      ]


-- | Cast a partition of type 'qt1' to 'qt2' and perform a split before the
-- casting if needed.  return 'Nothing' if no cast is required.
splitThenCastScheme
  :: ( Has (Gensym String) sig m
     , Has (Gensym EmitBinding) sig m
     , Has (State TState) sig m
     , Has Trace sig m
     , Has (Reader IEnv) sig m
     , Has (Error String) sig m
     )
  => STuple
  -> QTy
  -> Range
  -> m ( STuple             -- the finally resolved partition
       , Maybe SplitScheme  -- May split if cast or not
       , Maybe CastScheme   -- May cast or not
       )
splitThenCastScheme s'@(STuple (loc, p, (qt1, ptys))) qt2 rSplitTo =
  case (qt1, qt2) of
    (_, _) | isEN qt1 && qt1 == qt2 -> do
      -- same type therefore no cast needed,
      -- do check to see if split is also not needed
      RangeSplits { rsRFocused = rOrigin
                  , rsRsRem = rsRem
                  } <- getRangeSplits s' rSplitTo
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
     , Has (Reader IEnv) sig m
     , Has Trace sig m
     )
  => GuardExp -> m (STuple, Partition)
typingGuard (GEPartition s' _) = resolvePartition s' <&> (,s')

-- | Type check if the given partition exists in the context
typingPartitionQTy
  :: ( Has (State TState)  sig m
     , Has (Error String) sig m
     , Has (Reader IEnv) sig m
     , Has Trace sig m
     )
  => Partition -> QTy -> m STuple
typingPartitionQTy s qt = do
  st@(STuple tup) <- resolvePartition s
  when (qt /= (tup ^. _3 ^. _1)) $ throwError' (errTypeMismatch st)
  return st
  where
    errTypeMismatch st =
      printf "The partition %s is not of type %s.\nResolved: %s"
      (show s) (show qt) (show st)

typingPartition
  :: ( Has (State TState)  sig m
     , Has (Error String) sig m
     , Has (Reader IEnv) sig m
     , Has Trace sig m
     )
  => Partition -> m STuple
typingPartition s = do
  st@(STuple(_, pResolved, qtResolved)) <- resolvePartition s
  when (List.sort (unpackPart s) /= List.sort (unpackPart pResolved)) $
    throwError' $ errIncompletePartition st
  return st
  where
    errIncompletePartition st@(STuple(_, p, _)) =
      printf "The partition %s is a sub-partition of %s.\nResolved: %s"
      (show s) (show p) (show st)

--------------------------------------------------------------------------------
-- * Subtyping
--------------------------------------------------------------------------------
checkTypeEq
  :: Has (Error String) sig m
  => Ty -> Ty -> m ()
checkTypeEq t1 t2 =
  unless (t1 == t2)
    (throwError @String $
      printf "Type mismatch: `%s` is not a subtype of `%s`"
      (showEmitI 0 t1)
      (showEmitI 0 t2))

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

  -- traceStack "" .

  -- traceStack "" .

  -- traceStack "" .
  throwError $
  "Type mismatch: `" ++ show t1 ++ "` is not a subtype of `" ++ show t2 ++ "`"
-------------------------------------------------------------------------------
-- | Type Manipulation
--------------------------------------------------------------------------------
retypePartition1
  :: ( Has (Error String) sig m
     , Has (State TState) sig m
     , Has (Gensym EmitBinding) sig m
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
     , Has (Gensym EmitBinding) sig m
     )
  => STuple -> QTy -> m (STuple, CastScheme)
castScheme st qtNow = do
  let STuple(locS, sResolved, (qtPrev, _)) = st
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
  -- FIXME: Cast phases
  let pty' = undefined
  sSt %= (at locS ?~ (sResolved, (qtNow, pty')))
  vsNewEmit <- unpackPart sResolved `forM` (`gensymEmitRangeQTy` qtNow)
  return ( STuple (locS, sResolved, (qtNow, pty'))
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
     , Has (Gensym EmitBinding) sig m
     )
  => STuple -> QTy -> m CastScheme
retypePartition = (snd <$>) .: castScheme

--------------------------------------------------------------------------------
-- * Merge Typing
--------------------------------------------------------------------------------

matchEmitStates
  :: EmitState -> EmitState -> [(Range, (Var, Var))]
matchEmitStates es1 es2 =
  filter removeEq . Map.toList $ Map.intersectionWith (,) em1 em2
  where
    removeEq (_, (v1, v2)) = v1 /= v2
    ripLoc = (`Map.withoutKeys` Set.singleton Nothing) .
      Map.mapKeys ((fst <$>) . projEmitBindingRangeQTy)
    reduceKeys = Map.mapKeys (reduce . fromJust)
    reduceMap = reduceKeys . ripLoc
    (em1, em2) = (reduceMap es1, reduceMap es2)


-- Given two states compute the correspondence of emitted varaible between two
-- states where 'tsInit' refers to the state before iteration starts and
-- 'tsLoop' is for the state during iteration.
matchStateCorrLoop
  :: ( Has (Error String) sig m
     )
  => TState -> TState -> AEnv -> m [(Var, Var)]
matchStateCorrLoop tsInit tsLoop env = do
  pure $ snd <$> matchEmitStates esLoop esInit
  where
    esInit = tsInit ^. emitSt
    esLoop = subst env $ tsLoop ^. emitSt


-- | Take 2 type states, match emit variables by their ranges and output
-- merge scheme for each of them.
mergeMatchedTState
  :: ( Has (Error String) sig m
     , Has (Reader IEnv) sig m
     , Has Trace sig m)
  => TState -> TState -> m [MergeScheme]
mergeMatchedTState
  ts1@TState {_emitSt=eSt1}
  ts2@TState {_emitSt=eSt2}
  = (catMaybes <$>) . forM matchedRangeAndVars $ \(r, (v1, v2)) -> do
  (qt1, _) <- getQPTy ts1 r
  (qt2, _) <- getQPTy ts2 r
  when (qt1 /= qt2) $ throwError' "How can they be different?"
  pure $ case qt1 of
    _ | qt1 `elem` [ TEN, TEN01 ] -> Just . MEqual $
        EqualStrategy
        { esRange = r
        , esQTy = qt1
        , esVMain = v1
        , esVAux = v2
        }
    _ -> Nothing
  where
    matchedRangeAndVars = matchEmitStates eSt1 eSt2
    getQPTy ts r = evalState ts $ inferRangeTy r


-- | Merge the second STuple into the first one
-- FIXME: Check if phase type is correct!
mergeScheme
  :: ( Has (State TState) sig m
     , Has (Error String) sig m
     , Has (Reader IEnv) sig m
     )
  => STuple -- ^ Main
  -> STuple -- ^ Servent
  -> m [MergeScheme]
mergeScheme
  stM'@(STuple (locMain, _, (qtMain, ptysMain)))
  stA@(STuple (locAux, sAux@(Partition rsAux), (qtAux, ptysAuz))) = do
  sSt %= (`Map.withoutKeys` Set.singleton locAux) -- GC aux's loc
  forM rsAux $ \rAux@(Range _ _ erAux) -> do
    -- fetch the latest 'rsMain'
    let fetchMain = uses sSt (^. at locMain)
    (Partition rsMain, _) <- rethrowMaybe fetchMain "WTF?"
    -- decide how to merge based on the if there's an adjacent range match
    rsMergeTo <- lookupAdjacentRange rsMain rAux
    case rsMergeTo of
      [] -> do
        -- | Merge the standalone range into the Main partition and update range
        -- reference record in 'xSt' and the partition informaton of Main in
        -- 'sSt'
        let pM = Partition $ rAux : rsMain
        xSt %= Map.map redirectX
        sSt %= (at locMain ?~ (pM, (qtMain, ptysMain))) -- update main's partition
        return MMove
      [rCandidate@(Range x elCandidate _)] -> do
        -- | Merge the range into an existing range
        -- We know that the upperbound of the candidate is the same as the
        -- lowerbound of the aux range
        let rNew = Range x elCandidate erAux
        let pM = Partition $ (\r -> bool r rNew (r == rCandidate)) <$> rsMain
        xSt %= Map.map (revampX rCandidate rAux rNew)
        sSt %= (at locMain ?~ (pM, (qtMain, ptysMain)))
        return $ MJoin JoinStrategy
          { jsRMain = rCandidate
          , jsRMerged = rAux
          , jsRResult = rNew
          , jsQtMain = qtMain
          , jsQtMerged = qtAux
          }
      _ -> throwError' "Whoops! A lot of candidates to go, which one to go?"
  where
    redirectX rAndLoc = do
      (r, locR) <- oneOf rAndLoc
      let locRNew = if locR == locAux then locMain else locR
      return (r, locRNew)
    revampX rCandidate rAux rNew rAndLoc = do
      self@(r, locR) <- oneOf rAndLoc
      return $ if r == rCandidate || r == rAux
               then (rNew, locMain)
               else self

-- | check if there exists a range that's adjacent to another.
lookupAdjacentRange
  :: ( Has (Reader IEnv) sig m
     )
  => [Range] -> Range -> m [Range]
lookupAdjacentRange rs r@(Range _ el er) = do
  (≡?) <- (allI .:) <$> liftIEnv2 (≡)
  return  [ r' | r'@(Range x' el' er') <- rs, er' ≡? el ]


-- | Given two STuples in EN type where the first is for the body partition and
-- the other one is for the guard partition.
--
mergeSTuplesHadEN
  :: ( Has (State TState) sig m
     , Has (Error String) sig m
     )
  => STuple -> STuple -> m ()
mergeSTuplesHadEN
  stM@(STuple (locMain, sMain@(Partition rsMain), (qtMain, ptysMain)))
  stA@(STuple (locAux, sAux@(Partition rsAux), (qtAux, ptysAux))) =
  do
    -- Sanity Check
    unless (qtMain == qtAux && qtAux == TEN) $
      throwError @String $ printf "%s and %s have different Q types!"
        (show stM) (show stA)

    -- start merge
    let newPartition = Partition $ rsMain ++ rsAux
    xSt %= Map.map
      (\rLoc -> [ (r, loc')
                | (r, loc) <- rLoc,
                  let loc' = if loc == locAux then locMain else loc])
    sSt %=
      (`Map.withoutKeys` Set.singleton locAux) . -- GC aux's loc
      (at locMain ?~ (newPartition, (TEN, ptysMain))) -- update main's state
    return ()

--------------------------------------------------------------------------------
-- * Method Typing
--------------------------------------------------------------------------------
-- Generate a method type signature through pre-&post- conditions and the
-- origianl signature following the calling convention.
--
analyzeMethodType :: QMethod () -> (Var, MethodType)
analyzeMethodType (QMethod v bds rts rqs ens _) =
  let srcParams = collectRange <$> bds
      srcReturns = collectRange <$> rts
      instantiate (r :: Map.Map Var Range) =
        runIdentity $ runReader r $ forM (mapMaybe collectSignature rqs) go
      receive (r :: Map.Map Var Range) =
        runIdentity $ runReader r $ forM (mapMaybe collectSignature ens) go

    in (v, MethodType { mtSrcParams=srcParams
                      , mtSrcReturns=srcReturns
                      , mtInstantiate = instantiate
                      , mtReceiver = receive
                      -- , mtDebugInit = mapMaybe collectSignature rqs
                      })
  where
    collectRange :: Binding () -> MethodElem
    collectRange (Binding vq (TQReg a)) = MTyQuantum vq (aexpToExp a)
    collectRange (Binding varg t)       = MTyPure varg t

    -- FIXME: collect phase types as well
    collectSignature :: Exp' -> Maybe (Partition, QTy, [Int])
    collectSignature (ESpec s qt pexp) =
      pure (s, qt, analyzePhaseSpecDegree . snd <$> pexp)
    collectSignature _                 = Nothing

    go
      :: (Has (Reader (Map.Map Var Range)) sig' m')
      => (Partition, QTy, [Int]) -> m' (Partition, QTy, [Int])
    go (s, qt, dgr) = (,qt, dgr) <$> instPart s

    -- instantiate a Type expression with a given mapping from variable to Range
    instPart
      :: (Has (Reader (Map.Map Var Range)) sig' m')
      => Partition -> m' Partition
    instPart (Partition rs) = Partition <$> mapM instRange rs

    instRange
      :: ( Has (Reader (Map.Map Var Range)) sig' m' )
      => Range -> m' Range
    instRange rr@(Range x l r) = do
      -- Q: What to do with the right
      rMaybe <- asks (Map.!? x)
      pure $ case rMaybe of
        Just (Range x' l' r') ->
          reduce $ Range x' (reduce (l + l')) (reduce (r + l'))
        Nothing               -> rr

typeCheckEachParameter
  :: ( Has (Error String) sig m'
     , Has (State (Map.Map Var Range)) sig m'
     , Has (State TState) sig m'
     , Has (Reader IEnv) sig m'
     , Has (Reader TEnv) sig m'
     )
  => Exp' -> MethodElem -> m' (Maybe Exp')
-- for simple types, check it immediately
typeCheckEachParameter earg (MTyPure v ty) = do
  tyArg <- typingExp earg
  checkTypeEq tyArg ty
  pure (Just earg)
-- for quantum types, collect the qreg correspondence instead
typeCheckEachParameter earg (MTyQuantum v cardinality) = do
  qRange@(Range x el er) <-
    case earg of
      EVar varg                  -> pure $ Range varg 0 cardinality
      EPartition (Partition [r]) -> pure r
      _                          -> nonQArgument earg
  -- check if the cardinality is fine
  let eCard :: Exp' = er - el
  eq <- (allI .:) <$> liftIEnv2 (≡)
  unless (eq 0 (er - el - cardinality)) $
    throwError' $ cardinalityMismatch eCard cardinality
  modify (Map.insert v qRange)
  pure Nothing
  where
    nonQArgument arg = throwError' $
      printf "%s is not a valid qreg parameter" (showEmitI 0 arg)
    cardinalityMismatch cardGiven cardReq = fail $
      printf "the cardinality of the qreg passed %s doesn't match the required: %s"
      (showEmitI 0 cardGiven) (showEmitI 0 cardReq)


-- | Compute the argment map and pure arguments for a given argument list and
-- parameter list.
normalizeArguments
  :: ( Has (Error String) sig m
     , Has (State TState) sig m
     , Has (Reader IEnv) sig m
     , Has (Reader TEnv) sig m
     )
  => [Exp'] -> [MethodElem] -> m (Map.Map Var Range, [Exp'])
normalizeArguments es params = runState Map.empty $
    catMaybes <$> zipWithM typeCheckEachParameter es params

-- | Take in a list of arguments, check against the method signature and resolve
-- arguments to be emitted w.r.t. the calling convention.
--
-- Return a map from QVars to ranges passed, arguments to be emitted, and passed
-- STuples in the caller's context.
resolveMethodApplicationArgs
  ::  ( Has (Gensym String) sig m
      , Has (Gensym EmitBinding) sig m
      , Has (Error String) sig m
      , Has (Reader TEnv) sig m
      , Has (Reader IEnv) sig m
      , Has (State TState) sig m
      , Has Trace sig m
      )
  => [Exp']
  -> MethodType
  -> m (Map.Map Var Range, [Exp'], [(STuple, Maybe SplitScheme, Maybe CastScheme)])
resolveMethodApplicationArgs es
  MethodType { mtSrcParams=srcParams
             , mtInstantiate=instantiator
             } = do
  unless (length es == length srcParams) $ arityMismatch srcParams
  (envArgs, pureArgs) <- normalizeArguments es srcParams
  let inst = instantiator envArgs
  -- perform qtype check for each argument
  (resolvedSts, qArgs) <- second concat <$>
    mapAndUnzipM (uncurry getEmitVarsAfterTyCheck) ((\(a,b,c) -> (a, b)) <$> inst)
  pure (envArgs, pureArgs ++ qArgs, resolvedSts)
  where
    arityMismatch prs = throwError' $
      "The number of arguments given doesn't match the number of parameters expected by the method."
      ++ printf "Given:\n%s\nExpected:\n%s" (show es) (show prs)


    -- type check partitions in the typing state
    getEmitVarsAfterTyCheck part q = do
      sAndMaySC <- case part of
        Partition [r] -> do
          st <- resolvePartition part
          splitThenCastScheme st q r
        _ -> (, Nothing, Nothing) <$> typingPartitionQTy part q
      (sAndMaySC,) <$> (findEmitVarsFromPartition part q <&> fmap EVar)



-- | Compute the typing state after returning from a method call.
resolveMethodApplicationRets
  ::  ( Has (Error String) sig m
      , Has (State TState) sig m
      , Has (Gensym Var) sig m
      , Has (Gensym EmitBinding) sig m
      )
  => Map.Map Var Range -> MethodType ->  m [Var]
resolveMethodApplicationRets envArgs
  MethodType { mtSrcReturns=retParams
             , mtReceiver=receiver
             } = do
  qBindings :: [Var] <- concat <$> forM psRet ((fst <$>) . extendTState'Degree)
  -- TODO: also outputs pure variables here
  -- Sanity check for now:
  let pureArgs = collectPureBindings retParams
  unless (null pureArgs) unimpl
  return qBindings
  where
    unimpl = throwError' "Unimplemented: method returns a pure value."
    -- partitions after the method call
    psRet = receiver envArgs

--------------------------------------------------------------------------------
-- | Constraints
--------------------------------------------------------------------------------
collectConstraints
  :: ( Has (Error String) sig m )
  => [Exp'] -> m (Map.Map Var (Interval Exp'))
collectConstraints es = (Map.mapMaybe glb1 <$>) . execState Map.empty $
  forM normalizedEs collectIntv
  where
    collectIntv e@(op, v1, e2) = do
      intv :: Interval Exp' <- case op of
            OLt -> pure $ Interval 0 e2
            OLe -> pure $ Interval 0 (e2 + 1)
            OGt -> pure $ Interval (e2 + 1) maxE
            OGe -> pure $ Interval e2 maxE
            _   -> failUninterp e
      modify $ Map.insertWith (++) v1 [intv]

    -- pick 100 here to avoid overflow in computation
    maxE = fromInteger $ toInteger (maxBound @Int - 100)

    failUninterp e = throwError' $ printf "(%s) is left uninterpreted" (show e)

    normalize e@(EOp2 op (EVar v1) e2) = pure (op , v1, e2)
    normalize (EOp2 op e2 (EVar v1))   = (, v1, e2) <$> flipLOp op
    normalize _                        = Nothing

    normalizedEs = mapMaybe normalize es

    flipLOp OLt = pure OGt
    flipLOp OLe = pure OGe
    flipLOp OGe = pure OLe
    flipLOp OGt = pure OLt
    flipLOp _   = Nothing


-- | Given an STuple for a fragment of a Had guard match in the current
-- environment for a EN partition to be merged with this stuple.
mergeCandidateHad
  :: ( Has (State TState) sig m
     , Has (Error String) sig m
     , Has (Reader IEnv) sig m
     , Has Trace sig m
     )
  => STuple -> m STuple
mergeCandidateHad st@(STuple (_, Partition [r], (THad, ptys))) = do
  ps <- use sSt <&> Map.elems
  matched <- catMaybes <$> forM ps matchMergeable
  case matched of
    [p'] -> resolvePartition p'
    _    -> throwError' $ ambiguousCandidates matched
  where
    matchMergeable (p'@(Partition rs), (TEN, ptysEN)) = do
      rsAdjacent <- lookupAdjacentRange rs r
      pure $ case rsAdjacent of
        [] -> Nothing
        _  -> Just p'
    matchMergeable _ = pure Nothing

    ambiguousCandidates matched = printf
      "There're more than one merge candidate for %s.\n%s"
      (show st) (showEmit0 $ byLineT matched)


mergeCandidateHad st =
  throwError' $ printf "%s may not be a Had guard partition." (show st)

--------------------------------------------------------------------------------
-- * Phase Typing
--------------------------------------------------------------------------------

-- | Analyze the degree of a phase expression
analyzePhaseSpecDegree :: PhaseExp -> Int
analyzePhaseSpecDegree PhaseZ          = 0
analyzePhaseSpecDegree PhaseWildCard   = 0
analyzePhaseSpecDegree PhaseOmega{}    = 1
analyzePhaseSpecDegree PhaseSumOmega{} = 2


-- | Generate variables and phase types based on a phase specification.
-- generatephasetype
--   :: ( Has (Gensym EmitBinding) sig m
--      )
--   => Int -> m PhaseTy
-- generatePhaseType 0 = return PT0
-- generatePhaseType n = do
--   vEmitBase <- gensym (LBinding ("base", inj n))
--   vEmitRepr <- gensym (LBinding ("repr", inj (typingPhaseEmitReprN 1)))
--   return (PTN n $ PhaseRef { prBase = vEmitBase, prRepr = vEmitRepr })


-- | Query in the emit state the phase types of the given STuple
queryPhaseType
  :: ( Has (State TState) sig m
     , Has (Error String) sig m
     )
  => STuple -> m [PhaseTy] 
queryPhaseType (STuple (loc, Partition rs, (qt, dgrs))) =
  if | isEN qt -> do
         dgr <- onlyOne throwError' dgrs
         (: []) <$> findEmitLocDegree loc dgr
     | otherwise -> do
         checkListCorr rs dgrs
         forM (zip rs dgrs) $ uncurry findEmitRangeDegree

--------------------------------------------------------------------------------
-- | Helpers
--------------------------------------------------------------------------------
-- | Collect all partitions with their types from spec expressions
specPartitionQTys :: [Exp x] -> [(Partition, QTy, [Int])]
specPartitionQTys es =
  [ (p, qty, analyzePhaseSpecDegree . snd <$> specs)
  | (ESpec p qty specs) <- es
  ]


-- Collect all pure variables
collectPureBindings :: [MethodElem] -> [Binding']
collectPureBindings params =  [ Binding v t | MTyPure v t <- params ]

-- Compute types of methods from the toplevel
collectMethodTypes :: AST -> Map.Map Var MethodType
collectMethodTypes a = run $ execState Map.empty $
  forM_ a go
  where
    go (Toplevel (Inl q@(QMethod {}))) =
      modify (uncurry Map.insert (analyzeMethodType q))
    go _ = pure ()

appkEnvWithBds :: Bindings () -> TEnv -> TEnv
appkEnvWithBds bds = kEnv %~ appBds
  where appBds = Map.union $ Map.fromList [(v, inj t) | Binding v t <- bds]

bdTypes :: Bindings () -> [Ty]
bdTypes b = [t | Binding _ t <- b]


-- | Construct from a scratch a new TState containing the given partitons.
tStateFromPartitionQTys
  :: ( Has (Gensym EmitBinding) sig m
     , Has (Gensym Var) sig m
     , Has (Error String) sig m
     )
  => [(Partition, QTy, [Int])] -> m TState
tStateFromPartitionQTys pqts = execState initTState $ do
  forM_ pqts extendTState'Degree

-- | Extend the typing state with a partition and its type, generate emit
-- symbols for every range in the partition and return all emitted symbols in
-- the same order as those ranges.
extendTState
  :: ( Has (Gensym EmitBinding) sig m
     , Has (Gensym Var) sig m
     , Has (State TState) sig m
     , Has (Error String) sig m
     )
  => Partition -> QTy -> [Int] -> m ([Var], [PhaseTy])
extendTState p qt dgrs = do
  sLoc <- gensymLoc "requires"
  sSt %= (at sLoc ?~ (p, (qt, dgrs)))
  let xMap = [ (v, [(r, sLoc)]) | r@(Range v _ _) <- ranges ]
  ptys <- if | isEN qt -> do
                 dgr <- onlyOne throwError' dgrs
                 (: []) <$> gensymEmitLocDegree sLoc dgr
             | otherwise -> do
                 checkListCorr dgrs ranges
                 forM (zip ranges dgrs) (uncurry gensymEmitRangeDegree)
  vsREmit <- unpackPart p `forM` (\r -> (,r) <$> r `gensymEmitRangeQTy` qt)
  xSt %= Map.unionWith (++) (Map.fromListWith (++) xMap)
  return $ (,ptys) $ fst <$> vsREmit
  where
    ranges = unpackPart p

extendTState'Degree
  :: ( Has (Gensym EmitBinding) sig m
     , Has (Gensym Var) sig m
     , Has (State TState) sig m
     , Has (Error String) sig m
     )
  => (Partition, QTy, [Int]) -> m ([Var], [PhaseTy])
extendTState'Degree (p, qt, ds) =
  extendTState p qt ds


-- * Lattice and Ordering Operators lifted to IEnv
-- | Perform substitution on both ranges and compute with the (⊑) predicate
liftIEnv2
  :: ( Has (Reader IEnv) sig m, Substitutable b )
  => (b -> b -> a) -> m (b -> b -> NonEmpty (a, AEnv))
liftIEnv2 (<?>) = do
  ienv <- ask @IEnv
  return $ \r1 r2 ->
    let fvs = fVars r1 ++ fVars r2 ++ concatMap (concatMap fVars . NE.toList . snd) ienv
        aenvs = nondetIEnv $ filterIEnv fvs ienv
        subst' r'' = (\aenv -> fixN (subst aenv) (length aenv) r'') <$> aenvs
    in NE.zipWith (\(r1', r2') -> (r1' <?> r2',)) (NE.zip (subst' r1) (subst' r2)) aenvs

fixN ::  (a -> a) -> Int -> (a -> a)
fixN f = go
  where
    go 0 = id
    go n = go (n - 1) . f

-- some permutations
(⊑/)
  :: ( Has (Reader IEnv) sig m )
  => m (Range -> Range -> NonEmpty (Maybe Bool, AEnv))
(⊑/) = liftIEnv2 (⊑)

allI :: NonEmpty (Maybe Bool, a) -> Bool
allI = all ((== Just True) . fst)

-- All hold?
(⊑?)
  :: ( Has (Reader IEnv) sig m )
  => m (Range -> Range -> Bool)
(⊑?) = (allI .:) <$> (⊑/)

isBotI
  :: ( Has (Reader IEnv) sig m )
  => m (Range -> NonEmpty (Maybe Bool))
isBotI = do
  ienv <- ask
  return $ \r -> isBot . (\env -> fixN (substR env) (length env) r) <$> nondetIEnv ienv


