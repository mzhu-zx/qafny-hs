{-# LANGUAGE
    FlexibleContexts
  , FlexibleInstances
  , LambdaCase
  , MultiParamTypeClasses
  , MultiWayIf
  , NamedFieldPuns
  , ParallelListComp
  , ScopedTypeVariables
  , TupleSections
  , TypeApplications
  , TypeFamilies
  #-}


module Qafny.Typing.Typing where

-- | Typing though Fused Effects

-- Effects
import           Control.Effect.NonDet
import           Qafny.Effect

-- Qafny
import           Qafny.Error
    (QError (..))
import           Qafny.Interval
import           Qafny.Partial
    (Reducible (reduce))
import           Qafny.Syntax.AST
import           Qafny.Syntax.Emit
    (byComma, byLineT, showEmit0, showEmitI)
import           Qafny.Syntax.EmitBinding
import           Qafny.Syntax.IR
import           Qafny.Typing.Utils
import           Qafny.Utils.Utils
    (errTrace, exp2AExp, fromMaybeM, gensymLoc, rethrowMaybe, uncurry3)

import           Qafny.Typing.Partial
import           Qafny.Utils.EmitBinding

-- Utils
import           Control.Carrier.State.Lazy
    (evalState, execState)
import           Control.Lens
    (at, (%~), (?~), (^.))
import           Control.Monad
    (forM, forM_, liftM2, unless, when, zipWithM, (>=>))
import           Data.Bifunctor
    (Bifunctor (second))
import           Data.Bool
    (bool)
import           Data.Functor
    ((<&>))
import           Data.Functor.Identity

import qualified Data.List                  as List
import           Data.List.NonEmpty
    (NonEmpty (..))
import qualified Data.List.NonEmpty         as NE
import qualified Data.Map.Strict            as Map
import           Data.Maybe
    (catMaybes, isJust, listToMaybe, mapMaybe)
import qualified Data.Set                   as Set
import           Data.Sum
import           GHC.Stack
    (HasCallStack)
import           Qafny.Typing.Cast
import           Qafny.Typing.Error
    (SCError (SplitENError), failureAsSCError)
import           Text.Printf
    (printf)
import Qafny.Typing.Locus (updateMetaStByLocus)

throwError'
  :: ( Has (Error String) sig m )
  => String -> m a
throwError' = throwError @String . ("[Typing] " ++)

-- | Compute the simple type of the given expression
typingExp
  :: ( Has (Reader TEnv) sig m
     , Has (Error String) sig m
     , HasCallStack
     )
  => Exp' -> m Ty
typingExp (ENum _)  = return TNat
typingExp (EVar x)  = do
  env <- view kEnv
  return ((env ^. at x) >>= projTy) `rethrowMaybe` (show $ UnknownVariableError x env)
typingExp (EMeasure p) = return TMeasured
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
-- Examine each Range in a given Partition and resolve to a Locus
resolvePartition
  :: ( Has (State TState) sig m
     , Has (Error String) sig m
     , Has (Reader IEnv) sig m
     , Has Trace sig m
     )
  => Partition -> m Locus
resolvePartition = (fst <$>) . resolvePartition'

-- | Look up the Locus record by the Loc reference in the session state.
findLocusByLoc :: HasResolution sig m => Loc -> m Locus
findLocusByLoc loc = do
  (part, (qty, degrees)) <- use (sSt . at loc) `rethrowMaybe`
    show (UnknownLocError loc)
  return Locus {loc, part, qty, degrees}

resolvePartition'
  :: HasResolution sig m => Partition -> m (Locus, [(Range, Range)])
resolvePartition' se' = do
  -- resolve the canonical range names
  rsResolved <- rs `forM` resolveRange
  let locs = [ ((rSe, rSt), loc)
             | (rSe, rSt, ans, loc) <- concat rsResolved, included ans ]
  constraints <- ask @IEnv
  let related = concatMap ("\n\t" ++) . concat $
                [ showRel r1 r2 b | (r1, r2, b, _) <- concat rsResolved ]
  trace $ printf "[resolvePartition] (%s) with %s %s" (show se) (show constraints) related
  case List.nub (snd <$> locs) of
    [] -> throwError $ errInternal related
    [loc] ->
      findLocusByLoc loc <&> (, fst <$> locs)
    ss -> throwError $ errNonunique ss related
  where
    se@(Partition rs) = reduce se'

    -- | an inclusion predicate is satisfied only if it holds under all possible
    -- environment constraints.
    included :: NonEmpty (Maybe Bool, AEnv) -> Bool
    included = all ((== Just True) . fst)

    -- Format
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
            printf "%s %s %s at %s" (showEmitI 0 r1) (mkRelOp rel)
            (showEmitI 0 r2) (showEmitI 0 $ byComma env)


removeTStateByLocus
  :: (Has (State TState) sig m)
  => Locus -> m ()
removeTStateByLocus st@(Locus{loc, part=p, qty}) = do
  sSt %= flip Map.withoutKeys (Set.singleton loc)
  xSt %= Map.map (filter ((/= loc) . snd))
  deleteEmPartition loc (unpackPart p)

-- | Query all ranges related to the given range.
-- Return a list of tuple standing for
-- * matched ranges
-- * statistics of the resolution
-- * the owner locus of the canonical range
-- FIXME: provide "resolveRanges" that instantiates the predicate only once!
resolveRange
  :: ( Has (State TState) sig m
     , Has (Error String) sig m
     , Has (Reader IEnv) sig m
     )
  => Range -> m [(Range, Range, NonEmpty (Maybe Bool, AEnv), Loc)]
resolveRange r@(Range name _ _) = do
  (⊑//) <- (⊑/) -- specialize the predicate using the current constraints
  rlocs <- use (xSt . at name) `rethrowMaybe` (show . UnknownRangeError) r
  return [ (r, r', r ⊑// r', loc)
         | (r', loc) <- rlocs ]

-- | Resolve the ranges using the Range name state and the current constraint
-- environment.  It is strict in that the resolution is considered strict if all
-- constraints are satisfied and the range is a sub-range of only one locus.
resolveRangesStrict :: HasResolution sig m => [Range] -> m [(Range, Range, Loc)]
resolveRangesStrict rs = do
  (∀⊑//) <- (∀⊑/)
  st <- use xSt
  let rslocsM = rs <&> \r -> st Map.!? getRangeName r
  rslocs <- zipWithM (fromMaybeM . errUnknownRange) rs rslocsM
  zipWithM (go (∀⊑//)) rs rslocs
  where
    go cmp rGiven rlFound =
      case filter (cmp rGiven . fst) rlFound of
        [(rFound, lFound)] ->
          pure (rGiven, rFound, lFound)
        []    -> errUnknownRange rGiven
        found -> errAmbiguousRange rGiven found
    errUnknownRange = throwError' . show .UnknownRangeError
    errAmbiguousRange rGiven found =
      throwError' (show (AmbiguousRange rGiven found))

-- | Resolve the ranges using the Range name state and the current constraint
-- environment.  It is strict in that the resolution is considered strict if all
-- constraints are satisfied and the range is a sub-range of only one locus.
resolveRangesStrictIntoLoci ::
  HasResolution sig m => [Range] -> m [(Range, Range, Locus)]
resolveRangesStrictIntoLoci =
  resolveRangesStrict >=> mapM go
  where
    go (r1, r2, l) = findLocusByLoc l <&> (r1, r2, )

resolvePartitions
  :: ( Has (State TState) sig m
     , Has (Error String) sig m
     , Has (Reader IEnv) sig m
     , Has Trace sig m
     )
  => [Partition] -> m Locus
resolvePartitions =
  resolvePartition . Partition . concatMap unpackPart


inferRangeTy
  :: ( Has (State TState) sig m
     , Has (Error String) sig m
     , Has (Reader IEnv) sig m
     , Has Trace sig m)
  => Range -> m (QTy, [Int])
inferRangeTy r =
  go <$>  resolvePartition (Partition [r])
  where
    go Locus{qty, degrees} = (qty, degrees)

--------------------------------------------------------------------------------
-- | Split Typing
--------------------------------------------------------------------------------
-- | Given a partition and a range, compute a split scheme if the range is a
-- part of the partition.
--
-- The returned 'Locus' is the partition covering the range
--
-- For the optional return value, return 'Nothing' if no split needs **on a specific
-- range** needs to be performed, i.e. no codegen needs to be done.
splitScheme
  :: ( Has (Error String) sig m
     , Has (Gensym String) sig m
     , Has (State TState) sig m
     , Has (Gensym Emitter) sig m
     , Has (Reader IEnv) sig m
     , Has Trace sig m
     )
  => Locus
  -> Range
  -> m (Locus, Maybe SplitScheme)
splitScheme s r = errTrace "`splitScheme`" $ do
  splitScheme' s r

-- | Rationale: there's no good reason to split a partition with multiple ranges
-- in entanglement. So, we're safe to reject non-singleton partitions for now.
splitSchemePartition
  :: ( Has (Error String) sig m
     , Has (Gensym String) sig m
     , Has (State TState) sig m
     , Has (Gensym Emitter) sig m
     , Has (Reader IEnv) sig m
     , Has Trace sig m
     )
  => Locus
  -> Partition
  -> m (Locus, Maybe SplitScheme)
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
     , Has (Gensym Emitter) sig m
     , Has (Reader IEnv) sig m
     , Has Trace sig m
     )
  => Locus
  -> Range
  -> m (Locus, Maybe SplitScheme)
splitScheme' s@(Locus{loc, part, qty, degrees}) rSplitTo@(Range to rstL rstR) = do
  -- FIXME: Type checking of `qt` should happen first because splitting an EN
  -- typed partition should not be allowed.
  -- TODO: Is this correct?
  when (isEn qty) $
    throwError'' errSplitEN

  rangeSplit@RangeSplits { rsRsUnchanged, rsRLeft, rsRRight, rsRAffected} <-
    getRangeSplits s rSplitTo
  case NE.nonEmpty (rsRsRemainder rangeSplit) of
    Nothing -> -- | No split!
      return (s, Nothing)

    Just rsRemainder -> do

      let psRemainder = Partition . Identity <$> rsRemainder
          psRemainder' = Partition . List.singleton <$> rsRemainder
          pSplitInto  = Partition [rSplitTo]
      -- | ill-formed partition
      unless (null rsRsUnchanged) $
        throwError'' errInconsistentRemainder

      -- 1. Allocate partitions, break ranges and move them around
      lociRem <- mapM (gensymLoc . rangeVar) rsRemainder
      -- Aux reuses the current loc
      sSt %= (at loc ?~ (pSplitInto, (qty, degrees)))
      sequence_ $ NE.zipWith
        (\locMain pMain -> sSt %= (at locMain ?~ (pMain, (qty, degrees))))
        lociRem psRemainder'

      -- | retrieve all (range, loc) pair associated with the variable `x`
      xRangeLocs <- use (xSt . at to) `rethrowMaybe` errXST
      let xrl =
            -- "split range -> old loc"
            [ (rSplitTo, loc) ] ++
            -- "quotient ranges -> new loci"
            [ (rRemainder, locRem) | rRemainder <- NE.toList rsRemainder
                                   | locRem <- NE.toList lociRem
                                   ] ++
            -- "the rest with the old range removed"
            List.filter ((/= rsRAffected) . fst) xRangeLocs
      -- update the range name state
      xSt %= (at to ?~ xrl)

      -- 2. Generate emit symbols for split ranges
      let locusSplitInto = s{part=pSplitInto}
          lociRemainder  = NE.zipWith updateLocPartOfS lociRem psRemainder

      -- locate EmitData of both range and locus
      edRAffected@EmitData{evBasis=vEmitRMaybe} <- findEm (inj rsRAffected)
      edLAffected@EmitData{evPhaseRef=vPhaseMaybe
                          ,evAmp=vEmitAMaybe} <- findEm (inj loc)
      vEmitR <- findVisitEm evBasis (inj rsRAffected)
      -- delete the range record
      deleteEms [inj rsRAffected]

      -- generate EmitData for new ranges
      edRSplit <- genEmStByRange qty rSplitTo
      let schEdAffected = (rsRAffected, edLAffected, edRAffected)
      let schEdSplit = (rSplitTo,edRSplit)
      schEdRemainders <- forM lociRemainder $ \locRem -> do
        (edLoc, Identity (rRem, edR)) <- genEmStFromLocus locRem
        return (rRem, edLoc, edR)
      return $ ( locusSplitInto
               , Just SplitScheme { schEdAffected, schEdSplit, schEdRemainders })
  where
    updateLocPartOfS l p = s{loc=l, part=p}
    rangeVar (Range x _ _) = x
    -- infoSS :: String = printf
    --   "[splitScheme] from (%s) to (%s)" (show s) (show rSplitTo)
    throwError'' = throwError' . ("[split] " ++)
    -- errUnsupprtedTy = printf
    --   "Splitting a %s partition is unsupported." (show qty)
    errXST = printf
      "No range beginning with %s cannot be found in `xSt`" to
    errSplitEN = "Splitting an EN partition is disallowed!"
    errInconsistentRemainder = printf
      "Splittable partition %s should not include more than one range."
      (showEmit0 part)

-- | Duplicate a phase type by allocating a new reference to its Repr if
-- necessary.
--
-- duplicatePhaseTy
--   :: ( Has (Gensym Emitter) sig m
--      )
--   => Loc -> QTy -> PhaseTy
--   -> m PhaseTy
-- duplicatePhaseTy _ _ PT0 = return PT0
-- duplicatePhaseTy v qt pty@(PTN i (PhaseRef { prBase=vBase, prRepr=_ })) = do
--   -- allocate a new repr variable without allocating a new base one
--   vRepr <- gensym (LBinding (deref v, inj pty))
--   return (PTN i (PhaseRef { prBase=vBase, prRepr=vRepr }))


data RangeSplits = RangeSplits
  { rsRLeft       :: Maybe Range
    -- ^ left remainder
  , rsRRight      :: Maybe Range
    -- ^ right remainder
  , rsRSplitInto  :: Range
    -- ^ resulting range
  , rsRAffected   :: Range
    -- ^ original range that is affected
  , rsRsUnchanged :: [Range]
    -- ^ other ranges untouched
  , rsRsRemainder :: [Range]
    -- ^ remainders introduced by breaking the affected range (left + right)
  }

-- | Compute, in order to split the given range from a resolved partition, which
-- range in the partition needs to be split as well as the resulting quotient
-- ranges.
--
-- Note: this function is entanglement-type-agnostic and works for any kind of
-- partitions regardless of the number of ranges in the partition.
-- Ranges that are kept as is will be put in `rsRsUnchanged`
getRangeSplits
  :: ( Has (Error String) sig m
     , Has (Reader IEnv) sig m
     )
  => Locus -> Range -> m RangeSplits
getRangeSplits s@(Locus{loc, part=p, degrees}) rSplitTo@(Range to rstL rstR) = do
  botHuh <- ($ rSplitTo) <$> isBotI
  case botHuh of
    _ | all (== Just True)  botHuh -> throwError' errBotRx
    _ | all (== Just False) botHuh -> return ()
    _ -> do ienv <- ask @IEnv
            throwError' $ printf "Cannot decide if %s is empty.\nEnv: %s" (show rSplitTo) (show ienv)
  (⊑??) <- (∀⊑/)
  case matched (⊑??) of
    Nothing -> throwError' errImproperRx
    Just (rRemL, _, rRemR, rOrigin, idx)  -> do
      rRemLeft <- contractRange rRemL
      rRemRight <- contractRange rRemR
      let rsRest = removeNth idx (unpackPart p)
      return $ RangeSplits
        { rsRLeft       = rRemLeft
        , rsRRight      = rRemRight
        , rsRSplitInto  = rSplitTo
        , rsRAffected   = rOrigin
        , rsRsUnchanged = rsRest
        , rsRsRemainder = catMaybes [rRemLeft, rRemRight]
        }
  where
    removeNth n l = let (a, b) = splitAt n l in a ++ tail b
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
     , Has (Gensym Emitter) sig m
     , Has (State TState) sig m
     , Has Trace sig m
     , Has (Reader IEnv) sig m
     , Has (Error SCError) sig m
     )
  => Locus
  -> QTy
  -> Range
  -> m ( Locus              -- the finally resolved partition
       , Maybe SplitScheme  -- May split if cast or not
       , Maybe CastScheme   -- May cast or not
       )
splitThenCastScheme s'@Locus{ loc, part, qty=qt1, degrees } qt2 rSplitTo =
  failureAsSCError . errTrace "`splitThenCastScheme`" $
  case (qt1, qt2) of
    (_, _) | isEn qt1 && qt1 == qt2 -> do
      -- same type therefore no cast needed,
      -- do check to see if a split in range is also not needed
      RangeSplits { rsRAffected
                  , rsRsRemainder
                  } <- getRangeSplits s' rSplitTo
      case rsRsRemainder of
        [] -> return (s', Nothing, Nothing)
        _  -> throwError $ SplitENError s' rSplitTo rsRAffected rsRsRemainder
    (_ , _) | not (isEn qt1) && isEn qt2 -> do
      -- casting a smaller type to a larger type
      (sSplit, maySchemeS) <- splitScheme s' rSplitTo
      (sCast, maySchemeC) <- castScheme sSplit qt2
      return (sCast, maySchemeS, maySchemeC)
    (_, _) | qt1 == qt2 -> do
      -- the same type, therefore, only try to compute a split scheme
      (sSplit, maySchemeS) <- splitScheme s' rSplitTo
      return (sSplit, maySchemeS, Nothing)
    _ ->
      throwError' errUndef
   where
     errUndef :: String = printf
       "split-then-cast-scheme is undefined for %s to %s type"
       (show qt1) (show qt2)


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
  => GuardExp -> m (Locus, Partition)
typingGuard (GEPartition s' _) = resolvePartition s' <&> (,s')

-- | Type check if the given partition exists in the context
typingPartitionQTy
  :: ( Has (State TState)  sig m
     , Has (Error String) sig m
     , Has (Reader IEnv) sig m
     , Has Trace sig m
     )
  => Partition -> QTy -> m Locus
typingPartitionQTy s qt = do
  st <- resolvePartition s
  when (qt /= qty st) $ throwError' (errTypeMismatch st)
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
  => Partition -> m Locus
typingPartition s = do
  st@Locus{part=pResolved, qty=qtResolved} <- resolvePartition s
  when (List.sort (unpackPart s) /= List.sort (unpackPart pResolved)) $
    throwError' $ errIncompletePartition st
  return st
  where
    errIncompletePartition st@(Locus{part=p}) =
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
subQ _    TEn   = True
subQ THad THad  = True
subQ THad TEn01 = True
subQ TNor TEn01 = True
subQ TNor TNor  = True
subQ _     _    = False

checkSubtypeQ
  :: Has (Error String) sig m
  => QTy -> QTy -> m ()
checkSubtypeQ t1 t2 =
  unless (subQ t1 t2) $
  throwError $
  "Type mismatch: `" ++ show t1 ++ "` is not a subtype of `" ++ show t2 ++ "`"

-------------------------------------------------------------------------------
-- | Type Manipulation
--------------------------------------------------------------------------------
-- retypePartition1
--   :: ( Has (Error String) sig m
--      , Has (State TState) sig m
--      , Has (Gensym Emitter) sig m
--      )
--   => Locus -> QTy -> m (Maybe (Var, Ty, Var, Ty))
-- retypePartition1 st qtNow =
--   retypePartition st qtNow >>= maybe (return Nothing) go
--   where
--     go CastScheme{ schVsOldEmit=vsPrev
--                  , schVsNewEmit=vsNow} =
--       case (vsPrev, vsNow) of
--         ([(vPrev, tPrev)], [(vNow, tNow)]) ->
--           return $ pure (vPrev, tPrev, vNow, tNow)
--         _ ->
--           throwError @String $ printf "%s and %s contains more than 1 partition!"
--           (show vsPrev) (show vsNow)

-- | Cast the type of a partition to a given qtype, modify the typing state and
-- allocate emit variables.
castScheme
  :: GensymEmitterWithStateError sig m
  => Locus -> QTy -> m (Locus, Maybe CastScheme)
castScheme locus@Locus{loc=locS, part=sResolved, qty, degrees} qtNow =
  case castLocus locus qtNow of
    Left ErrNoCast -> return (locus, Nothing)
    Left ErrInvalidCast ->
      throwError' $ printf "%s cannot be casted into %s." (showEmit0 qty) (showEmit0 qtNow)
    Right locus' -> (locus,) . Just <$> castSchemeUnchecked locus locus'

-- | Calculate the cast scheme between two loci.
-- The cast will happen for sure even if there's actually no cast relation
-- between those two Loci.
castSchemeUnchecked
  :: GensymEmitterWithStateError sig m
  => Locus -> Locus ->m CastScheme
castSchemeUnchecked locus@Locus{qty=schQtFrom} newLocus@Locus{qty=schQtTo} = do
  updateMetaStByLocus newLocus
  schEdsFrom <- findEmsByLocus locus
  schEdsTo   <- regenEmStByLocus locus newLocus
  return CastScheme{schEdsFrom,schEdsTo,schQtFrom,schQtTo}

-- | The same as 'castScheme', for compatibility
retypePartition
  :: ( Has (Error String) sig m
     , Has (State TState) sig m
     , Has (Gensym Emitter) sig m
     )
  => Locus -> QTy -> m (Maybe CastScheme)
retypePartition = (snd <$>) .: castScheme

--------------------------------------------------------------------------------
-- * Merge Typing
--------------------------------------------------------------------------------

matchEmitStates
  :: EmitState -> EmitState -> [(Range, (EmitData, EmitData))]
matchEmitStates es1 es2 =
  filter removeEq . Map.toList $ Map.intersectionWith (,) em1 em2
  where
    removeEq (_, (v1, v2)) = v1 /= v2
    reduceMap = reduceKeys . ripLoc
    reduceKeys = Map.mapKeys reduce
    ripLoc = Map.mapKeys getInl . Map.filterWithKey (\k _ -> isInl k)
    (em1, em2) = (reduceMap es1, reduceMap es2)

matchEmitStatesVars
  :: Has (Error String) sig m
  => EmitState -> EmitState -> m [(Range, ((Var, Ty), (Var, Ty)))]
matchEmitStatesVars es1 es2 =
  sequence [ (r,) <$> liftM2 (,) (byBasis ed1) (byBasis ed2)
           | (r, (ed1, ed2)) <- reds ]
  where
    byBasis = visitEm evBasis
    reds = matchEmitStates es1 es2


-- Given two states compute the correspondence of emitted varaible between two
-- states where 'tsInit' refers to the state before iteration starts and
-- 'tsLoop' is for the state during iteration.
matchStateCorrLoop
  :: Has (Error String) sig m
  => TState -> TState -> AEnv -> m [((Var, Ty), (Var, Ty))]
matchStateCorrLoop tsInit tsLoop env =
  (snd <$>) <$> matchEmitStatesVars esLoop esInit
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
  = do
    matchedRangeAndVars <- matchEmitStatesVars eSt1 eSt2
    (catMaybes <$>) . forM matchedRangeAndVars $ \(r, (v1, v2)) -> do
      (qt1, _) <- getQPTy ts1 r
      (qt2, _) <- getQPTy ts2 r
      when (qt1 /= qt2) $ throwError' "How can they be different?"
      pure $ case qt1 of
        _ | qt1 `elem` [ TEn, TEn01 ] -> Just . MEqual $
            EqualStrategy
            { esRange = r
            , esQTy = qt1
            , esVMain = v1
            , esVAux = v2
            }
        _ -> Nothing
  where
    getQPTy ts r = evalState ts $ inferRangeTy r


-- | Merge the second Locus into the first one
-- FIXME: Check if phase type is correct!
mergeScheme
  :: ( Has (State TState) sig m
     , Has (Error String) sig m
     , Has (Reader IEnv) sig m
     )
  => Locus -- ^ Main
  -> Locus -- ^ Servent
  -> m [MergeScheme]
mergeScheme
  stM'@Locus{loc=locMain, qty=qtMain, degrees=ptysMain}
  stA@Locus{loc=locAux, part=sAux@(Partition rsAux), qty=qtAux, degrees=ptysAuz} = do

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


-- | Given two Loci in EN type where the first is for the body partition and
-- the other one is for the guard partition.
--
mergeLociHadEN
  :: ( Has (State TState) sig m
     , Has (Error String) sig m
     )
  => Locus -> Locus -> m ()
mergeLociHadEN
  stM@Locus{loc=locMain, part=sMain@(Partition rsMain), qty=qtMain, degrees=ptysMain}
  stA@Locus{loc=locAux , part=sAux@(Partition rsAux)  , qty=qtAux , degrees=ptysAux} =
  do
    -- Sanity Check
    unless (qtMain == qtAux && qtAux == TEn) $
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
      (at locMain ?~ (newPartition, (TEn, ptysMain))) -- update main's state
    return ()


--------------------------------------------------------------------------------
-- | Constraints
--------------------------------------------------------------------------------

-- | Collect constraints from specification expressions. Return collected
-- variables as well as interval information associated with.
collectConstraints
  :: ( Has (Error String) sig m
     , Has (Reader TEnv) sig m
     )
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
      ty <- typingExp (EVar v1)
      when (ty /= TNat) $ throwError' (errNotScalar v1 ty)
      modify $ Map.insertWith (++) v1 [intv]

    errNotScalar v ty = printf "%s : %s is not a scalar variable."  v (show ty)
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


-- | Given an Locus for a fragment of a Had guard, match in the current
-- environment for a EN partition to be merged with this Locus.
mergeCandidateHad
  :: ( Has (State TState) sig m
     , Has (Error String) sig m
     , Has (Reader IEnv) sig m
     , Has Trace sig m
     )
  => Locus -> m Locus
mergeCandidateHad st@(Locus{part, qty=THad, degrees}) = do
  ps <- use sSt <&> Map.elems
  matched <- catMaybes <$> forM ps matchMergeable
  case matched of
    [p'] -> resolvePartition p'
    _    -> throwError' $ ambiguousCandidates matched
  where
    [r] = ranges part
    matchMergeable (p'@(Partition rs), (TEn, ptysEN)) = do
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
-- | Helpers
--------------------------------------------------------------------------------
appkEnvWithBds :: Bindings () -> TEnv -> TEnv
appkEnvWithBds bds = kEnv %~ appBds
  where appBds = Map.union $ Map.fromList [(v, inj t) | Binding v t <- bds]

bdTypes :: Bindings () -> [Ty]
bdTypes b = [t | Binding _ t <- b]


-- TODO: Refactor this function to use a locus
-- | Construct from a scratch a new TState containing the given partitons.
tStateFromPartitionQTys
  :: ( Has (Gensym Emitter) sig m
     , Has (Gensym Var) sig m
     , Has (Error String) sig m
     , Has Trace sig m
     )
  => [(Partition, QTy, [Int])] -> m TState
tStateFromPartitionQTys pqts = execState initTState $ do
  forM_ pqts (uncurry3 extendState)

-- | Extend the typing state with a partition and its type, generate emit
-- symbols for every range in the partition and return all emit data
-- the same order as those ranges.
extendState
  :: ( Has (Gensym Emitter) sig m
     , Has (Gensym Var) sig m
     , Has (State TState) sig m
     , Has Trace sig m
     )
  => Partition -> QTy -> [Int] -> m (EmitData, [(Range, EmitData)])
extendState p@Partition{ranges} qt dgrs = do
  trace "* extendState"
  sLoc <- gensymLoc "receiver"
  -- "receive" a new locus
  sSt %= (at sLoc ?~ (p, (qt, dgrs)))
  -- update range state
  let xMap = [ (v, [(r, sLoc)]) | r@(Range v _ _) <- ranges ]
  xSt %= Map.unionWith (++) (Map.fromListWith (++) xMap)
  let sLocus = Locus{loc=sLoc, qty=qt, part=p, degrees=dgrs}
  genEmStFromLocus sLocus

