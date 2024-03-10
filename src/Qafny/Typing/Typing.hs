{-# LANGUAGE
    FlexibleContexts
  , FlexibleInstances
  , LambdaCase
  , MultiParamTypeClasses
  , MultiWayIf
  , NamedFieldPuns
  , ScopedTypeVariables
  , TupleSections
  , TypeApplications
  , TypeFamilies
  #-}


module Qafny.Typing.Typing where

-- | Typing though Fused Effects

-- Effects
import           Control.Carrier.Reader
    (runReader)
import           Control.Carrier.State.Lazy
    (execState)
import           Control.Effect.Catch
import           Control.Effect.Error
    (Error, throwError)
import           Control.Effect.Lens
import           Control.Effect.NonDet
import           Control.Effect.Reader
import           Control.Effect.State
    (State, get, modify)
import           Effect.Gensym
    (Gensym)

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
import           Qafny.TypeUtils
import           Qafny.Typing.Phase           hiding
    (throwError')
import           Qafny.Utils.Utils
    (errTrace, exp2AExp, gensymLoc, rethrowMaybe)

import           Qafny.Utils.EmitBinding

-- Utils
import           Control.Carrier.State.Lazy
    (evalState, runState)
import           Control.Effect.Trace
import           Control.Lens
    (at, (%~), (?~), (^.))
import           Control.Monad
    (forM, forM_, liftM2, mapAndUnzipM, unless, when, zipWithM)
import           Data.Bifunctor
    (Bifunctor (second))
import           Data.Bool
    (bool)
import           Data.Functor
    ((<&>))
import           Data.Functor.Identity
import qualified Data.List                    as List
import           Data.List.NonEmpty
    (NonEmpty (..))
import qualified Data.List.NonEmpty           as NE
import qualified Data.Map.Strict              as Map
import           Data.Maybe
    (catMaybes, isJust, listToMaybe, mapMaybe)
import qualified Data.Set                     as Set
import           Data.Sum
import           GHC.Stack
    (HasCallStack)
import           Qafny.Typing.Error
    (SCError (SplitENError), failureAsSCError, hdlSCError)
import           Text.Printf
    (printf)

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

resolvePartition'
  :: ( Has (State TState) sig m
     , Has (Error String) sig m
     , Has (Reader IEnv) sig m
     , Has Trace sig m
     )
  => Partition -> m (Locus, [(Range, Range)])
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
    [] ->  throwError $ errInternal related
    [loc] -> do
      (part, (qty, degrees)) <- use (sSt . at loc) `rethrowMaybe` (show . UnknownLocError) loc
      trace (printf "Resolved: %s ∈ %s" (show se) (show part))
      return (Locus{loc, part, qty, degrees}, fst <$> locs)
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
  deleteEDPartition loc (unpackPart p)

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
  -- trace $ printf "[splitScheme]\n\tIn: %s %s\n\tOut: %s"
  --   (show s) (show r) (show ans)



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
  when (isEN qty) $ throwError'' errSplitEN
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
      -- ptysRest = uncurry evPhaseTy <$> zip dgrsRest edsRest
      -- ptysMain = ptysRem ++ ptysRest
  let  dgrsMain = (dgrOrigin <$ rsRem) ++ dgrsRest
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
      sSt %= (at loc ?~ (pMain, (qty, dgrsMain))) .
        (at locAux ?~ (pAux, (qty, [dgrOrigin])))
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
      let sMain' = s{part=pMain, degrees=dgrsMain} -- the part that's split _from_
      case rsRem of
        [] -> case qty of
          t | t `elem` [ TEN, TEN01 ] ->
              throwError'' errSplitEN
          _ ->
            -- only split in partition but not in a range,
            -- therefore, no need to duplicate the range-based phases
            let sAux' = s { loc=locAux, part=pAux }
            in return (sAux', Nothing)
        _  -> do
          (vEmitR, vSyms, rPhReprs) <- case qty of
            t | t `elem` [ TNor, THad ] -> do
              -- locate the original range
              vEmitR <- findVisitED evBasis (inj rOrigin)
              -- delete it from the record
              deleteEDs [inj rOrigin]
              -- gensym for each split ranges
              rsEDs <- genEDStSansPhaseByRanges qty (rSplitTo : rsRem)
              vSyms <- mapM (visitED evBasis . snd) rsEDs
              --
              -- FIXME: cobble "genEDStUpdatePhase" with "genEDStSansPhaseByRanges"
              ~eds@(edSplit : edsRem) <-
                forM (rSplitTo : rsRem) (genEDStUpdatePhase dgrOrigin . inj)
              edsRest <- forM rsRest (findED . inj)
              let (ptySplitTo: ptysRem) = evPhaseTy <$> eds
              --
              return (vEmitR, vSyms, (ptySplitTo : ptysRem))
            _    -> throwError'' $ errUnsupprtedTy ++ "\n" ++ infoSS
          let sAux' = Locus { loc=locAux, part=pAux, qty, degrees=[dgrOrigin] }
          let ans = SplitScheme
                { schROrigin = rOrigin
                , schRTo = rSplitTo
                , schRsRem = rsRem
                , schQty = qty
                , schSMain = sMain'
                , schVEmitOrigin = vEmitR
                , schVsEmitAll = vSyms
                }
          -- trace $ printf "[splitScheme (post)] %s" (show ans)
          return (sAux', Just ans)
  where
    infoSS :: String = printf
      "[splitScheme] from (%s) to (%s)" (show s) (show rSplitTo)
    throwError'' = throwError' . ("[split] " ++)
    errUnsupprtedTy = printf
      "Splitting a %s partition is unsupported." (show qty)
    errXST = printf
      "No range beginning with %s cannot be found in `xSt`" to
    errSplitEN = "Splitting an EN partition is disallowed!"

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
  => Locus -> Range -> m RangeSplits
getRangeSplits s@(Locus{loc, part=p, qty, degrees}) rSplitTo@(Range to rstL rstR) = do
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
      let psRest = if isEN qty then [] else removeNth idx degrees
          rsRest = removeNth idx (unpackPart p)
      return $ RangeSplits
        { rsRLeft = rRemLeft
        , rsRRight = rRemRight
        , rsRSplit = rSplitTo
        , rsRFocused = rOrigin
        , rsDFocused = head degrees
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
    (_, _) | isEN qt1 && qt1 == qt2 -> do
      -- same type therefore no cast needed,
      -- do check to see if split is also not needed
      RangeSplits { rsRFocused = rOrigin
                  , rsRsRem = rsRem
                  } <- getRangeSplits s' rSplitTo
      case rsRem of
        [] -> return (s', Nothing, Nothing)
        _  -> throwError $ SplitENError s' rSplitTo (rSplitTo : rsRem)
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
     , Has (Gensym Emitter) sig m
     )
  => Locus -> QTy -> m (Var, Ty, Var, Ty)
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
     , Has (Gensym Emitter) sig m
     )
  => Locus -> QTy -> m (Locus, CastScheme)
castScheme st qtNow = errTrace "`castScheme`" $ do
  let Locus{ loc=locS, part=sResolved, qty=qtPrev, degrees=dgrs } = st
  when (qtNow == qtPrev) $
    throwError @String  $ printf
     "Partition `%s` is of type `%s`. No retyping need to be done."
     (show sResolved) (show qtNow)
  -- Get info based on its previous type!
  let tOldEmit = typingQEmit qtPrev
  let rsOld = unpackPart sResolved
  vsOldEmit <- findVisitEDs evBasis (inj <$> rsOld)
  deleteEDs (inj <$> rsOld)
  let tNewEmit = typingQEmit qtNow
  -- FIXME: Cast phases
  sSt %= (at locS ?~ (sResolved, (qtNow, dgrs)))
  rsEDsNew <- genEDStSansPhaseByRanges qtNow $ unpackPart sResolved
  vsNewEmit <- mapM (visitED evBasis . snd) rsEDsNew
  return ( st { qty=qtNow }
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
     , Has (Gensym Emitter) sig m
     )
  => Locus -> QTy -> m CastScheme
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
  => EmitState -> EmitState -> m [(Range, (Var, Var))]
matchEmitStatesVars es1 es2 =
  sequence [ (r,) <$> liftM2 (,) (byBasis ed1) (byBasis ed2)
           | (r, (ed1, ed2)) <- reds ]
  where
    byBasis = visitED evBasis
    reds = matchEmitStates es1 es2


-- Given two states compute the correspondence of emitted varaible between two
-- states where 'tsInit' refers to the state before iteration starts and
-- 'tsLoop' is for the state during iteration.
matchStateCorrLoop
  :: Has (Error String) sig m
  => TState -> TState -> AEnv -> m [(Var, Var)]
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
        _ | qt1 `elem` [ TEN, TEN01 ] -> Just . MEqual $
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
      pure (s, qt, analyzePhaseSpecDegree . phase <$> pexp)
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
-- Loci in the caller's context.
resolveMethodApplicationArgs
  ::  ( Has (Gensym String) sig m
      , Has (Gensym Emitter) sig m
      , Has (Error String) sig m
      , Has (Reader TEnv) sig m
      , Has (Reader IEnv) sig m
      , Has (State TState) sig m
      , Has Trace sig m
      )
  => [Exp']
  -> MethodType
  -> m (Map.Map Var Range, [Exp'], [(Locus, Maybe SplitScheme, Maybe CastScheme)])
resolveMethodApplicationArgs es
  MethodType { mtSrcParams=srcParams
             , mtInstantiate=instantiator
             } = errTrace "`resolveMethodApplicationArgs`" $ do
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
    getEmitVarsAfterTyCheck part q = errTrace "`getEmitVarsAfterTyCheck`" $ do
      sAndMaySC <- case part of
        Partition [r] -> do
          st <- resolvePartition part
          hdlSCError $ splitThenCastScheme st q r
        _ -> (, Nothing, Nothing) <$> typingPartitionQTy part q
      (sAndMaySC,) <$> (findVisitEDs evBasis (inj <$> unpackPart part) <&> fmap EVar)



-- | Compute the typing state after returning from a method call.
resolveMethodApplicationRets
  ::  ( Has (Error String) sig m
      , Has (State TState) sig m
      , Has (Gensym Var) sig m
      , Has (Gensym Emitter) sig m
      , Has Trace sig m
      )
  => Map.Map Var Range -> MethodType ->  m [Var]
resolveMethodApplicationRets envArgs
  MethodType { mtSrcReturns=retParams
             , mtReceiver=receiver
             } = do
  trace "* resolveMethodApplicationRets"
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


-- | Given an Locus for a fragment of a Had guard match in the current
-- environment for a EN partition to be merged with this stuple.
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
-- | Helpers
--------------------------------------------------------------------------------
-- | Collect all partitions with their types from spec expressions
specPartitionQTys :: [Exp x] -> [(Partition, QTy, [Int])]
specPartitionQTys es =
  [ (p, qty, analyzePhaseSpecDegree . phase <$> specs)
  | (ESpec p qty specs) <- es
  ]


-- Collect all pure variables
collectPureBindings :: [MethodElem] -> [Binding']
collectPureBindings params =  [ Binding v t | MTyPure v t <- params ]

-- Compute types of methods from the toplevel
collectMethodTypes
  :: (Has (Error String) sig m)
  => AST  -> m (Map.Map Var MethodType)
collectMethodTypes a = execState @(Map.Map Var MethodType) Map.empty $
  forM_ a go
  where
    go :: ( Has (Error String) sig m'
          , Has (State (Map.Map Var MethodType)) sig m'
          )
       => Toplevel () -> m' ()
    go (Toplevel (Inl q@(QMethod {}))) = do
      let (idMethod, methodTy) = analyzeMethodType q
      existsMaybe <- (Map.!? idMethod) <$> get @(Map.Map Var MethodType)
      case existsMaybe of
        Just _ ->
          throwError' $ printf "Duplicated definitions of the method %s." idMethod
        _ -> modify (Map.insert idMethod methodTy)
    go _ = pure ()

appkEnvWithBds :: Bindings () -> TEnv -> TEnv
appkEnvWithBds bds = kEnv %~ appBds
  where appBds = Map.union $ Map.fromList [(v, inj t) | Binding v t <- bds]

bdTypes :: Bindings () -> [Ty]
bdTypes b = [t | Binding _ t <- b]


-- | Construct from a scratch a new TState containing the given partitons.
tStateFromPartitionQTys
  :: ( Has (Gensym Emitter) sig m
     , Has (Gensym Var) sig m
     , Has (Error String) sig m
     , Has Trace sig m
     )
  => [(Partition, QTy, [Int])] -> m TState
tStateFromPartitionQTys pqts = execState initTState $ do
  forM_ pqts extendTState'Degree

-- | Extend the typing state with a partition and its type, generate emit
-- symbols for every range in the partition and return all emitted symbols in
-- the same order as those ranges.
extendTState
  :: ( Has (Gensym Emitter) sig m
     , Has (Gensym Var) sig m
     , Has (State TState) sig m
     , Has (Error String) sig m
     , Has Trace sig m
     )
  => Partition -> QTy -> [Int] -> m ([Var], [PhaseTy])
extendTState p@Partition{ranges} qt dgrs = do
  trace "* extendTState"
  sLoc <- gensymLoc "requires"
  sSt %= (at sLoc ?~ (p, (qt, dgrs)))
  let xMap = [ (v, [(r, sLoc)]) | r@(Range v _ _) <- ranges ]
  (edL, rEd) <- genEDStFromLocus sLoc ranges qt dgrs
  let eds = snd <$> rEd
  -- bdsEmit <- genEDStByRangesSansPhase qt (unpackPart p)
  -- ptys <- allocPhaseType (Locus (sLoc, p, (qt, dgrs)))
  vsEmit <- visitEDs evBasis eds
  -- FIXME: redesign dgrs in Locus so that len(dgrs)==1+len(ranges)
  let ptys = mapMaybe evPhaseTy (edL : eds)
  trace "* Die?"
  xSt %= Map.unionWith (++) (Map.fromListWith (++) xMap)
  return (vsEmit, ptys)

extendTState'Degree
  :: ( Has (Gensym Emitter) sig m
     , Has (Gensym Var) sig m
     , Has (State TState) sig m
     , Has (Error String) sig m
     , Has Trace sig m
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


