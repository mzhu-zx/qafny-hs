{-# LANGUAGE
    CPP
  , DataKinds
  , FlexibleContexts
  , FlexibleInstances
  , IncoherentInstances
  , RecordWildCards
  , ScopedTypeVariables
  , TupleSections
  , TypeApplications
  , TypeFamilies
  , UndecidableInstances
  #-}

module Qafny.Codegen where
-- | Code Generation through Fused Effects


-- Effects
import           Control.Carrier.Reader       (runReader)
import           Control.Effect.Catch
import           Control.Effect.Error         (Error, throwError)
import           Control.Effect.Lens
import           Control.Effect.Reader
import           Control.Effect.State         (State, get, modify, put)
import           Control.Effect.Trace
import           Effect.Gensym                (Gensym, gensym)

-- Handlers
import           Qafny.Gensym                 (resumeGensym)

-- Utils
import           Control.Lens
    ( at
    , non
    , (%~)
    , (?~)
    , (^.)
    )
import           Control.Lens.Tuple
import           Control.Monad
    ( MonadPlus (mzero)
    , forM
    , forM_
    , join
    , unless
    , void
    , when
    )

import           Data.Bifunctor
import           Data.Functor                 ((<&>))
import qualified Data.List                    as List
import           Data.List.NonEmpty           (NonEmpty (..))
import qualified Data.Map.Strict              as Map
import qualified Data.Sum                     as Sum
import           Text.Printf                  (printf)

-- Qafny
import           Control.Carrier.State.Strict (runState)
import           Control.Effect.Fail          (Fail)
import           Control.Exception            (throw)
import           Data.Bool                    (bool)
import           Data.List                    (find)
import           Data.Maybe                   (listToMaybe, maybeToList)
import           Qafny.Config
import           Qafny.Env
import           Qafny.Interval               (Interval (Interval))
import           Qafny.Partial                (Reducible (reduce), sizeOfRangeP)
import           Qafny.Syntax.AST
import           Qafny.Syntax.ASTFactory
import           Qafny.Syntax.Emit
    ( DafnyPrinter (build)
    , showEmit
    , showEmitI
    )
import           Qafny.TypeUtils              (isEN)
import           Qafny.Typing
    ( appkEnvWithBds
    , castScheme
    , checkSubtype
    , checkSubtypeQ
    , collectConstraints
    , collectMethodTypesM
    , extendTState
    , matchEmitStates
    , matchStateCorrLoop
    , mergeMatchedTState
    , mergeSTuples
    , mergeScheme
    , resolvePartition
    , resolvePartition'
    , resolvePartitions
    , retypePartition
    , retypePartition1
    , splitScheme
    , splitThenCastScheme
    , tStateFromPartitionQTys
    , typingExp
    , typingGuard
    , typingPartition
    , typingPartitionQTy
    )
import           Qafny.Utils
    ( dumpSSt
    , findEmitRangeQTy
    , gensymEmitRangeQTy
    , gensymLoc
    , gensymRangeQTy
    , liftPartition
    , modifyEmitRangeQTy
    , rbindingOfRangeQTy
    , removeEmitRangeQTys
    , rethrowMaybe
    , throwError'
    )

--------------------------------------------------------------------------------
-- * Introduction
-- $doc
-- Qafny-to-Dafny translation is organized into two stages:
--
--   * Type Inference/Checking
--   * Code Generation
--
-- The 'Qafny.Codegen' module implements the translation and is responsible of
-- calling typing functions to provide hints and perform type checkings.
-- $doc
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- * Splits
--------------------------------------------------------------------------------
-- put Stmt's anyway
putPure :: Has (Reader Bool) sig m
        => [Stmt'] -> m [Stmt']
putPure = pure

-- put Stmt's only if it's allowed
putOpt :: Has (Reader Bool) sig m => m [a] -> m [a]
putOpt s = do
  bool (pure []) s =<< ask

--------------------------------------------------------------------------------
-- * Codegen
--------------------------------------------------------------------------------
codegenAST
  :: ( Has (Reader Configs) sig m
     , Has (Reader TEnv) sig m
     , Has (State TState)  sig m
     , Has (Error String) sig m
     , Has Trace sig m
     )
  => AST
  -> m AST
codegenAST ast = do
  path <- asks stdlibPath
  let prelude = (mkIncludes path <$> includes) ++ imports
  -- let methods = collectMethodTypesM ast
  let methods = undefined
  main <- local (kEnv %~ Map.union methods) $ mapM codegenToplevel ast
  return $ injQDafny prelude ++ main ++ injQDafny finale
  where
    injQDafny = (Sum.inj <$>)
    mkIncludes path s =
      QDafny $ "include \"" ++ path ++ "/" ++ s ++ "\""
    includes =
      [ "QPreludeUntyped.dfy"
      , "libraries/src/Collections/Sequences/Seq.dfy"
      , "libraries/src/NonlinearArithmetic/Power2.dfy"
      ]
    imports =
      [ QDafny ""
      , QDafny "// target Dafny version: 3.12.0"
      , QDafny "abstract module QafnyDefault {"
      , QDafny "import opened QPreludeUntyped"
      , QDafny "import opened Seq"
      , QDafny "import opened Power2"
      , QDafny ""
      ]
    finale = [ QDafny "}" ]

codegenToplevel
  :: ( Has (Reader TEnv) sig m
     , Has (State TState)  sig m
     , Has (Error String) sig m
     , Has Trace sig m
     )
  => Toplevel'
  -> m Toplevel'
codegenToplevel t = case unTop t of
  Sum.Inl q -> Sum.inj <$> codegenToplevel'Method q
  Sum.Inr q -> return . Sum.inj $ q

codegenToplevel'Method
  :: ( Has (Reader TEnv) sig m
     , Has (State TState)  sig m
     , Has (Error String) sig m
     , Has Trace sig m
     )
  => QMethod ()
  -> m (QMethod ())
-- | The method calling convention is defined as followed.
--
-- [params] __qreg__ variables are replaced in place in the parameter list by
-- the ranges
--
-- [returns] all emitted symbols present in the final emit state will be
-- appended to the original __returns__ list in the order the same as the
-- presence of those in the parameter list
--
-- [rest] do forward declarations in the method body
--
-- TODO: to keep emitted symbols for the same __qreg__ variable in a unique
-- order, sorting those variables should also be the part of the calling
-- convention
codegenToplevel'Method q@(QMethod v bds rts rqs ens Nothing) = return q
codegenToplevel'Method q@(QMethod v bds rts rqs ens (Just block)) = runWithCallStack q $ do
  boundConstraints <- collectConstraints rqs
  trace $ printf "Constraint Sets:\n%s\n" (show boundConstraints)
  let iEnv = Map.foldMapWithKey vIntv2IEnv boundConstraints

  (countMeta, (countEmit, (rbdvsEmitR', rbdvsEmitB), (rqsCG, blockCG))) <-
    local (appkEnvWithBds bds) $
    codegenRequires rqs `resumeGensym` codegenMethodBody iEnv block


  mapFinalEmits <- use emitSt
  ensCG <- codegenEnsures ens

  -- Gensym symbols are in the reverse order!
  let rbdvsEmitR = reverse rbdvsEmitR'
  let bdsCG = genBdsReqs rbdvsEmitR
      bdRets = genBdsRets $ Map.toList mapFinalEmits
      stmtsDeclare = fDecls rbdvsEmitB mapFinalEmits
  let blockStmts = concat
        [ return $ qComment "Forward Declaration"
        , stmtsDeclare
        , [ SDafny "reveal Map();" ] -- TODO: any optimization can be done here?
        , [ SDafny "" , qComment "Method Definition"]
        , inBlock blockCG
        ]
  return $ QMethod v bdsCG (rts ++ bdRets) rqsCG ensCG (Just . Block $ blockStmts)
  where
    vIntv2IEnv v' (Interval l r) = [(v', l :| [r])]

    codegenMethodBody iEnv =
      runReader iEnv . -- | TODO: propagate parameter constraints
      runReader TEN .  -- | resolve λ to EN on default
      runReader True .
      codegenBlock

    -- | All __qreg__ parameters
    vIns = [ vIn | Binding vIn (TQReg _) <- bds ]

    -- | Forward declare all symbols emitted during Codegen except for those to
    -- be put in the __returns__ clause.
    fDecls rbdvsEmitB mapFinalEmits =
       [ SVar (Binding vEmit tEmit) Nothing
       | (RBinding (Range vMeta _ _, tEmit), vEmit) <- rbdvsEmitB
       , vMeta `notElem` vIns ||
         vEmit `notElem` Map.elems mapFinalEmits ]

    -- | For each qreg variable passed into the method, filter its corresponding
    -- symbols emitted during 'codegenRequires' and replace the meta variable in
    -- the method parameter list with the emited variables.
    genBdsReqs rbdvsEmitR = do
        bd@(Binding vIn ty) <- bds
        case ty of
          TQReg _ ->
            [ Binding vEmit tEmit
            | (RBinding (Range vMeta _ _, tEmit), vEmit) <- rbdvsEmitR
            , vMeta == vIn ]
          _    -> return bd

    -- | For each qreg variable passed into the method, look it up in the final
    -- 'emitSt', filter their emit symbols out and add to the __returns__
    -- clause.
    genBdsRets finalEmits =
        [ Binding vEmit tEmit
        | vMeta <- vIns
        , (RBinding (Range vMetaE _ _, tEmit), vEmit) <- finalEmits
        , vMetaE == vMeta]


codegenBlock
  :: ( Has (Reader TEnv) sig m
     , Has (State TState)  sig m
     , Has (Error String) sig m
     , Has (Gensym String) sig m
     , Has (Gensym RBinding) sig m
     , Has (Reader Bool) sig m
     , Has (Reader IEnv) sig m
     , Has (Reader QTy) sig m
     , Has Trace sig m
     )
  => Block ()
  -> m (Block ())
codegenBlock (Block stmts) =
  Block <$> codegenStmts stmts

codegenStmts
  :: ( Has (Reader TEnv) sig m
     , Has (State TState)  sig m
     , Has (Error String) sig m
     , Has (Reader Bool) sig m
     , Has (Gensym String) sig m
     , Has (Gensym RBinding) sig m
     , Has (Reader IEnv) sig m
     , Has Trace sig m
     , Has (Reader QTy) sig m -- hints for λ type resolution
     )
  => [Stmt']
  -> m [Stmt']
codegenStmts [] = return []
codegenStmts (stmt : stmts) = do
  stmts' <- codegenStmt stmt
  (stmts' ++) <$>
    case stmt of
      SVar (Binding v t) eM -> do
        local (kEnv %~ at v ?~ Sum.inj t) $ codegenStmts stmts
      _ -> do
        codegenStmts stmts


codegenStmt
  :: ( Has (Reader TEnv) sig m
     , Has (Reader IEnv) sig m
     , Has (Reader QTy) sig m
     , Has (Reader Bool) sig m
     , Has (State TState)  sig m
     , Has (Error String) sig m
     , Has (Gensym String) sig m
     , Has (Gensym RBinding) sig m
     , Has Trace sig m
     )
  => Stmt'
  -> m [Stmt']
codegenStmt s = runWithCallStack s (codegenStmt' s)

runWithCallStack
  :: ( Has (Error String) sig m
     , DafnyPrinter s
     )
  => s
  -> m b
  -> m b
runWithCallStack s =
  flip catchError $ \err -> throwError' $ err ++ "\nat:\n" ++ showEmitI 4 s

codegenStmt'
  :: ( Has (Reader TEnv) sig m
     , Has (Reader Bool) sig m
     , Has (Reader IEnv) sig m
     , Has (Reader QTy) sig m
     , Has (State TState)  sig m
     , Has (Error String) sig m
     , Has (Gensym String) sig m
     , Has (Gensym RBinding) sig m
     , Has Trace sig m
     )
  => Stmt'
  -> m [Stmt']
codegenStmt' s@(SVar (Binding v t) Nothing)  = return [s]
codegenStmt' s@(SVar (Binding v t) (Just e)) = do
  te <- typingExp e
  -- check if `t` agrees with the type of `e`
  checkSubtype t te
  codegenAlloc v e t <&> (: [])

codegenStmt' s@(_ :*=: _) =
  codegenStmt'Apply s

codegenStmt' (SIf e seps b) = do
  -- resolve the type of the guard
  stG@(STuple (_, _, qtG)) <- typingGuard e
  -- resolve the body partition
  stB'@(STuple( _, sB, qtB)) <- resolvePartitions . leftPartitions . inBlock $ b
  let annotateCastB = qComment $
        printf "Cast Body Partition %s => %s" (show qtB) (show TEN)
  (stmtsCastB, stB) <- case qtB of
    TEN -> return ([], stB')
    _   -> (,) . (annotateCastB :) <$> castPartitionEN stB' <*> resolvePartition sB
  -- act based on the type of the guard
  stmts <- case qtG of
    THad -> codegenStmt'If'Had stG stB b
    _    -> undefined
  return $ stmtsCastB ++ stmts

codegenStmt' s@(SFor {}) =
  codegenStmt'For s

codegenStmt' (SAssert e@(ESpec{})) =
  (SAssert <$>) <$> codegenAssertion e

codegenStmt' (SCall x eargs) =
  undefined

codegenStmt' s = error $ "Unimplemented:\n\t" ++ show s ++ "\n"


--------------------------------------------------------------------------------
-- * Application
--------------------------------------------------------------------------------
-- TODO: make this typesafe by using DataKinds
codegenStmt'Apply
  :: ( Has (Reader TEnv) sig m
     , Has (Reader Bool) sig m
     , Has (Reader IEnv) sig m
     , Has (Reader QTy) sig m
     , Has (State TState)  sig m
     , Has (Error String) sig m
     , Has (Gensym String) sig m
     , Has (Gensym RBinding) sig m
     , Has Trace sig m
     )
  => Stmt'
  -> m [Stmt']
codegenStmt'Apply ((:*=:) s EHad) = do
  r <- case unpackPart s of
    [r] -> return r
    _   -> throwError "TODO: support non-singleton partition in `*=`"
  st@(STuple(_, _, qt)) <- resolvePartition s
  opCast <- opCastHad qt
  -- run split semantics here!
  (stSplit, ssMaybe) <- splitScheme st r
  stmtsSplit <- case ssMaybe of
    Nothing -> return []
    Just ss -> codegenSplitEmit ss
  -- use sSt >>= \s' -> trace $ printf "[precast] sSt: %s" (show s')
  (stmtsSplit ++) <$> castWithOp opCast stSplit THad
  where
    opCastHad TNor = return "CastNorHad"
    opCastHad t = throwError $ "type `" ++ show t ++ "` cannot be casted to Had type"

codegenStmt'Apply stmt@(s@(Partition ranges) :*=: eLam@(EEmit (ELambda {}))) = do
  (st'@(STuple (_, _, qt')), corr) <- resolvePartition' s
  qtLambda <- ask
  checkSubtypeQ qt' qtLambda
  -- compute the correspondence between range on surface ser and the range in
  -- partition record
  r@(Range _ erLower erUpper) <- case ranges of
    []  -> throwError "Parser says no!"
    [x] -> return x
    _   -> throwError errRangeGt1

  -- do the type cast and split first
  ((STuple (_, _, qt)), maySplit, mayCast) <- splitThenCastScheme st' qtLambda r
  stmts <- codegenSplitThenCastEmit maySplit mayCast

  -- resolve again for consistency
  (_, corr') <- resolvePartition' s

  rSt@(Range _ esLower esUpper) <-
    maybe (throwError' (errNotInCorr r corr')) return
    $ lookup (reduce r) (first reduce <$> corr')

  trace $ printf "LEFT: %s, RIGHT: %s" (show r) (show rSt)
  -- | It's important not to use the fully resolved `s` here because the OP
  -- should only be applied to the sub-partition specified in the annotation.
  [vEmit] <- unpackPart s `forM` (`findEmitRangeQTy` qt)
  ((stmts ++) <$>) . putOpt $ case qtLambda of
    TEN -> return $ [ mkMapCall vEmit ]
    TEN01 -> do
      vInner <- gensym "lambda_x"
      let offset = erLower - esLower
      let lambda = lambdaSplit vEmit offset (erUpper - offset)
      return [ vEmit ::=: callMap lambda (EVar vEmit) ]
    TNor -> do
      let offset = erLower - esLower
      let body = bodySplit vEmit offset (erUpper - erLower + offset)
      return [ vEmit ::=: body ]
    _    -> throwError' "I have no idea what to do in this case ..."
  where
    errNotInCorr r corr = printf "%s is not in the corr. %s" (show r) (show corr)
    errRangeGt1 :: String
    errRangeGt1 = printf "%s contains more than 1 range no!" (show ranges)
    -- split a sequence into 3 parts and apply the operation 'f' to the second
    -- one.
    splitMap3 v el er f = EOpChained (sliceV v 0 el) $
      (OAdd,) <$> [ callMap f (sliceV v el er)
                  , sliceV v er (cardV v)
                  ]
    bodySplit v el er =  EEmit $ splitMap3 v el er eLam
    lambdaSplit v el er = EEmit (ELambda v (bodySplit v el er))
    mkMapCall v = v ::=: callMap eLam (EVar v)

codegenStmt'Apply _ = fail "What could possibly go wrong?"

--------------------------------------------------------------------------------
-- * Conditional
--------------------------------------------------------------------------------
codegenStmt'If
  :: ( Has (Reader TEnv) sig m
     , Has (Reader Bool) sig m
     , Has (Reader IEnv) sig m
     , Has (Reader QTy) sig m
     , Has (State TState)  sig m
     , Has (Error String) sig m
     , Has (Gensym String) sig m
     , Has (Gensym RBinding) sig m
     , Has Trace sig m
     )
  => Stmt'
  -> m [Stmt']

codegenStmt'If (SIf e seps b) = do
  -- resolve the type of the guard
  stG@(STuple (_, _, qtG)) <- typingGuard e
  -- resolve the body partition
  stB'@(STuple( _, sB, qtB)) <- resolvePartitions . leftPartitions . inBlock $ b
  let annotateCastB = qComment $
        printf "Cast Body Partition %s => %s" (show qtB) (show TEN)
  (stmtsCastB, stB) <- case qtB of
    TEN -> return ([], stB')
    _   -> (,) . (annotateCastB :) <$> castPartitionEN stB' <*> resolvePartition sB
  -- act based on the type of the guard
  stmts <- case qtG of
    THad -> codegenStmt'If'Had stG stB b
    _    -> undefined
  return $ stmtsCastB ++ stmts

codegenStmt'If _ = fail "What could go wrong?"

-- | Code Generation of an `If` statement with a Had partition
codegenStmt'If'Had
  :: ( Has (Reader TEnv) sig m
     , Has (State TState)  sig m
     , Has (Error String) sig m
     , Has (Gensym String) sig m
     , Has (Gensym RBinding) sig m
     , Has (Reader IEnv) sig m
     , Has (Reader QTy) sig m
     , Has (Reader Bool) sig m
     , Has Trace sig m
     )
  => STuple -> STuple -> Block'
  -> m [Stmt']
codegenStmt'If'Had stG stB' b = do
  -- 0. extract partition, this will not be changed
  let sB = unSTup stB' ^. _2
  -- 1. cast the guard and duplicate the body partition
  (stmtsDupB, corr) <- dupState sB
  -- 2. codegen the body
  stmtB <- SEmit . SBlock <$> codegenBlock b
  -- TODO: left vs right merge strategy
  (cardMain, cardStash) <- cardStatesCorr corr
  -- 3. merge duplicated body partitions and merge the body with the guard
  stB <- resolvePartition sB
  stmtsG <- mergeHadGuard stG stB cardMain cardStash
  let stmtsMerge = mergeEmitted corr
  return $ stmtsDupB ++ [stmtB] ++ stmtsMerge ++ stmtsG

--------------------------------------------------------------------------------
-- * Loop
--------------------------------------------------------------------------------
codegenStmt'For
  :: ( Has (Reader TEnv) sig m
     , Has (Reader Bool) sig m
     , Has (Reader IEnv) sig m
     , Has (Reader QTy) sig m
     , Has (State TState)  sig m
     , Has (Error String) sig m
     , Has (Gensym String) sig m
     , Has (Gensym RBinding) sig m
     , Has Trace sig m
     )
  => Stmt'
  -> m [Stmt']

codegenStmt'For (SFor idx boundl boundr eG invs seps body) = do
  -- statePreLoop: the state before the loop starts
  -- stateLoop:    the state for each iteration
  (stmtsPreGuard, statePreLoop, stateLoop) <- codegenInit
  put stateLoop
  -- generate loop invariants
  newInvs <- forM invs codegenAssertion

  stmtsBody <- local (++ substEnv) $ do
    ask @IEnv >>= trace . printf "Augmented IENV: %s" . show
    stSep <- typingPartition seps -- check if `seps` clause is valid
    stmtsBody <- codegenFor'Body idx boundl boundr eG body stSep (concat newInvs)

    -- update the post-loop typing state
    trace $ "stateLoop:\n" ++ show stateLoop
    codegenFinish stateLoop
    get @TState >>= trace . ("staetLoop (subst):\n" ++) . show
    pure $ stmtsBody

  return $ concat stmtsPreGuard ++ stmtsBody
  where
    -- IEnv for loop constraints
    substEnv = [(idx, boundl :| [boundr - 1])]

    -- AEnv for the precondition of the first iteration
    -- initEnv = [(idx, boundl)]

    -- errInvMtPart = "The invariants contains no partition."
    -- errInvPolypart p = printf
    --   "The loop invariants contains more than 1 partition.\n%s" (show p)

    -- | Partitions and their types collected from the loop invariants
    invPQts = specPartitionQTys invs

    -- | ... partially evaluted with the index variable substituted by the lower
    -- bound
    invPQtsPre = first (reduce . substP [(idx, boundl)]) <$> invPQts

    -- | the postcondtion of one iteration can be computed bys setting the upper
    -- bound to be the index plus one
    -- invPQtsPost = first (reduce . substP [(idx, EVar idx + 1)]) <$> invPQts

    -- | Generate code and state for the precondition after which
    -- | we only need to concern those mentioned by the loop invariants
    codegenInit = do
      stmtsPreGuard <- invPQtsPre `forM` \(sInv, qtInv) -> case sInv of
        Partition [rInv] -> do
          stInv <- resolvePartition sInv
          (sInvSplit, maySplit, mayCast) <- splitThenCastScheme stInv qtInv rInv
          codegenSplitThenCastEmit maySplit mayCast
        _                ->
          -- Q: What is a reasonable split if there are 2 ranges? Would this have
          --    a slightly different meaning? For example, consider a EN partition
          --
          --       { q[0..i], p[0..i] } ↦ { Σ_i . ket(i, i) }
          --
          --    In this case, split will also requires a non-trivial merge?
          --    How to do this?
          --
          throwError' $ printf "More than 1 range %s" (show sInv)
      -- | This is important because we will generate a new state from the loop
      -- invariant and perform both typing and codegen in the new state!
      statePreLoop <- get @TState

      -- | Do type inference with the loop invariant typing state
      stateLoop <- tStateFromPartitionQTys invPQts
      trace $ printf "statePreLoop: %s\nstateLoop: %s"  (show statePreLoop) (show stateLoop)

      -- | pass preLoop variables to loop ones
      stmtsEquiv <- (uncurry mkAssignment <$>) <$> matchStateCorrLoop statePreLoop stateLoop [(idx, boundl)]
      return (stmtsPreGuard ++ [stmtsEquiv], statePreLoop, stateLoop)

    -- update the typing state by plugging the right bound into the index
    -- parameter

    -- [ASSIGN A TICKET HERE]
    -- FIXME: there's a bug here though, if we have something like
    --
    --   for i := 0 to 10
    --      invariant i != 10 ==> <some partition>
    --
    -- This logically valid predicate will cause a problem in generating the
    -- post-condition of the entire loop statement because I only blindly
    -- collect all partitions mentioned by the invariants without considering
    -- the semantics of the logic.
    --
    -- Type states depend solely on those invariant partitions to work
    -- correctly.
    --
    -- Here's an (unimplemented) workaround
    -- - SpecExpressions cannot be mixed with &&, || or not
    -- - SpecExpressions can only appear on the positive position in logical
    --   implication
    -- - The negative position must be a simple propositions about only linear
    --   arithmetic
    --
    -- With those restrictions, I can collect negative position propositions and
    -- solve and decide when to include predicates using the PE engine.
    --
    codegenFinish tsLoop = do
      trace $ show (idx, boundr)
      put . reduce $ subst [(idx, boundr)] tsLoop

codegenStmt'For _ = fail "What could possibly go wrong?"



-- | Code generation of the body statements of a for loop construct
codegenFor'Body
  :: ( Has (Reader TEnv) sig m
     , Has (Reader IEnv) sig m
     , Has (Reader QTy) sig m
     , Has (Reader Bool) sig m
     , Has (State TState)  sig m
     , Has (Error String) sig m
     , Has (Gensym String) sig m
     , Has (Gensym RBinding) sig m
     , Has Trace sig m
     )
  => Var   -- ^ index variable
  -> Exp'   -- ^ lower bound
  -> Exp'   -- ^ upper bound
  -> GuardExp   -- ^ guard expression
  -> Block' -- ^ body
  -> STuple -- ^ the partition to be merged into
  -> [Exp'] -- ^ emitted invariants
  -> m ([Stmt'])
codegenFor'Body idx boundl boundr eG body stSep@(STuple (_, Partition rsSep, qtSep)) newInvs = do
  let psBody = leftPartitions . inBlock $ body
  stG@(STuple (_, sG, qtG)) <- typingGuard eG

  -- ^ FIXME: these two handling of guard state seems ungrounded
  (stmtsPrelude, stmtsBody) <- case qtG of
    THad -> do
      stB'@(STuple (_, sB, qtB)) <- resolvePartitions psBody
      -- It seems that castEN semantics maybe unnecessary with invariant typing?
      (stmtsCastB, stB) <- case qtB of
        _ | isEN qtB -> return ([], stB')
        _            -> (,) <$> castPartitionEN stB' <*> resolvePartition (unSTup stB' ^. _2)

      -- what to do with the guard partition is unsure...
      (stmtsDupG, gCorr) <- dupState sG

      (rL, eConstraint) <- makeLoopRange sG boundl boundr

      -- FIXME: for now, I discard the env for the Had case for backward
      -- compatibility
      stateIterBegin <- get @TState
      local (const initIEnv) $ do
         (stGSplited, schemeSMaybe) <- splitScheme stG rL
         stmtsSplitG <- codegenSplitEmitMaybe schemeSMaybe
         schemeC <- retypePartition stGSplited TEN
         let CastScheme { schVsNewEmit=(~[vEmitG]) } = schemeC
         let cardVEmitG = EEmit . ECard . EVar $ vEmitG
         let stmtsInitG =
               [ qComment "Retype from Had to EN and initialize with 0"
               , (::=:) vEmitG $
                   EEmit $ EMakeSeq TNat cardVEmitG $ constExp $ ENum 0 ]
         stG' <- resolvePartition (unSTup stGSplited ^. _2)
         stmtsCGHad <- codegenStmt'For'Had stB stG' vEmitG idx body
         return $ ( stmtsCastB ++ stmtsDupG ++ stmtsInitG
                  , stmtsSplitG ++ stmtsCGHad
                  )
    TEN01 -> do
      eSep <- case eG of
        GEPartition _ (Just eSep) -> return eSep
        _                         -> throwError' errNoSep

      -- 1. save the "false" part to a new variable
      vsEmitG <- liftPartition (`findEmitRangeQTy` qtG) sG
      rqtvsEmitFalseG <- liftPartition (\r -> ((r, qtG),) <$> r `gensymRangeQTy` qtG) sG
      let vsEmitGFalse = snd <$> rqtvsEmitFalseG
      let stmtsSaveFalse = uncurry (stmtAssignSlice (ENum 0) eSep) <$> zip vsEmitGFalse vsEmitG
      let stmtsFocusTrue = stmtAssignSelfRest eSep <$> vsEmitG

      -- save the current emit symbol table for
      stateIterBegin <- get @TState

      let installEmits bindings =
            forM_ bindings $ \((r, qt), v) -> modifyEmitRangeQTy r qt v

      -- SOLVED?
      -- TODO: I need one way to duplicate generated emit symbols in the split
      -- and cast semantics so that executing the computation above twice will
      -- solve the problem.
      vsEmitSep <- forM rsSep (`findEmitRangeQTy` qtSep)

      -- compile for the 'false' branch with non-essential statements suppressed
      (tsFalse, (stmtsFalse, vsFalse)) <- runState stateIterBegin $ do
        installEmits rqtvsEmitFalseG
        local (const False) $ codegenHalf psBody

      -- compile the for body for the 'true' branch
      (tsTrue, (stmtsTrue, vsTrue))  <- runState stateIterBegin $ do
        codegenHalf psBody

      -- compute what's needed to merge those 2 copies
      mSchemes <- mergeMatchedTState tsFalse tsTrue
      stmtsVarsMergeMatched <- codegenMergeScheme mSchemes

      -- I need a way to merge two typing state here.
      put tsFalse

      let inferTsLoopEnd =  subst [(idx, EVar idx + 1)]
      stmtsMatchLoopBeginEnd <- codegenMatchLoopBeginEnd . inferTsLoopEnd $ stateIterBegin ^. emitSt

      -- 4. put stashed part back
      return ( []
             , concat [ stmtsSaveFalse
                      , stmtsFocusTrue
                      , [qComment "begin false"]
                      , stmtsFalse
                      , [qComment "end false"]
                      , [qComment "begin true"]
                      , stmtsTrue
                      , [qComment "end true"]
                      , [qComment "begin true-false"]
                      , fst <$> stmtsVarsMergeMatched
                      , [qComment "end true-false"]
                      , [ qComment "Match Begin-End"]
                      , stmtsMatchLoopBeginEnd
                      ]
             )
    _    -> throwError' $ printf "%s is not a supported guard type!" (show qtG)
  let innerFor = SEmit $ SForEmit idx boundl boundr newInvs $ Block stmtsBody
  return $ stmtsPrelude ++ [innerFor]
  where
    codegenHalf psBody = do
      -- 2. generate the body statements with the hint that lambda should
      -- resolve to EN01 now
      stmtsBody <- local (const TNor) $ codegenBlock body

      -- 3. Perform merge with merge scheme
      stmtsAndVsMerge <- (concat <$>) $ forM psBody $ \p -> do
        stP <- resolvePartition p
        dumpSSt "premerge"
        schemes <- mergeScheme stSep stP
        trace $ printf "What's the merge scheme here?\n %s" (show schemes)
        dumpSSt "postmerge"
        codegenMergeScheme schemes
      let (stmtsMerge, vsEmitMerge) = unzip stmtsAndVsMerge

      return $ (inBlock stmtsBody ++ stmtsMerge, vsEmitMerge)

    codegenMatchLoopBeginEnd emitStBegin = do
      -- Next, I need to collect ranges/partitions from the invariant with
      --   [ i := i + 1 ]
      -- Match those ranges with those in [ i := i ] case to compute the
      -- corresponding emitted variables
      --
      -- Use collected partitions and merge it with the absorbed typing state.
      emitStEnd <- (^. emitSt) <$> get @TState
      let corrBeginEnd = matchEmitStates emitStBegin emitStEnd
      -- I don't remember the purpose of this line, purely sanity check?
      pure $ uncurry mkAssignment . snd <$> corrBeginEnd


    errNoSep = "Insufficient knowledge to perform a separation for a EN01 partition "
    stmtAssignSlice el er idTo idFrom = (::=:) idTo (sliceV idFrom el er)
    stmtAssignSelfRest eBegin idSelf = stmtAssignSlice eBegin (EEmit . ECard . EVar $ idSelf) idSelf idSelf

-- | Code Generation of a `For` statement with a Had partition
codegenStmt'For'Had
  :: ( Has (Reader TEnv) sig m
     , Has (Reader IEnv) sig m
     , Has (Reader QTy) sig m
     , Has (Reader Bool) sig m
     , Has (State TState)  sig m
     , Has (Error String) sig m
     , Has (Gensym String) sig m
     , Has (Gensym RBinding) sig m
     , Has Trace sig m
     )
  => STuple -> STuple -> Var -> Var -> Block'
  -> m [Stmt']
codegenStmt'For'Had stB stG vEmitG vIdx b = do
  -- 0. extract partition, this will not be changed
  let sB = unSTup stB ^. _2
  -- 1. duplicate the guard
  (stmtsDupB, corrB) <- dupState sB
  -- 3. codegen the body
  stmtB <- SEmit . SBlock <$> codegenBlock b
  -- 4. merge the main body with the stashed
  let stmtsMergeB = mergeEmitted corrB

  -- 5. (Proposed) compute the value for the had ket from the counter and the
  -- body cardinality
  --
  -- (cardMain, cardStash) <- cardStatesCorr corrB
  -- let stmtsUpdateG =
  --       hadGuardMergeExp vEmitG tEmitG cardMain cardStash (EVar vEmitCounter)
  --
  -- TODO: in the current implementation, if the number of kets is changed in
  -- the body, this strategy is incorrect!

  -- 5. (Compromised) double the counter
  let stmtAdd1 = addENHad1 vEmitG vIdx
  mergeSTuples stB stG
  return $ stmtsDupB ++ [stmtB] ++ stmtsMergeB ++ [ stmtAdd1 ]



-- | Assume `stG` is a Had guard, cast it into `EN` type and merge it with
-- the partition in`stB`. The number of kets in the generated states depends on
-- the number of kets in the body and that in the stashed body
mergeHadGuard
  :: ( Has (State TState) sig m
     , Has (Error String) sig m
     , Has (Gensym RBinding) sig m
     , Has (Reader IEnv) sig m
     , Has Trace sig m
     )
  => STuple -> STuple -> Exp' -> Exp' -> m [Stmt']
mergeHadGuard = mergeHadGuardWith (ENum 0)

mergeHadGuardWith
  :: ( Has (State TState) sig m
     , Has (Error String) sig m
     , Has (Gensym RBinding) sig m
     , Has (Reader IEnv) sig m
     , Has Trace sig m
     )
  => Exp' -> STuple -> STuple -> Exp' -> Exp' -> m [Stmt']
mergeHadGuardWith eBase stG' stB cardBody cardStashed = do
  (_, _, vGENow, tGENow) <- retypePartition1 stG' TEN
  stG <- resolvePartition (unSTup stG' ^. _2)
  mergeSTuples stB stG
  return $ hadGuardMergeExp vGENow tGENow cardBody cardStashed eBase

hadGuardMergeExp :: Var -> Ty -> Exp' -> Exp' -> Exp' -> [Stmt']
hadGuardMergeExp vEmit tEmit cardMain cardStash eBase =
  let ~(TSeq tInSeq) = tEmit
  in [ qComment "Merge: Body partition + the Guard partition."
     , (vEmit ::=:) $
       (EEmit . EMakeSeq tInSeq cardMain $
          constExp $ EOp2 OAdd eBase (ENum 1)) +
       (EEmit . EMakeSeq tInSeq cardStash $ constExp eBase)
     ]

-- Emit two expressions representing the number of kets in two states in
-- correspondence
cardStatesCorr
  :: (Has (Error String) sig m)
  => [(Var, Var)]
  -> m (Exp', Exp')
cardStatesCorr ((vStash ,vMain) : _) =
  return ( EEmit . ECard . EVar $ vStash
         , EEmit . ECard . EVar $ vMain)
cardStatesCorr a =
  throwError "State cardinality of an empty correspondence is undefined!"


-- Merge the two partitions in correspondence
mergeEmitted :: [(Var, Var)] -> [Stmt']
mergeEmitted corr =
  [ (::=:) vMain (EOp2 OAdd (EVar vMain) (EVar vStash))
  | (vMain, vStash) <- corr ]


-- | Generate statements that allocate qubits if it's Nor; otherwise, keep the
-- source statement as is.
codegenAlloc
  :: ( Has (Gensym RBinding) sig m
     , Has (Gensym String) sig m
     , Has (State TState)  sig m
     , Has (Error String) sig m
     )
  => Var -> Exp' -> Ty -> m Stmt'
codegenAlloc v e@(EOp2 ONor e1 e2) t@(TQReg _) = do
  let eEmit = EEmit $ EMakeSeq TNat e1 $ constExp e2
  let rV = Range v (ENum 0) e1
      sV = partition1 rV
  vEmit <- gensymEmitRangeQTy rV TNor
  loc <- gensymLoc v
  xSt %= (at v . non [] %~ ((rV, loc) :))
  sSt %= (at loc ?~ (sV, TNor))
  return $ (::=:) vEmit eEmit
codegenAlloc v e@(EOp2 ONor _ _) _ =
  throwError "Internal: Attempt to create a Nor partition that's not of nor type"
codegenAlloc v e _ = return $ (::=:) v e

--------------------------------------------------------------------------------
-- * Cast Semantics
--------------------------------------------------------------------------------
codegenCastEmitMaybe
  :: ( Has (Error String) sig m)
  => Maybe CastScheme -> m [Stmt']
codegenCastEmitMaybe =
  maybe (return []) codegenCastEmit


codegenCastEmit
  :: ( Has (Error String) sig m)
  => CastScheme -> m [Stmt']
codegenCastEmit
  CastScheme{ schVsOldEmit=vsOldEmits
            , schVsNewEmit=vsNewEmit
            , schQtNew=qtNew
            , schQtOld=qtOld
            , schRsCast=rsCast
            } = do
  op <- mkOp qtOld qtNew
  return . concat $
      [ [ qComment $ "Cast " ++ show qtOld ++ " ==> " ++ show qtNew
        , (::=:) vNew $ EEmit (op rCast  `ECall` [EEmit $ EDafnyVar vOld])
        ]
      | (vOld, vNew, rCast) <- zip3 vsOldEmits vsNewEmit rsCast ]
  where
    -- | Consume /from/ and /to/ types and return a function that consumes a
    -- range and emit a specialized cast operator based on the property of the
    -- range passed in
    mkOp TNor TEN   = return $ const "CastNorEN"
    mkOp TNor TEN01 = return $ const "CastNorEN01"
    mkOp TNor THad  = return $ const "CastNorHad"
    mkOp THad TEN01 = return $ \r -> case sizeOfRangeP r of
      Just 1 -> "CastHadEN01'1"
      _      -> "CastHadEN01"
    mkOp _    _     = throwError err
    err :: String = printf "Unsupport cast from %s to %s." (show qtOld) (show qtNew)

-- | Convert quantum type of `s` to `newTy` and emit a cast statement with a
-- provided `op`
castWithOp
  :: ( Has (Error String) sig m
     , Has (State TState) sig m
     , Has (Gensym RBinding) sig m
     )
  => String -> STuple -> QTy -> m [Stmt']
castWithOp op s newTy =
  do
    schemeC <- retypePartition s newTy
    let CastScheme{ schVsOldEmit=vsOldEmits , schVsNewEmit=vsNewEmit} = schemeC
    let partitionTy = unSTup s ^. _3
    -- assemble the emitted terms
    return . concat $
      [ [ qComment $ "Cast " ++ show partitionTy ++ " ==> " ++ show newTy
        , (::=:) vNew $ EEmit (op `ECall` [EEmit $ EDafnyVar vOld])
        ]
      | (vOld, vNew) <- zip vsOldEmits vsNewEmit ]


-- | Cast the given partition to EN type!
castPartitionEN
  :: ( Has (Error String) sig m
     , Has (State TState) sig m
     , Has (Gensym RBinding) sig m
     )
  => STuple -> m [Stmt']
castPartitionEN st@(STuple (locS, s, qtS)) = do
  case qtS of
    TNor -> castWithOp "CastNorEN" st TEN
    THad -> castWithOp "CastHadEN" st TEN
    TEN -> throwError' $
      printf "Partition `%s` is already of EN type." (show st)
    TEN01 -> throwError' $
      printf "Casting %s to TEN is expensive therefore not advised!" (show qtS)

-- | Duplicate the data, i.e. sequences to be emitted, by generating statements
-- that duplicates the data as well as the correspondence between the range
-- bindings, emitted variables from the fresh copy and the original emitted
-- varaibles.
--
-- However, this does not add the generated symbols to the typing environment or
-- modifying the existing bindings!
--
dupState
  :: ( Has (Error String) sig m
     , Has (State TState) sig m
     , Has (Gensym RBinding) sig m
     , Has (Reader IEnv) sig m
     , Has Trace sig m
     )
  => Partition -> m ([Stmt'], [(Var, Var)])
dupState s' = do
  STuple (locS, s, qtS) <- resolvePartition s'
  let rs = unpackPart s
  -- generate a set of fresh emit variables as the stashed partition
  -- do not manipulate the `emitSt` here
  vsEmitFresh <- rs `forM` (`gensymRangeQTy` qtS)
  -- the only place where state is used!
  vsEmitPrev  <- rs `forM` (`gensymEmitRangeQTy` qtS)
  let stmts = [ (::=:) vEmitFresh (EVar vEmitPrev)
              | (vEmitFresh, vEmitPrev) <- zip vsEmitFresh vsEmitPrev ]
  return (stmts, zip vsEmitPrev vsEmitFresh)

-- | Assemble a partition collected from the guard with bounds and emit a
-- verification time assertions that checks the partition is indeed within the
-- bound.
--
-- Precondition: Split has been performed at the subtyping stage so that it's
-- guaranteed that only one range can be in the partition
--
makeLoopRange
  :: Has (Error String) sig m
  => Partition -> Exp' -> Exp' -> m (Range, Exp')
makeLoopRange (Partition [Range r sl sh]) l h =
  return
    ( Range r l h
    , EEmit (EOpChained l [(OLe, sl), (OLt, sh), (OLe, h)])
    )
makeLoopRange s _ _ =
  throwError $
    "Partition `"
      ++ show s
      ++ "` contains more than 1 range, this should be resolved at the typing stage"


--------------------------------------------------------------------------------
-- * Split Semantics
--------------------------------------------------------------------------------
codegenSplitEmitMaybe
  :: ( Has (Error String) sig m
     , Has Trace sig m
     )
  => Maybe SplitScheme
  -> m [Stmt']
codegenSplitEmitMaybe = maybe (return []) codegenSplitEmit

-- | Generate emit variables and split operations from a given split scheme.
codegenSplitEmit
  :: ( Has (Error String) sig m
     )
  => SplitScheme
  -> m [Stmt']
codegenSplitEmit
  ss@SplitScheme { schQty=qty
                 , schROrigin=rOrigin@(Range x left _)
                 , schRTo=rTo
                 , schRsRem=rsRem
                 , schVEmitOrigin=vEmitOrigin
                 , schVsEmitAll=vEmitAll
                 } =
  -- trace ("codegenSplitEmit: " ++ show ss) >>
  case qty of
    t | t `elem` [ TNor, THad, TEN01 ] -> do
      let offset e = reduce $ EOp2 OSub e left
      let stmtsSplit =
            [ [ (vEmitNew ::=:) $
                EEmit (ESlice (EVar vEmitOrigin) (offset el) (offset er))
              , infoWeirdAssertionNeeded
              , SAssert (EOp2 OEq
                          (EEmit (ESlice (EVar vEmitOrigin) (offset el) (offset er)))
                          (EEmit (ESlice (EVar vEmitNew) 0 (reduce (er - el)))))
              ]
            | (vEmitNew, Range _ el er) <- zip (schVsEmitAll ss) (rTo : rsRem) ]
      return . concat $ stmtsSplit
    _    -> throwError @String $ printf "Splitting a %s partition is unsupported." (show qty)
  where
    infoWeirdAssertionNeeded = qComment "I have no idea why this assertion about equality is necessary...."

--------------------------------------------------------------------------------
-- * Split & Cast Semantics
--------------------------------------------------------------------------------
codegenSplitThenCastEmit
  :: ( Has (Error String) sig m
     , Has Trace sig m
     )
  => Maybe SplitScheme
  -> Maybe CastScheme
  -> m [Stmt']
codegenSplitThenCastEmit sS sC =
  (++) <$> codegenSplitEmitMaybe sS <*> codegenCastEmitMaybe sC

--------------------------------------------------------------------------------
-- * Merge Semantics
--------------------------------------------------------------------------------
-- | Merge semantics of a Had qubit into one EN emitted state
-- uses the name of the emitted seq as well as the index name
addENHad1 :: Var -> Var -> Stmt'
addENHad1 vEmit idx =
  (::=:) vEmit $
    EOp2 OAdd (EVar vEmit) (EEmit $ ECall "Map" [eLamPlusPow2, EVar vEmit])
  where
    vfresh = "x__lambda"
    eLamPlusPow2 =
      EEmit . ELambda vfresh $
        EOp2 OAdd (EVar vfresh) (EEmit (ECall "Pow2" [EVar idx]))


-- | Multiply the Had coutner by 2
doubleHadCounter :: Var -> Stmt'
doubleHadCounter vCounter =
  (::=:) vCounter $ EOp2 OMul (ENum 2) (EVar vCounter)


-- | Generate from the merge scheme statements to perform the merge and the
-- final result variable.
codegenMergeScheme
  :: ( Has (Gensym RBinding) sig m
     , Has (Gensym String) sig m
     , Has (State TState) sig m
     , Has (Error String) sig m
     )
  => [MergeScheme] -> m [(Stmt', Var)]
codegenMergeScheme = mapM $ \scheme -> do
  case scheme of
    MMove -> throwError' "I have no planning in solving it here now."
    MJoin JoinStrategy { jsQtMain=qtMain, jsQtMerged=qtMerged
                       , jsRResult=rResult, jsRMerged=rMerged, jsRMain=rMain
                       } -> do
      vEmitResult <- gensymEmitRangeQTy rResult qtMain
      vEmitMerged <- findEmitRangeQTy rMerged qtMerged
      vEmitMain   <- findEmitRangeQTy rMain qtMain
      removeEmitRangeQTys [(rMerged, qtMerged), (rMain, qtMain)]
      case (qtMain, qtMerged) of
        (TEN01, TNor) -> do
          -- append the merged value (ket) into each kets in the main value
          vBind <- gensym "lambda_x"
          let stmt = vEmitResult ::=: callMap ef (EVar vEmitMain)
              ef   = EEmit (ELambda vBind (EVar vBind + EVar vEmitMerged))
          return (stmt, vEmitMain)
        _             -> throwError' $ printf "No idea about %s to %s conversion."
    MEqual EqualStrategy { esRange = r, esQTy = qt
                         , esVMain = v1, esVAux = v2 } -> do
      -- This is all about "unsplit".
      case qt of
        TNor ->
          -- no "unsplit" should happen here!
          return (qComment "TNor has nothing to be merged!", v1)
        THad ->
          throwError' $ printf "This type (%s) cannot be handled: (%s)" (show qt) (show r)
        _ | qt `elem` [ TEN01, TEN ] ->
          -- TEN01 is emitted as seq<seq<nat>> representing Sum . Tensor,
          -- TEN   is emitted as seq<nat>      representing Sum . Tensor,
          -- It suffices to simply concat them
          pure $ (merge3 v1 v1 v2, v1)
        _ -> throwError' "This pattern shoule be complete!"
  where
    merge3 vS vRF vRT = vS ::=: (EVar vRF + EVar vRT)


--------------------------------------------------------------------------------
-- * Specification Related
--------------------------------------------------------------------------------

codegenRequires
  :: ( Has (State TState)  sig m
     , Has (Error String) sig m
     , Has (Gensym String) sig m
     , Has (Gensym RBinding) sig m
     -- , Has (Writer [(String, Range)]) sig m
     )
  => [Exp'] -> m [Exp']
codegenRequires rqs = forM rqs $ \rq ->
  -- TODO: I need to check if partitions from different `requires` clauses are
  -- indeed disjoint!
  case rq of
    ESpec s qt espec -> do
      vsEmit <- extendTState s qt
      (ands <$>) . runReader True $ codegenSpecExp (zip vsEmit (unpackPart s)) qt espec
    _ -> return rq

codegenEnsures
  :: ( Has (State TState)  sig m
     , Has (Error String) sig m
     , Has Trace sig m
     )
  => [Exp'] -> m [Exp']
codegenEnsures ens =
  (ands <$>) <$> forM ens (runReader initIEnv . runReader True  . codegenAssertion)


codegenAssertion
  :: ( Has (State TState)  sig m
     , Has (Error String) sig m
     , Has (Reader IEnv) sig m
     , Has (Reader Bool) sig m
     , Has Trace sig m
     )
  => Exp' -> m [Exp']
codegenAssertion e = runWithCallStack e (codegenAssertion' e)

-- | Take in an /assertional/ expression, perform type check and emit
-- corresponding expressions
--
-- TODO: Would it be better named as _checkAndCodegen_?
codegenAssertion'
  :: ( Has (State TState)  sig m
     , Has (Error String) sig m
     , Has (Reader IEnv) sig m
     , Has (Reader Bool) sig m
     , Has Trace sig m
     )
  => Exp' -> m [Exp']
codegenAssertion' (ESpec s qt espec) = do
  st <- typingPartitionQTy s qt
  vsEmit <- unpackPart s `forM` (`findEmitRangeQTy` qt)
  codegenSpecExp (zip vsEmit (unpackPart s)) qt espec
codegenAssertion' e = return [e]

-- | Take in the emit variable corresponding to each range in the partition and the
-- partition type; with which, generate expressions (predicates)
codegenSpecExp
  :: ( Has (Error String) sig m
     , Has (Reader Bool) sig m
     )
  => [(Var, Range)] -> QTy -> SpecExp' -> m [Exp']
codegenSpecExp vrs p e = putOpt $
  case (p, e) of
    (_, SEWildcard) -> return []
    (TNor, SESpecNor idx es) -> do
      checkListCorr vrs es
      -- In x[l .. r]
      -- @
      --   forall idx | 0 <= idx < (r - l) :: xEmit[idx] == eBody
      -- @
      let eSelect x = EEmit (ESelect (EVar x) (EVar idx))
      return . concat $
        [ [ reduce (er - el) `eEq` EEmit (ECard (EVar v))
          , EForall (natB idx) eBound (eSelect v `eEq` eBody)
          ]
        | ((v, Range _ el er), eBody) <- zip vrs es
        , let eBound = Just (eIntv idx (ENum 0) (reduce (er - el))) ]
    (TEN, SESpecEN idx (Intv l r) eValues) -> do
      checkListCorr vrs eValues
      -- In x[? .. ?] where l and r bound the indicies of basis-kets
      -- @
      --   forall idx | l <= idx < r :: xEmit[idx] == eBody
      -- @
      let eBound = Just $ eIntv idx l r
      let eSelect x = EEmit (ESelect (EVar x) (EVar idx))
      return . concat $
        [ [ r `eEq` EEmit (ECard (EVar vE))
          , EForall (natB idx) eBound (EOp2 OEq (eSelect vE) eV) ]
        | ((vE, _), eV) <- zip vrs eValues
        , eV /= EWildcard ]
      -- In x[l .. r]
      -- @
      --   forall idxS | lS <= idxS < rS ::
      --   forall idxT | 0 <= idxT < rT - lT ::
      --   xEmit[idxS][idxT] == eBody
      -- @
    (TEN01, SESpecEN01 idxSum (Intv lSum rSum) idxTen (Intv lTen rTen) eValues) -> do
      -- todo: also emit bounds!
      checkListCorr vrs eValues
      return . concat $ do
        ((vE, Range _ el er), eV) <- bimap (second reduce) reduce <$> zip vrs eValues
        when (eV == EWildcard) mzero
        let eBoundSum = Just $ eIntv idxSum lSum rSum
        let cardSum = rSum `eEq` EEmit (ECard (EVar vE))
        let rTen = reduce (er - el)
        let eBoundTen = Just $ eIntv idxTen 0 rTen
        let cardTen = rTen `eEq` EEmit (ECard (EVar vE `eAt` EVar idxSum))
        let eForallSum = EForall (natB idxSum) eBoundSum
        let eForallTen = EForall (natB idxTen) eBoundTen
        let eSel = (EVar vE `eAt` EVar idxSum) `eAt` EVar idxTen
        let eBodys = [ cardTen
                     , (EOp2 OEq eSel eV)
                     ]
        return $ cardSum : ((eForallSum . eForallTen) <$> eBodys)
    _ -> throwError' $ printf "%s is not compatible with the specification %s"
         (show p) (show e)

checkListCorr
  :: ( Has (Error String) sig m
     , Show a
     , Show b
     )
  => [a] -> [b] -> m ()
checkListCorr vsEmit eValues =
  unless (length vsEmit == length eValues) $
    throwError' $ printf
      "The number of elements doesn't agree with each other: %s %s"
      (show vsEmit) (show eValues)



--------------------------------------------------------------------------------
instance (Has (Error String) sig m, Monad m) => MonadFail m where
  fail = throwError
