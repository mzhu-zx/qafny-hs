{-# LANGUAGE
    CPP
  , DataKinds
  , FlexibleContexts
  , FlexibleInstances
  , MultiWayIf
  , NamedFieldPuns
  , RecordWildCards
  , ScopedTypeVariables
  , TupleSections
  , TypeApplications
  , TypeFamilies
  , UndecidableInstances
  #-}

module Qafny.Codegen.Codegen (codegenAST) where
-- | Code Generation through Fused Effects


-- Effects
import qualified Control.Carrier.Error.Church as ErrC
import qualified Control.Carrier.Error.Either as ErrE
import           Control.Carrier.Reader
    (runReader)
import           Control.Carrier.State.Strict
    (runState)
import           Control.Effect.Catch
import           Control.Effect.Error
    (Error, throwError)
import           Control.Effect.Lens
import           Control.Effect.Reader
import           Control.Effect.State
    (State, get, put)
import           Control.Effect.Trace
import           Effect.Gensym
    (Gensym, gensym)

-- Handlers
import qualified Carrier.Gensym.Emit          as GEmit
import           Qafny.Gensym
    (resumeGensym)

-- Utils
import           Control.Lens
    (at, non, (%~), (?~), (^.))
import           Control.Lens.Tuple
import           Control.Monad
    (MonadPlus (mzero), forM, forM_, liftM2, when)

import           Control.Arrow
    ((&&&))
import           Data.Bifunctor
import           Data.Bool
    (bool)
import           Data.Functor
    ((<&>))
import qualified Data.List                    as List
import           Data.List.NonEmpty
    (NonEmpty (..))
import qualified Data.Map.Strict              as Map
import           Data.Maybe
    (catMaybes, mapMaybe)
import qualified Data.Sum                     as Sum
import           Text.Printf
    (printf)

-- Qafny
import           Qafny.Codegen.Phase
    (codegenPhaseLambda, codegenPromotion)
import           Qafny.Config
import           Qafny.Env
import           Qafny.Interval
    (Interval (Interval))
import           Qafny.Partial
    (Reducible (reduce), sizeOfRangeP)
import           Qafny.Syntax.AST
import           Qafny.Syntax.ASTFactory
import           Qafny.Syntax.Emit
    (DafnyPrinter, byLineT, showEmit0, showEmitI)
import           Qafny.Syntax.EmitBinding
import           Qafny.TypeUtils
    (bindingsFromPtys, emitTypeFromDegree, isEN, typingPhaseEmitReprN,
    typingQEmit)
import           Qafny.Typing
    (Promotion (..), PromotionScheme (..), allocAndUpdatePhaseType,
    analyzePhaseSpecDegree, appkEnvWithBds, checkSubtype, checkSubtypeQ,
    collectConstraints, collectMethodTypes, collectPureBindings, extendTState,
    matchEmitStates, matchEmitStatesVars, matchStateCorrLoop, mergeCandidateHad,
    mergeMatchedTState, mergeSTuplesHadEN, mergeScheme, promotionScheme,
    queryPhaseType, removeTStateBySTuple, resolveMethodApplicationArgs,
    resolveMethodApplicationRets, resolvePartition, resolvePartition',
    resolvePartitions, retypePartition, retypePartition1, specPartitionQTys,
    splitScheme, splitSchemePartition, splitThenCastScheme,
    tStateFromPartitionQTys, typingExp, typingGuard, typingPartition,
    typingPartitionQTy)

import           Data.Sum
    (Injection (inj))
import           Qafny.Codegen.Bindings
    (findEmitBindingsFromPartition)
import           Qafny.Codegen.Method
    (codegenMethodParams, genEmitSt)
import           Qafny.Typing.Error
import           Qafny.Utils.EmitBinding
import           Qafny.Utils.Emitter.Compat
    (findEmitRanges)
import           Qafny.Utils.Utils
    (checkListCorr, dumpSt, fst2, gensymLoc, getMethodType, onlyOne, uncurry3)

throwError'
  :: ( Has (Error String) sig m )
  => String -> m a
throwError' = throwError @String . ("[Codegen] " ++)


first3 :: (a -> d) -> (a, b, c) -> (d, b, c)
first3 f (a, b, c) = (f a, b, c)

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
     , Has Trace sig m
     )
  => AST
  -> m ([((Var, TState), Either String Toplevel')], Either String AST)
codegenAST ast = ErrC.runError handleASTError return  $ do
  Configs { stdlibPath=libPath, depth=depth' } <- ask
  let path = concat (replicate depth' "../") ++ libPath
  let prelude = (mkIncludes path <$> includes) ++ imports
  methodMap <- collectMethodTypes ast
  stTops <- local (kEnv %~ Map.union (Sum.inj <$> methodMap)) $ mapM codegenToplevel ast
  let methodOutcomes = mapMaybe methodOnly stTops
  let (_, mainMayFail) = unzip stTops
  let main :: Either String AST = sequence mainMayFail
  let astGened = (injQDafny prelude ++) <$> main <&> (++ injQDafny finale)
  return (methodOutcomes, astGened)
  where
    handleASTError = (return . ([],) . Left)

    methodOnly (qOrM, a) = qOrM <&> (, a)

    injQDafny = (Sum.inj <$>)
    mkIncludes path s =
      QDafny $ "include \"" ++ path ++ "/" ++ s ++ "\""
    includes =
      [ "QPreludeUntyped.dfy"
      , "libraries/src/Collections/Sequences/Seq.dfy"
      -- , "libraries/src/Collections/Sequences/LittleEndianNat.dfy"
      , "libraries/src/NonlinearArithmetic/Power2.dfy"
      , "libraries/src/NonlinearArithmetic/Power.dfy"
      ]
    imports =
      [ QDafny ""
      , QDafny "// target Dafny version: 4.2.0"
      , QDafny "abstract module QafnyDefault {"
      , QDafny "import opened QPreludeUntyped"
      -- , QDafny "import opened LittleEndianNat"
      , QDafny "import opened Seq"
      , QDafny "import opened Power2"
      , QDafny "import opened Power"
      , QDafny "import opened DivMod"
      , QDafny ""
      ]
    finale = [ QDafny "}" ]

codegenToplevel
  :: ( Has (Reader TEnv) sig m
     , Has Trace sig m
     )
  => Toplevel'
  -> m (Maybe (Var, TState), Either String Toplevel')
codegenToplevel t = case unTop t of
  Sum.Inl q@(QMethod idm _ _ _ _ _ ) ->
    bimap (Just . (idm, )) (Sum.inj <$>)  <$> codegenMethod q
  Sum.Inr q -> return (Nothing, pure . Sum.inj $ q)
  where
    codegenMethod =
      runState initTState .
      ErrE.runError .
      codegenToplevel'Method

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
codegenToplevel'Method q@(QMethod vMethod bds rts rqs ens Nothing) = return q
codegenToplevel'Method q@(QMethod vMethod bds rts rqs ens (Just block)) = runWithCallStack q $ do
  -- gather constraints from "requires" clauses
  boundConstraints <- local (appkEnvWithBds bds) $
    collectConstraints rqs

  -- construct the Interval environment
  let iEnv = Map.foldMapWithKey vIntv2IEnv boundConstraints
  trace $ printf "Constraint Sets:\n%s\n" (show boundConstraints)

  -- construct requires, parameters and the method body
  mty <- getMethodType vMethod
  (countMeta, (countEmit, (rbdvsEmitR', rbdvsEmitB), (appetizer, mainCourse))) <-
    local (appkEnvWithBds bds) $
    codegenRequiresAndParams mty `resumeGensym` codegenMethodBody iEnv block

  let (rqsCG, params, stmtsMatchParams) = appetizer
  let blockCG = mainCourse
  dumpSt "Main Course"
  (stmtsMatchEnsures, returns) <- GEmit.evalGensymEmitWith @Emitter countEmit $
    runReader iEnv . codegenMethodReturns $ mty

  ensCG <- codegenEnsures ens

  trace (printf "** %s" (show rbdvsEmitB))
  -- Gensym symbols are in the reverse order!
  let stmtsDeclare = fDecls rbdvsEmitB
  -- let stmtsDeclare = undefined
  let blockStmts = concat
        [ stmtsMatchParams
        , return $ qComment "Forward Declaration"
        , stmtsDeclare
        , [ qComment "Revealing"
          , SDafny "reveal Map();"
          , SDafny "reveal Pow2();"
          -- , SDafny "reveal LittleEndianNat.ToNatRight();"
          ] -- TODO: any optimization can be done here?
        , [ SDafny "" , qComment "Method Definition"]
        , inBlock blockCG
        , stmtsMatchEnsures
        ]
  return $ QMethod vMethod params returns rqsCG ensCG (Just . Block $ blockStmts)
  where

    vIntv2IEnv v' (Interval l r) = [(v', l :| [r])]

    codegenRequiresAndParams mty = do
      trace "* codegenRequiresAndParams"
      (es, ptys) <- codegenRequires rqs
      methodBindings <- codegenMethodParams mty ptys
      stmtsCopy <- genEmitSt
      dumpSt "genEmitSt"
      return (es, methodBindings, stmtsCopy)

    codegenMethodBody iEnv =
      runReader iEnv . -- | TODO: propagate parameter constraints
      runReader TEN .  -- | resolve λ to EN on default
      runReader True .
      -- ((,) <$> genEmitSt <*>) .
      ((dumpSt "begin block") >>) .
      codegenBlock

    -- | Compile the foward declaration of all variables produced in compiling
    -- the body
    fDecls = mapMaybe $ uncurry fDecl


    fDecl :: Emitter -> Var -> Maybe Stmt'
    fDecl (EmBaseSeq _ qt) v' =
      Just $ mkSVar v' (typingQEmit qt)
    fDecl (EmPhaseSeq _ i) v' =
      emitTypeFromDegree i <&> mkSVar v'
    fDecl (EmPhaseBase _) v' =
      Just $ mkSVar v' TNat
    fDecl (EmAnyBinding v' t) _ =
      Just $ mkSVar v' t
    fDecl _ _ = Nothing

    mkSVar :: Var -> Ty -> Stmt'
    mkSVar v ty = SVar (Binding v ty) Nothing

codegenBlock
  :: ( Has (Reader TEnv) sig m
     , Has (State TState)  sig m
     , Has (Error String) sig m
     , Has (Gensym String) sig m
     , Has (Gensym Emitter) sig m
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
     , Has (Gensym Emitter) sig m
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
     , Has (Gensym Emitter) sig m
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
  flip catchError $ \err -> throwError $ err ++ "\nat:\n" ++ showEmitI 4 s

codegenStmt'
  :: ( Has (Reader TEnv) sig m
     , Has (Reader Bool) sig m
     , Has (Reader IEnv) sig m
     , Has (Reader QTy) sig m
     , Has (State TState)  sig m
     , Has (Error String) sig m
     , Has (Gensym String) sig m
     , Has (Gensym Emitter) sig m
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
  (stG'@(STuple (_, _, (qtG, ptysG))), pG) <- typingGuard e
  -- perform a split to separate the focused guard range from parition
  (stG, maySplit) <- splitSchemePartition stG' pG
  stmtsSplit <- codegenSplitEmitMaybe maySplit
  -- resolve and collect partitions in the body of the IfStmt
  -- analogous to what we do in SepLogic
  stB'@(STuple( _, sB, (qtB, ptysB))) <-
    resolvePartitions . leftPartitions . inBlock $ b
  let annotateCastB = qComment $
        printf "Cast Body Partition %s => %s" (show qtB) (show TEN)
  (stmtsCastB, stB) <- case qtB of
    TEN -> return ([], stB')
    _   ->
      (,) . (annotateCastB :) <$> castPartitionEN stB' <*> resolvePartition sB
  -- act based on the type of the guard
  stmts <- case qtG of
    THad -> codegenStmt'If'Had stG stB b
    _    -> undefined
  return $ stmtsSplit ++ stmtsCastB ++ stmts

codegenStmt' s@(SFor {}) =
  codegenStmt'For s

codegenStmt' (SAssert e@(ESpec{})) =
  (SAssert <$>) <$> codegenAssertion e

-- TODO: Handle arguments in the method call in one pass to codegen Repr.
codegenStmt' (SCall x eargs) = do
  mtyMaybe <- asks @TEnv (^. kEnv . at x) <&> (>>= projMethodTy)
  mty <- maybe errNoAMethod return mtyMaybe
  (envArgs, resolvedArgs, rSts) <- resolveMethodApplicationArgs eargs mty
  stmtsSC <- forM rSts codegenStupleSplitCast
  forM_ rSts $ removeTStateBySTuple . fst3
  rets <- resolveMethodApplicationRets envArgs mty
  pure $ concat stmtsSC ++ [SEmit (rets :*:=: EEmit (ECall x resolvedArgs))]
  where
    fst3 (a, _, _) = a
    codegenStupleSplitCast (_, mS, mC) =
      codegenSplitThenCastEmit mS mC
    errNoAMethod = throwError' $
      printf "The variable %s is not referring to a method." x

codegenStmt' s@(SDafny {}) = return [s]

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
     , Has (Gensym Emitter) sig m
     , Has Trace sig m
     )
  => Stmt'
  -> m [Stmt']
codegenStmt'Apply (s :*=: EHad) = do
  r <- case unpackPart s of
    [r] -> return r
    _   -> throwError "TODO: support non-singleton partition in `*=`"
  st@(STuple(_, _, (qt, _))) <- resolvePartition s
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

codegenStmt'Apply
  stmt@(s@(Partition {ranges}) :*=: eLam@(ELambda pbinder _ pexpMaybe _)) = do
  (st'@(STuple (_, _, (qt', _))), corr) <- resolvePartition' s
  qtLambda <- ask
  checkSubtypeQ qt' qtLambda
  -- compute the correspondence between range written and the range in partition
  -- record
  r@(Range _ erLower erUpper) <- case ranges of
    []  -> throwError "Parser says no!"
    [x] -> return x
    _   -> throwError errRangeGt1

  -- do the type cast and split first
  (STuple (_, _, (qt, _)), maySplit, mayCast) <-
    hdlSC st' $ splitThenCastScheme st' qtLambda r
  stmts <- codegenSplitThenCastEmit maySplit mayCast

  -- resolve again for consistency
  (stS', corr') <- resolvePartition' s

  -- handle promotions in phases
  stmtsPhase <- case pexpMaybe of
    Just pexp -> do
      promoteMaybe <- promotionScheme stS' pbinder pexp;
      case promoteMaybe of
        Just promote -> codegenPromotion promote
        Nothing      -> codegenPhaseLambda stS' pbinder pexp
    Nothing   -> pure []

  -- resolve againnnnn for consistency
  (stS', corr') <- resolvePartition' s

  rSt@(Range _ esLower esUpper) <-
    maybe (throwError' (errNotInCorr r corr')) return
    $ lookup (reduce r) (first reduce <$> corr')

  trace $ printf "LEFT: %s, RIGHT: %s" (show r) (show rSt)
  -- | It's important not to use the fully resolved `s` here because the OP
  -- should only be applied to the sub-partition specified in the annotation.
  ~[vEmit] <- findEmitRanges $ unpackPart s
  ((stmts ++) . (stmtsPhase ++) <$>) . putOpt $ case qtLambda of
    TEN -> return [ mkMapCall vEmit ]
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
    hdlSC stuple m  = do
      a <- ErrE.runError @SCError m
      case a of
        -- Left (SplitENError{}) -> return (stuple, Nothing, Nothing)
        Left err -> throwError $ show err
        Right v  -> return v

    errNotInCorr r corr = printf "%s is not in the corr. %s" (show r) (show corr)
    errRangeGt1 :: String
    errRangeGt1 = printf "%s contains more than 1 range no!" (show ranges)

    -- split a sequence into 3 parts and apply the operation 'f' to the second
    -- one.
    splitMap3 v el er f = EOpChained (sliceV v 0 el) $
      (OAdd,) <$> [ callMap f (sliceV v el er)
                  , sliceV v er (cardV v)
                  ]
    bodySplit v el er =  EEmit $ splitMap3 v el er (lambdaUnphase eLamPure)

    lambdaSplit v el er = simpleLambda v (bodySplit v el er)
    mkMapCall v = v ::=: callMap eLamPure (EVar v)
    eLamPure = lambdaUnphase eLam

codegenStmt'Apply (s :*=: EQFT) = undefined

codegenStmt'Apply _ = throwError' "What could possibly go wrong?"

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
     , Has (Gensym Emitter) sig m
     , Has Trace sig m
     )
  => Stmt'
  -> m [Stmt']

codegenStmt'If (SIf e _ b) = do
  -- resolve the type of the guard
  (stG@(STuple (_, _, (qtG, _))), pG) <- typingGuard e
  trace $ printf "Partitions collected from %s:\n%s" (showEmit0 e) (showEmit0 pG)
  -- resolve the body partition
  stB'@(STuple( _, sB, (qtB, _))) <- resolvePartitions . leftPartitions . inBlock $ b
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

codegenStmt'If _ = throwError' "What could go wrong?"

-- | Code Generation of an `If` statement with a Had partition
codegenStmt'If'Had
  :: ( Has (Reader TEnv) sig m
     , Has (State TState)  sig m
     , Has (Error String) sig m
     , Has (Gensym String) sig m
     , Has (Gensym Emitter) sig m
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
  -- 1. duplicate the body partition
  (stmtsDupB, corr) <- dupState sB
  -- 2. codegen the body
  stmtB <- SEmit . SBlock <$> codegenBlock b
  -- TODO: left vs right merge strategy
  (cardMain', cardStash') <- cardStatesCorr corr
  ~[(stmtCard, cardMain), (stmtStash, cardStash)] <-
    forM [cardMain', cardStash'] saveCard
  -- 3. merge duplicated body partitions and merge the body with the guard
  stB <- resolvePartition sB
  stmtsG <- mergeHadGuard stG stB cardMain cardStash
  let stmtsMerge = mergeEmitted corr []
  return $ stmtsDupB ++ [stmtB] ++ [stmtCard, stmtStash] ++ stmtsMerge ++ stmtsG
  where
    saveCard e = do
      v <- gensym "card"
      let stmt :: Stmt' = SVar (Binding v TNat) (Just e)
      pure (stmt, EVar v)


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
     , Has (Gensym Emitter) sig m
     , Has Trace sig m
     )
  => Stmt'
  -> m [Stmt']

codegenStmt'For (SFor idx boundl boundr eG invs (Just seps) body) = do
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
    -- trace $ "stateLoop:\n" ++ show stateLoop
    codegenFinish stateLoop
    -- get @TState >>= trace . ("staetLoop (subst):\n" ++) . show
    pure stmtsBody

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
    invPQtsPre = first3 (reduce . substP [(idx, boundl)]) <$> invPQts

    -- | the postcondtion of one iteration can be computed bys setting the upper
    -- bound to be the index plus one
    -- invPQtsPost = first (reduce . substP [(idx, EVar idx + 1)]) <$> invPQts

    -- | Generate code and state for the precondition after which
    -- | we only need to concern those mentioned by the loop invariants
    codegenInit = do
      stmtsPreGuard <- invPQtsPre `forM` \(sInv, qtInv, _) -> case sInv of
        Partition [rInv] -> do
          stInv <- resolvePartition sInv
          (sInvSplit, maySplit, mayCast) <- hdlSCError $ splitThenCastScheme stInv qtInv rInv
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
          -- A: In this case, I don't want to do casts or splits at this
          -- moment. But this will be a serious limitation given that I haven't
          -- allow explicit casts/splits yet. There's a way to do it by using
          -- λ. However, this falls into the category of undocumented, probably
          -- undefined tricks.
          --
          -- But why would one split and cast a real partition?
          -- If we have a partition made up of two ranges, it's likely that
          -- both ranges are in entanglement, therefore, there's no reasonable
          -- way to split them. To entangle two partitions into one, one should
          -- use a single If statement to perform the initialization.
          --
          -- ------------------------------------------------------------------
          -- Here, I simply allow this by performing NO cast/split.
          pure []
      -- | This is important because we will generate a new state from the loop
      -- invariant and perform both typing and codegen in the new state!
      statePreLoop <- get @TState

      -- | Do type inference with the loop invariant typing state
      stateLoop <- tStateFromPartitionQTys invPQts
      -- trace $ printf "statePreLoop: %s\nstateLoop: %s"  (show statePreLoop) (show stateLoop)

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

codegenStmt'For _ = throwError' "What could possibly go wrong?"



-- | Code generation of the body statements of a for loop construct
codegenFor'Body
  :: ( Has (Reader TEnv) sig m
     , Has (Reader IEnv) sig m
     , Has (Reader QTy) sig m
     , Has (Reader Bool) sig m
     , Has (State TState)  sig m
     , Has (Error String) sig m
     , Has (Gensym String) sig m
     , Has (Gensym Emitter) sig m
     , Has Trace sig m
     )
  => Var   -- ^ index variable
  -> Exp'   -- ^ lower bound
  -> Exp'   -- ^ upper bound
  -> GuardExp   -- ^ guard expression
  -> Block' -- ^ body
  -> STuple -- ^ the partition to be merged into
  -> [Exp'] -- ^ emitted invariants
  -> m [Stmt']
codegenFor'Body idx boundl boundr eG body stSep@(STuple (_, Partition rsSep, (qtSep, _))) newInvs = do
  let psBody = leftPartitions . inBlock $ body
  (stG@(STuple (_, sG, (qtG, _))), pG) <- typingGuard eG
  trace $ printf "The guard partition collected from %s is %s" (showEmit0 eG) (showEmit0 pG)
  trace $ printf "From invariant typing, the guard partition is %s from %s" (showEmit0 pG) (show stG)

  -- ^ FIXME: these two handling of guard state seems ungrounded

  (stmtsPrelude, stmtsBody) <- case qtG of
    THad -> do
      stB'@(STuple (_, sB, (qtB, _))) <- resolvePartitions psBody

      -- It seems that castEN semantics maybe unnecessary with invariant typing?
      (stmtsCastB, stB) <- case qtB of
        _ | isEN qtB -> return ([], stB')
        _            -> (,) <$> castPartitionEN stB' <*> resolvePartition (unSTup stB' ^. _2)

      -- what to do with the guard partition is unsure...
      -- TODO: This comment seems out-of-date
      -- (stmtsDupG, gCorr) <- dupState sG
      ------------------------------------------------------------
      -- Begin compiling the body
      ------------------------------------------------------------
      stateIterBegin <- get @TState
      dumpSt "the beginning of Had for loop"

      let rG = head (unpackPart pG)
      (stGSplited, maySplit) <- splitScheme stG rG
      stmtsSplitG <- codegenSplitEmitMaybe maySplit

      -- Splitting the guard maintains the invariant of the Had part. It remains
      -- to find a merge candidate of this split guard parition at the end of
      -- the loop.

      -- schemeC <- retypePartition stGSplited TEN
      -- let CastScheme { schVsNewEmit=vsEmitG } = schemeC
      -- let vEmitG = head vsEmitG
      -- let cardVEmitG = EEmit . ECard . EVar $ vEmitG
      -- let stmtsInitG =
      --       [ qComment "Retype from Had to EN and initialize with 0"
      --       , (::=:) vEmitG $
      --           EEmit $ EMakeSeq TNat cardVEmitG $ constExp $ ENum 0 ]
      stG' <- resolvePartition (unSTup stGSplited ^. _2)
      stmtsCGHad <- codegenStmt'For'Had stB stG' idx body
      dumpSt "the end of Had for loop"
      stmtsMatchLoopBeginEnd <- codegenMatchLoopBeginEnd . inferTsLoopEnd $ stateIterBegin ^. emitSt

      return ( stmtsCastB -- ++ stmtsDupG -- ++ stmtsInitG
             , stmtsSplitG ++ stmtsCGHad ++ stmtsMatchLoopBeginEnd
             )

    TEN01 -> do
      eSep <- case eG of
        GEPartition _ (Just eSep) -> return eSep
        _                         -> throwError' errNoSep

      -- 1. save the "false" part to a new variable
      vsEmitG <- findEmitRanges $ unpackPart sG
      redFalseG <- genEDStByRangesSansPhase qtG (ranges sG)
      vsEmitGFalse <- mapM (visitEDBasis . snd) redFalseG
      let stmtsSaveFalse = uncurry (stmtAssignSlice (ENum 0) eSep) <$> zip vsEmitGFalse vsEmitG
      let stmtsFocusTrue = stmtAssignSelfRest eSep <$> vsEmitG

      -- save the current emit symbol table for
      stateIterBegin <- get @TState

      let installEmits rEds =
            forM_ rEds $ \(r, ed) -> appendEDSt (inj r) ed

      -- SOLVED?
      -- TODO: I need one way to duplicate generated emit symbols in the split
      -- and cast semantics so that executing the computation above twice will
      -- solve the problem.
      vsEmitSep <-  findEmitRanges rsSep

      -- compile for the 'false' branch with non-essential statements suppressed
      (tsFalse, (stmtsFalse, vsFalse)) <- runState stateIterBegin $ do
        installEmits redFalseG
        local (const False) $ codegenHalf psBody

      -- compile the for body for the 'true' branch
      (tsTrue, (stmtsTrue, vsTrue))  <- runState stateIterBegin $ do
        codegenHalf psBody

      -- compute what's needed to merge those 2 copies
      mSchemes <- mergeMatchedTState tsFalse tsTrue
      stmtsVarsMergeMatched <- codegenMergeScheme mSchemes

      -- I need a way to merge two typing state here.
      put tsFalse

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
    inferTsLoopEnd =  subst [(idx, EVar idx + 1)]
    codegenHalf psBody = do
      -- 2. generate the body statements with the hint that lambda should
      -- resolve to EN01 now
      stmtsBody <- local (const TNor) $ codegenBlock body

      -- 3. Perform merge with merge scheme
      stmtsAndVsMerge <- (concat <$>) $ forM psBody $ \p -> do
        stP <- resolvePartition p
        -- dumpSSt "premerge"
        schemes <- mergeScheme stSep stP
        -- trace $ printf "What's the merge scheme here?\n %s" (show schemes)
        -- dumpSSt "postmerge"
        codegenMergeScheme schemes
      let (stmtsMerge, vsEmitMerge) = unzip stmtsAndVsMerge

      return (inBlock stmtsBody ++ stmtsMerge, vsEmitMerge)

    codegenMatchLoopBeginEnd emitStBegin = do
      -- Next, I need to collect ranges/partitions from the invariant with
      --   [ i := i + 1 ]
      -- Match those ranges with those in [ i := i ] case to compute the
      -- corresponding emitted variables
      --
      -- Use collected partitions and merge it with the absorbed typing state.
      emitStEnd <- (^. emitSt) <$> get @TState
      corrBeginEnd <- matchEmitStatesVars emitStBegin emitStEnd
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
     , Has (Gensym Emitter) sig m
     , Has Trace sig m
     )
  => STuple -> STuple -> Var -> Block'
  -> m [Stmt']
codegenStmt'For'Had stB stG vIdx b = do
  -- 0. extract partition, this will not be changed
  let sB = unSTup stB ^. _2
  -- 1. duplicate the body
  (stmtsDupB, corrB) <- dupState sB
  trace $ ">>>>>\n" ++ showEmitI 4 (byLineT stmtsDupB)
  -- 3. codegen the body
  stmtB <- SEmit . SBlock <$> codegenBlock b

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
  stToBeMerged <- mergeCandidateHad stG
  mayMerge <- mergeScheme stToBeMerged stG
  (stmtsMergeG, vsSkip) <- unzip <$> codegenMergeScheme mayMerge

  -- 4. merge the main body with the stashed
  let stmtsMergeB = mergeEmitted corrB vsSkip


  return $ stmtsDupB ++ [stmtB] ++ stmtsMergeB ++ stmtsMergeG

mergeHadGuard
  :: ( Has (State TState) sig m
     , Has (Error String) sig m
     , Has (Gensym Emitter) sig m
     , Has (Reader IEnv) sig m
     , Has Trace sig m
     )
  => STuple -> STuple -> Exp' -> Exp' -> m [Stmt']
mergeHadGuard = mergeHadGuardWith (ENum 0)


-- | Assume `stG` is a Had guard, cast it into `EN` type and merge it with
-- the partition in`stB`.
--
-- The merge is done by concatenating the representation of generated and the
-- stashed states. Therefore, the number of kets in the generated states depends
-- on the number of kets in the body and that in the stashed body.
--
--
--
mergeHadGuardWith
  :: ( Has (State TState) sig m
     , Has (Error String) sig m
     , Has (Gensym Emitter) sig m
     , Has (Reader IEnv) sig m
     , Has Trace sig m
     )
  => Exp' -> STuple -> STuple -> Exp' -> Exp' -> m [Stmt']
mergeHadGuardWith eBase stG' stB cardBody cardStashed = do
  (_, _, vGENow, tGENow) <- retypePartition1 stG' TEN
  stG <- resolvePartition (unSTup stG' ^. _2)
  mergeSTuplesHadEN stB stG
  return $ hadGuardMergeExp vGENow tGENow cardBody cardStashed eBase

hadGuardMergeExp :: Var -> Ty -> Exp' -> Exp' -> Exp' -> [Stmt']
hadGuardMergeExp vEmit tEmit cardMain cardStash eBase =
  let ~(TSeq tInSeq) = tEmit
  in [ qComment "Merge: Body partition + the Guard partition."
     , (vEmit ::=:) $
       (EEmit . EMakeSeq tInSeq cardStash $ constLambda eBase) +
       (EEmit . EMakeSeq tInSeq cardMain $
         constLambda $ reduce $ EOp2 OAdd eBase (ENum 1))
     ]

codegenMergePhase
  :: ( Has (Gensym Emitter) sig m
     , Has (Error String) sig m
     )
  => PhaseTy -> PhaseTy -> m (PhaseTy, [Stmt'])
codegenMergePhase p PT0 = return (p, [])
codegenMergePhase PT0 p = return (p, [])
codegenMergePhase (PTN n1 pr1) (PTN n2 pr2) = do
   when (n1 /= n2) $
     throwError' "I don't know how to merge two phases of different degrees."
   if | prBase pr1 == prBase pr2 -> do
          let vRepr1 = prRepr pr1
              vRepr2 = prRepr pr2
          return (PTN n1 pr1, [ vRepr1 ::=: (EVar vRepr1 + EVar vRepr2) ])
      | otherwise -> do
          throwError' "Merging phase types of differnt types is unimplemented. "



-- Emit two expressions representing the number of kets in two states in
-- correspondence
cardStatesCorr
  :: ( Has (Error String) sig m )
  => [(Var, Var)]
  -> m (Exp', Exp')
cardStatesCorr ((vStash ,vMain) : _) =
  return ( EEmit . ECard . EVar $ vStash
         , EEmit . ECard . EVar $ vMain)
cardStatesCorr a =
  throwError "State cardinality of an empty correspondence is undefined!"


-- Merge the two partitions in correspondence
mergeEmitted :: [(Var, Var)] -> [Var] -> [Stmt']
mergeEmitted corr excluded =
  [ vMain ::=: EOp2 OAdd (EVar vStash) (EVar vMain)
  | (vMain, vStash) <- corr
  , vMain `notElem` excluded ]


-- | Generate statements that allocate qubits if it's Nor; otherwise, keep the
-- source statement as is.
codegenAlloc
  :: ( Has (Gensym Emitter) sig m
     , Has (Gensym String) sig m
     , Has (State TState)  sig m
     , Has (Error String) sig m
     )
  => Var -> Exp' -> Ty -> m Stmt'
codegenAlloc v e@(EOp2 ONor e1 e2) t@(TQReg _) = do
  let eEmit = EEmit $ EMakeSeq TNat e1 $ constLambda e2
  let rV = Range v (ENum 0) e1
      sV = partition1 rV
  vEmit <- genEDStByRangeSansPhase TNor rV >>= visitEDBasis
  loc <- gensymLoc v
  xSt %= (at v . non [] %~ ((rV, loc) :))
  sSt %= (at loc ?~ (sV, (TNor, [0])))
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
     , Has (Gensym Emitter) sig m
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
     , Has (Gensym Emitter) sig m
     )
  => STuple -> m [Stmt']
castPartitionEN st@(STuple (locS, s, (qtS, _))) = do
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
     , Has (Gensym Emitter) sig m
     , Has (Reader IEnv) sig m
     , Has Trace sig m
     )
  => Partition -> m ([Stmt'], [(Var, Var)])
dupState s' = do
  STuple (locS, s, (qtS, ptys)) <- resolvePartition s'
  let rs = ranges s
  -- generate a set of fresh emit variables as the stashed partition
  -- do not manipulate the `emitSt` here
  vsEmitFresh <- genEDByRangeSansPhase qtS `mapM` rs >>= visitEDsBasis
  -- the only place where state is used!
  vsEmitPrev  <- findEmitBasesByRanges rs
  let comm = qComment "Duplicate"
  let stmts = [ (::=:) vEmitFresh (EVar vEmitPrev)
              | (vEmitFresh, vEmitPrev) <- zip vsEmitFresh vsEmitPrev ]
  return (comm : stmts, zip vsEmitPrev vsEmitFresh)

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
     )
  => Maybe SplitScheme
  -> m [Stmt']
codegenSplitEmitMaybe = maybe (return []) codegenSplitEmit

-- | Generate emit variables and split operations from a given split scheme.
-- FIXME: implement split for phases as well
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
codegenSplitThenCastEmit sS sC = do
  trace "* codegenSplitThenCastEmit"
  (++) <$> codegenSplitEmitMaybe sS <*> codegenCastEmitMaybe sC

--------------------------------------------------------------------------------
-- * Merge Semantics
--------------------------------------------------------------------------------
-- | Merge semantics of a Had qubit into one EN emitted state
-- uses the name of the emitted seq as well as the index name
addENHad1 :: Var -> Exp' -> Stmt'
addENHad1 vEmit idx =
  (::=:) vEmit $
    EOp2 OAdd (EVar vEmit) (EEmit $ ECall "Map" [eLamPlusPow2, EVar vEmit])
  where
    vfresh = "x__lambda"
    eLamPlusPow2 =
      simpleLambda vfresh $
        EOp2 OAdd (EVar vfresh) (EEmit (ECall "Pow2" [idx]))


-- | Multiply the Had coutner by 2
doubleHadCounter :: Var -> Stmt'
doubleHadCounter vCounter =
  (::=:) vCounter $ EOp2 OMul (ENum 2) (EVar vCounter)


-- | Generate from the merge scheme statements to perform the merge and the
-- final result variable.
codegenMergeScheme
  :: ( Has (Gensym Emitter) sig m
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
      vEmitMerged <- findEmitBasisByRange rMerged
      vEmitMain   <- findEmitBasisByRange rMain
      deleteEDs $ inj <$> [rMerged, rMain]
      case (qtMain, qtMerged) of
        (TEN01, TNor) -> do
          -- append the merged value (ket) into each kets in the main value
          vEmitResult <- genEDStByRangeSansPhase qtMain rResult >>= visitEDBasis
          vBind <- gensym "lambda_x"
          let stmt = vEmitResult ::=: callMap ef (EVar vEmitMain)
              ef   = simpleLambda vBind (EVar vBind + EVar vEmitMerged)
          return (stmt, vEmitMain)
        (TEN, THad) -> do
          let (Range _ lBound rBound) = rMain
          let stmtAdd = addENHad1 vEmitMain (reduce (rBound - lBound))
          return (stmtAdd, vEmitMain)
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
-- | Find the representation of the given range
codegenRangeRepr
  :: ( Has (State TState) sig m
     , Has (Error String) sig m
     , Has (Reader IEnv) sig m
     , Has Trace sig m
     )
  => Range -> m Var
codegenRangeRepr r = do
  STuple(_, _, (qt, _)) <- resolvePartition (Partition [r])
  findEmitBasisByRange r


-- | Generate predicates for require clauses
--
-- This introduces constraints and knowledges into the current context.
codegenRequires
  :: ( Has (State TState)  sig m
     , Has (Error String) sig m
     , Has (Gensym String) sig m
     , Has (Gensym Emitter) sig m
     , Has Trace sig m
     )
  => [Exp'] -> m ([Exp'], [PhaseTy])
codegenRequires rqs = do
  trace "* codegenRequires"
  (bimap concat concat . unzip <$>) . forM rqs $ \rq ->
  -- TODO: I need to check if partitions from different `requires` clauses are
  -- indeed disjoint!
    case rq of
      ESpec s qt espec -> do
        let pspec = phase <$> espec
        let dgrs = pspec <&> analyzePhaseSpecDegree
        (vsEmit, ptys) <- extendTState s qt dgrs
        es <- runReader True $ codegenSpecExp (zip vsEmit (unpackPart s)) qt espec ptys
        return (es, ptys)
      _ -> return ([rq], [])

codegenMethodReturns
  :: ( Has (State TState) sig m
     , Has (Gensym Emitter) sig m
     , Has (Error String) sig m
     , Has (Reader IEnv) sig m
     , Has Trace sig m
     )
  => MethodType -> m ([Stmt'], [Binding'])
codegenMethodReturns MethodType{ mtSrcReturns=srcReturns
                               , mtReceiver=receiver
                               } = do
  let pureBds = collectPureBindings srcReturns
      qVars = [ (v, Range v 0 card) | MTyQuantum v card <- srcReturns ]
      inst = receiver $ Map.fromList qVars
  -- perform type checking
  sts <- forM (fst2 <$> inst) (uncurry typingPartitionQTy)
  ptys <- concat <$>forM sts queryPhaseType
  ptysNew <- concat <$> forM sts allocAndUpdatePhaseType
  let (stmtsP, bdsP) = unzip $ pairPhaseTys ptysNew ptys
  (stmtsAssign, bdsRet) <- (unzip . concat <$>) . forM inst $ uncurry3 genAndPairReturnRanges
  return (stmtsAssign ++ stmtsP, pureBds ++ bdsRet ++ bdsP)
  where
    -- genAndPairReturnRanges
    --   :: Partition -> QTy -> m [(Stmt', Binding')]
    genAndPairReturnRanges p qt dgrs = do
      prevBindings <- findEmitBindingsFromPartition p qt
      let prevVars = [ v | Binding v _ <- prevBindings ]
      -- FIXME: remove loc as well!
      deleteEDs (inj<$> ranges p)
      newVars <- genEDStByRangesSansPhase' qt (ranges p) >>= visitEDsBasis
      let emitTy = typingQEmit qt
      pure $ zipWith (pairAndBind emitTy) newVars prevVars
    pairPhaseTys ptysNew ptysPre =
      zipWith pairEachRef (bindingsFromPtys ptysNew) (bindingsFromPtys ptysPre)
    pairEachRef (Binding vNew ty) (Binding vOld _) = pairAndBind ty vNew vOld
    pairAndBind emitTy nv pv = (mkAssignment nv pv, (`Binding` emitTy) nv)


codegenEnsures
  :: ( Has (State TState)  sig m
     , Has (Error String) sig m
     , Has Trace sig m
     )
  => [Exp'] -> m [Exp']
codegenEnsures ens =
  concat <$> forM ens (runReader initIEnv . runReader True  . codegenAssertion)


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
  st@(STuple (_, _, (_, dgrs))) <- typingPartitionQTy s qt
  vsEmit <- findEmitBasesByRanges (ranges s)
  qtys <- queryPhaseType st
  codegenSpecExp (zip vsEmit (unpackPart s)) qt espec qtys
codegenAssertion' e = return [e]

-- | Take in the emit variable corresponding to each range in the partition and the
-- partition type; with which, generate expressions (predicates)
codegenSpecExp
  :: ( Has (Error String) sig m
     , Has (Reader Bool) sig m
     )
  => [(Var, Range)] -> QTy -> [QSpec] -> [PhaseTy] -> m [Exp']
codegenSpecExp vrs p specs ptys = putOpt $
  if isEN p
  then do
    when (length specs /= 1) $ throwError' $ printf "More then one specs!"
    pspec <- onlyOne throwError' (phase <$> specs)
    specPerPartition p (spec (head specs)) pspec
  else do
      -- For `nor` and `had`, one specification is given one per range
    checkListCorr vrs specs
    concat <$> mapM (specPerRange' p) (zip3 vrs specs ptys)
  where
    specPerRange' ty (vr, qspec, pty) =
      specPerRange ty (vr, (spec qspec, phase qspec), pty)
    specPerRange ty ((v, Range _ el er), (SESpecNor idx eBody, pspec), pty) |
      ty `elem` [TNor, THad] =
      -- In x[l .. r]
      -- @
      --   forall idx | 0 <= idx < (r - l) :: xEmit[idx] == eBody
      -- @
      let eSelect x = EEmit (ESelect (EVar x) (EVar idx))
          eBound = Just (eIntv idx (ENum 0) (reduce (er - el)))
          quantifier = EForall (natB idx) eBound . ($ idx)
          eSize = reduce (er - el)
      in do
        ePSpec <- codegenPhaseSpec quantifier eSize pty pspec
        return $
         [ eSize `eEq` EEmit (ECard (EVar v))
         , quantifier (const (eSelect v `eEq` eBody))
         ] ++ ePSpec
    -- specPerRange THad ((v, Range _ el er), (SESpecNor idx eBody, pspec), pty) =
    --   -- In x[l .. r]
    --   -- @
    --   --   forall idx | 0 <= idx < (r - l) :: xEmit[idx] == eBody
    --   -- @
    --   let eSelect x = EEmit (ESelect (EVar x) (EVar idx))
    --       eBound = Just (eIntv idx (ENum 0) (reduce (er - el)))
    --       quantifier = EForall (natB idx) eBound . ($ idx)
    --   in do
    --     ePSpec <- codegenPhaseSpec quantifier pty pspec
    --     return $
    --      [ reduce (er - el) `eEq` EEmit (ECard (EVar v))
    --      , quantifier (const (eSelect v `eEq` eBody))
    --      ] ++ ePSpec
    specPerRange _ (_, (SEWildcard, pspec), pty) =
      return []
    specPerRange _ e  =
      errIncompatibleSpec e

    specPerPartition TEN (SESpecEN idx (Intv l r) eValues) pspec = do
      checkListCorr vrs eValues
      -- In x[? .. ?] where l and r bound the indicies of basis-kets
      -- @
      --   forall idx | l <= idx < r :: xEmit[idx] == eBody
      -- @
      let eBound = Just $ eIntv idx l r
          eSize = reduce (r - l)
          eSelect x = EEmit (ESelect (EVar x) (EVar idx))
          quantifier = EForall (natB idx) eBound . ($ idx)
      pty <- onlyOne throwError' ptys
      ePSpec <- codegenPhaseSpec quantifier eSize pty pspec
      return $ ePSpec ++ concat
        [ [ eSize `eEq` EEmit (ECard (EVar vE))
          , quantifier (const (EOp2 OEq (eSelect vE) eV)) ]
        | ((vE, _), eV) <- zip vrs eValues
        , eV /= EWildcard ]

    specPerPartition
      TEN01
      (SESpecEN01 idxSum (Intv lSum rSum) idxTen (Intv lTen rTen) eValues)
      pspec
       = do
      -- In x[l .. r]
      -- @
      --   forall idxS | lS <= idxS < rS ::
      --   forall idxT | 0 <= idxT < rT - lT ::
      --   xEmit[idxS][idxT] == eBody
      -- @
      -- todo: also emit bounds!
      checkListCorr vrs eValues
      pty <- onlyOne throwError' ptys
      let eBoundSum = Just $ eIntv idxSum lSum rSum
          eSizeSum = reduce (rSum - lSum)
          eForallSum = EForall (natB idxSum) eBoundSum . ($ idxSum)
      ePSpec <- codegenPhaseSpec eForallSum eSizeSum pty pspec
      return . (ePSpec ++) . concat $ do
        ((vE, Range _ el er), eV) <- bimap (second reduce) reduce <$> zip vrs eValues
        when (eV == EWildcard) mzero
        let cardSum = eSizeSum `eEq` EEmit (ECard (EVar vE))
        let rTen' = reduce (er - el)
        let eBoundTen = Just $ eIntv idxTen 0 rTen'
        let cardTen = rTen' `eEq` EEmit (ECard (EVar vE `eAt` EVar idxSum))
        let eForallTen = EForall (natB idxTen) eBoundTen
        let eSel = (EVar vE `eAt` EVar idxSum) `eAt` EVar idxTen
        let eBodys = [ cardTen
                     , EOp2 OEq eSel eV
                     ]
        return $  cardSum : (eForallSum . const . eForallTen <$> eBodys)
    specPerPartition _ e _ = throwError' $
      printf "%s is not compatible with the specification %s"
         (show p) (show e)

    errIncompatibleSpec e = throwError' $
      printf "%s is not compatible with the specification %s"
      (show p) (show e)


-- | Generate a predicates over phases based on the phase type
--
-- FIXME: Here's a subtlety: each range maps to one phase type which in the
-- current specification language is not supported?
codegenPhaseSpec
  :: ( Has (Error String) sig m
     )
  => ((Var -> Exp') -> Exp') -> Exp' -> PhaseTy ->  PhaseExp -> m [Exp']
codegenPhaseSpec _ _ PT0 pe =
  if | pe `elem` [ PhaseZ, PhaseWildCard ] -> return []
     | otherwise ->
       throwError' $ printf "%s is not a zeroth degree predicate." (show pe)
codegenPhaseSpec quantifier eSize (PTN 1 ref) (PhaseOmega eK eN) =
  let assertN = EOp2 OEq eN (EVar (prBase ref))
      assertK idx = EOp2 OEq eK (EVar (prRepr ref) `eAt` EVar idx)
      assertKCard = EOp2 OEq eSize (cardV (prRepr ref))
  in return [assertN, assertKCard, quantifier assertK ]

codegenPhaseSpec quantifier eSize (PTN 2 ref) (PhaseSumOmega (Range v l r) eK eN) =
  let assertN = EOp2 OEq eN (EVar (prBase ref))
      pLength = r - l
      -- FIXME: emit the length of the 2nd-degree range and get the inner
      -- quantifier right
      assertK idx = EForall (Binding v TNat) Nothing $
                    (EOp2 OEq eK ((EVar (prRepr ref) `eAt` EVar v) `eAt` EVar idx))
  in return [assertN, quantifier assertK]
codegenPhaseSpec _ _ (PTN n _) e =
  throwError' $ printf "Invalid %s for %d-degree phase." (show e) n

