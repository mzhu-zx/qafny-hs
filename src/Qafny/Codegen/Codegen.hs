{-# LANGUAGE
    DataKinds
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
import           Control.Effect.Lens
import           Qafny.Effect

-- Handlers
import qualified Carrier.Gensym.Emit          as GEmit
import           Qafny.Gensym
    (resumeGensym)

-- Utils
import           Control.Lens
    (at, non, (%~), (?~), (^.))
import           Control.Monad
    (forM, forM_, unless)

import           Data.Bifunctor
import           Data.Functor
    ((<&>))
import           Data.Functor.Identity
import           Data.List.NonEmpty
    (NonEmpty (..))
import qualified Data.Map.Strict              as Map
import           Data.Maybe
    (mapMaybe)
import qualified Data.Sum                     as Sum
import           Text.Printf
    (printf)

-- Qafny
import           Qafny.Codegen.Utils
    (runWithCallStack)

import           Qafny.Config
import           Qafny.Interval
    (Interval (Interval))
import           Qafny.Partial
    (Reducible (reduce))
import           Qafny.Syntax.AST
import           Qafny.Syntax.ASTFactory
import           Qafny.Syntax.Emit
    (byLineT, showEmit0, showEmitI)
import           Qafny.Syntax.EmitBinding
import           Qafny.Syntax.IR
import           Qafny.Typing
    (appkEnvWithBds, checkSubtype, checkSubtypeQ, collectConstraints,
    matchEmitStatesVars, matchStateCorrLoop, mergeCandidateHad, mergeLociHadEN,
    mergeMatchedTState, mergeScheme, removeTStateByLocus, resolvePartition,
    resolvePartition', resolvePartitions, retypePartition1, splitScheme,
    splitSchemePartition, splitThenCastScheme, tStateFromPartitionQTys,
    typingExp, typingGuard, typingPartition)
import           Qafny.Typing.Utils
    (emitTypeFromDegree, isEn)

import           Data.Sum
    (Injection (inj))
import           Qafny.Codegen.Common
    (codegenAssignEmitData)
import           Qafny.Codegen.Lambda
    (codegenLambdaEntangle, codegenUnaryLambda)
import           Qafny.Codegen.Method
    (codegenMethodParams, codegenMethodReturns, genEmitSt)
import           Qafny.Codegen.Phase
    (codegenApplyQft)
import           Qafny.Codegen.Predicates
    (codegenAssertion, codegenEnsures, codegenRequires)
import           Qafny.Codegen.SplitCast      hiding
    (throwError')
import           Qafny.Typing.Error
import           Qafny.Typing.Method
    (collectMethodTypes, resolveMethodApplicationArgs,
    resolveMethodApplicationRets)
import           Qafny.Typing.Predicates
    (dropSignatureSpecs, wfSignatureFromPredicates)
import           Qafny.Typing.Range
    (areRangesEquiv)
import           Qafny.Utils.EmitBinding
import           Qafny.Utils.TraceF
    (Traceable (tracef))
import           Qafny.Utils.Utils
    (both, bothM, dumpSt, gensymLoc, getMethodType)

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


throwError'
  :: ( Has (Error String) sig m )
  => String -> m a
throwError' = throwError @String . ("[Codegen] " ++)

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
    handleASTError = return . ([],) . Left

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
      (es, eds) <- codegenRequires rqs
      stmtsCopy <- genEmitSt
      dumpSt "genEmitSt"
      return (es, codegenMethodParams mty eds, stmtsCopy)

    codegenMethodBody iEnv =
      runReader iEnv . -- | TODO: propagate parameter constraints
      runReader TEn .  -- | resolve λ to EN on default
      runReader True .
      -- ((,) <$> genEmitSt <*>) .
      (dumpSt "begin block" >>) .
      codegenBlock

    -- | Compile the foward declaration of all variables produced in compiling
    -- the body
    fDecls = mapMaybe $ uncurry fDecl


    fDecl :: Emitter -> Var -> Maybe Stmt'
    fDecl (EmBaseSeq _ ty) v' =
      Just $ mkSVar v' ty
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
  (stG'@Locus{qty=qtG, degrees=ptysG}, pG) <- typingGuard e
  -- perform a split to separate the focused guard range from parition
  (stG, maySplit) <- splitSchemePartition stG' pG
  let stmtsSplit = codegenSplitEmitMaybe maySplit
  -- resolve and collect partitions in the body of the IfStmt
  -- analogous to what we do in SepLogic
  stB'@Locus{part=sB, qty=qtB, degrees=ptysB} <-
    resolvePartitions . leftPartitions . inBlock $ b
  let annotateCastB = qComment $
        printf "Cast Body Partition %s => %s" (show qtB) (show TEn)
  (stmtsCastB, stB) <- case qtB of
    TEn -> return ([], stB')
    _   ->
      (,) . (annotateCastB :) <$> castPartitionEN stB' <*> resolvePartition sB
  -- act based on the type of the guard
  stmts <- case qtG of
    THad -> codegenStmt'If'Had stG stB b
    _    -> undefined
  return $ stmtsSplit ++ stmtsCastB ++ stmts

codegenStmt' s@(SFor {}) =
  codegenStmt'For s

codegenStmt' (SAssert e) =
  (SAssert <$>) <$> codegenAssertion e

-- TODO: Handle arguments in the method call in one pass to codegen Repr.
codegenStmt' (SCall x eargs) = do
  mtyMaybe <- asks @TEnv (^. kEnv . at x) <&> (>>= projMethodTy)
  mty <- maybe errNoAMethod return mtyMaybe
  (rMap, pureArgs, qArgs, schemes, loci) <-
    resolveMethodApplicationArgs eargs mty
  stmtsSC <- forM schemes $ uncurry codegenSplitThenCastEmit
  -- because locis has been called, their type are no longer accurate. the
  -- actual type is then extracted from the method's `ensures` clauses
  forM_ loci removeTStateByLocus
  rets <- resolveMethodApplicationRets rMap mty
  pure $ concat stmtsSC ++
    [SEmit (fsts rets :*:=: [EEmit (ECall x (pureArgs ++ qArgs))])]
  where
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
    _   -> throwError' "TODO: support non-singleton partition in `*=`"
  st@Locus{qty=qt} <- resolvePartition s
  opCast <- opCastHad qt
  -- run split semantics here!
  (stSplit, ssMaybe) <- splitScheme st r
  let stmtsSplit = maybe [] codegenSplitEmit ssMaybe
  (stmtsSplit ++) <$> castWithOp opCast stSplit THad
  where
    opCastHad TNor = return "CastNorHad"
    opCastHad t = throwError $ "type `" ++ show t ++ "` cannot be casted to Had type"

codegenStmt'Apply
  stmt@(s@(Partition {ranges}) :*=: (ELambda lam)) = do

  -- FIXME: `resolve` fails on inter-locus ranges.
  -- I should apply cast before the resolution occurs to entangle two
  -- previously disjoint partitions.
  (locusS, rMapS) <- resolvePartition' s

  -- FIXME : qt' & qtLambda stuff should be turned into something better
  qtLambda <- ask
  checkSubtypeQ (qty locusS) qtLambda

  -- ranges must be complete
  case rMapS of
    [] -> throwError' "The parition specified on the LHS is empty!"
    [(rLhs, rResolved)] ->
      codegenUnaryLambda rLhs rResolved locusS qtLambda lam
    _ -> do
      -- do the complicated case
      unless (areRangesEquiv rMapS) $ throwError' (errRangesAreProper rMapS)
      codegenLambdaEntangle ranges lam
  where
    errRangesAreProper :: [(Range, Range)] -> String
    errRangesAreProper rMap = printf
      "Ranges given on the LHS of the application contains some incomplete range(s).\n%s"
      (showEmit0 $ byLineT rMap)

codegenStmt'Apply (s :*=: (EQft b)) = codegenApplyQft s
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
  (stG@Locus{qty=qtG}, pG) <- typingGuard e
  trace $ printf "Partitions collected from %s:\n%s" (showEmit0 e) (showEmit0 pG)
  -- resolve the body partition
  stB'@Locus{part=sB, qty=qtB} <- resolvePartitions . leftPartitions . inBlock $ b
  let annotateCastB = qComment $
        printf "Cast Body Partition %s => %s" (show qtB) (show TEn)
  (stmtsCastB, stB) <- case qtB of
    TEn -> return ([], stB')
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
  => Locus -> Locus -> Block'
  -> m [Stmt']
codegenStmt'If'Had stG stB' b = do
  -- 0. extract partition, this will not be changed
  let sB = part stB'
  -- 1. duplicate the body partition
  (stmtsDupB, corr) <- dupState sB
  -- 2. codegen the body
  stmtB <- SEmit . SBlock <$> codegenBlock b
  -- TODO: left vs right merge strategy
  (cardMain', cardStash') <- codegenEnReprCard2 corr
  ((stmtCard, cardMain), (stmtStash, cardStash)) <-
    bothM saveCard (cardMain', cardStash')
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
  newInvs <- forM invs codegenAssertion
  infoInv <- wfSignatureFromPredicates invs
  let infoInvPre = substInfoPre infoInv

  (stmtsPreGuard, statePreLoop, stateLoop) <-
    codegenInit (dropSignatureSpecs infoInv) (dropSignatureSpecs infoInvPre)
  put stateLoop
  -- generate loop invariants

  stmtsBody <- local (++ substEnv) $ do
    ask @IEnv >>= trace . printf "Augmented IENV: %s" . show
    stSep <- typingPartition seps -- check if `seps` clause is valid
    stmtsBody <- codegenFor'Body idx boundl boundr eG body stSep (concat newInvs)

    -- update the post-loop typing state
    -- trace $ "stateLoop:\n" ++ show stateLoop
    codegenFinish stateLoop
    -- get @TState >>= trace . ("staetLoop (subst):\n" ++) . show
    pure stmtsBody

  return $ stmtsPreGuard ++ stmtsBody
  where
    -- IEnv for loop constraints
    substEnv = [(idx, boundl :| [boundr - 1])]

    substInfoPre info = go <$> info
      where
        subst' :: forall a . Substitutable a => a -> a
        subst' = subst [(idx, boundl)]
        go (p, qt, dgr, specs) = (subst' p, qt, dgr, subst' <$> specs)

    -- | the postcondtion of one iteration can be computed bys setting the upper
    -- bound to be the index plus one
    -- invPQtsPost = first (reduce . substP [(idx, EVar idx + 1)]) <$> invPQts

    -- | Generate code and state for the precondition after which
    -- | we only need to concern those mentioned by the loop invariants
    codegenInit infoInv infoInvPre = do
      stmtsPreGuard <- infoInvPre `forM` \(sInv, qtInv, _) -> case sInv of
        Partition [rInv] -> do
          stInv <- resolvePartition sInv
          (sInvSplit, maySplit, mayCast) <- hdlSCError $
            splitThenCastScheme stInv qtInv rInv
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
      stateLoop <- tStateFromPartitionQTys infoInv
      -- trace $ printf "statePreLoop: %s\nstateLoop: %s"  (show statePreLoop) (show stateLoop)

      -- | pass preLoop variables to loop ones
      matchedVarTys <- matchStateCorrLoop statePreLoop stateLoop [(idx, boundl)]
      let stmtsEquiv = (\(e1, e2) -> mkAssignment (fst e1) (fst e2))
            <$> matchedVarTys

      return (concat stmtsPreGuard ++ stmtsEquiv, statePreLoop, stateLoop)

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
  -> Locus -- ^ the partition to be merged into
  -> [Exp'] -- ^ emitted invariants
  -> m [Stmt']
codegenFor'Body idx boundl boundr eG body stSep@(Locus{qty=qtSep}) newInvs = do

  let psBody = leftPartitions . inBlock $ body
  -- FIXME: what's the difference between pG and sG here?
  (stG@Locus{part=sG, qty=qtG }, pG) <- typingGuard eG
  trace $ printf "The guard partition collected from %s is %s" (showEmit0 eG) (showEmit0 pG)
  trace $ printf "From invariant typing, the guard partition is %s from %s" (showEmit0 pG) (show stG)

  -- ^ FIXME: these two handling of guard state seems ungrounded

  (stmtsPrelude, stmtsBody) <- case qtG of
    THad -> do
      stB'@Locus{part=sB, qty=qtB} <- resolvePartitions psBody

      -- It seems that castEN semantics maybe unnecessary with invariant typing?
      (stmtsCastB, stB) <- case qtB of
        _ | isEn qtB -> return ([], stB')
        _            ->
          (,) <$> castPartitionEN stB' <*> resolvePartition (part stB')

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
      let stmtsSplitG = codegenSplitEmitMaybe maySplit

      -- Splitting the guard maintains the invariant of the Had part. It remains
      -- to find a merge candidate of this split guard parition at the end of
      -- the loop.

      -- schemeC <- retypePartition stGSplited TEn
      -- let CastScheme { schVsNewEmit=vsEmitG } = schemeC
      -- let vEmitG = head vsEmitG
      -- let cardVEmitG = EEmit . ECard . EVar $ vEmitG
      -- let stmtsInitG =
      --       [ qComment "Retype from Had to EN and initialize with 0"
      --       , (::=:) vEmitG $
      --           EEmit $ EMakeSeq TNat cardVEmitG $ constExp $ ENum 0 ]
      stG' <- resolvePartition (part stGSplited)
      stmtsCGHad <- codegenStmt'For'Had stB stG' idx body
      dumpSt "the end of Had for loop"
      stmtsMatchLoopBeginEnd <- codegenMatchLoopBeginEnd . inferTsLoopEnd $ stateIterBegin ^. emitSt

      return ( stmtsCastB -- ++ stmtsDupG -- ++ stmtsInitG
             , stmtsSplitG ++ stmtsCGHad ++ stmtsMatchLoopBeginEnd
             )

    TEn01 -> do
      eSep <- case eG of
        GEPartition _ (Just eSep) -> return eSep
        _                         -> throwError' errNoSep

      -- 1. save the "false" part to a new variable
      -- FIXME: write general function to replicate EmitData from Locus instead.
      edsFalse <- findEmsByLocus stG
      edsSaved@(edSavedL, edsSavedR) <- genEmStFromLocus stG
      -- vsEmitG <- findEmitBasesByRanges $ unpackPart sG
      -- redFalseG <- genEmStByRanges qtG (ranges sG)
      -- vsEmitGFalse <- mapM (visitEmBasis . snd) redFalseG
      -- let stmtsSaveFalse = uncurry (stmtAssignSlice (ENum 0) eSep)
      --       <$> zip (fsts vsEmitGFalse) (fsts vsEmitG)
      let stmtsSaveFalse =
            codegenAssignEmitData (eraseRanges edsSaved) (eraseRanges edsFalse)
      -- let stmtsFocusTrue = stmtAssignSelfRest eSep <$> fsts vsEmitG

      -- save the current emit symbol table for
      stateIterBegin <- get @TState

      -- SOLVEm?
      -- TODO: I need one way to duplicate generated emit symbols in the split
      -- and cast semantics so that executing the computation above twice will
      -- solve the problem.
      vsEmitSep <-  findEmitBasesByRanges rsSep

      -- compile for the 'false' branch with non-essential statements suppressed
      (tsFalse, (stmtsFalse, vsFalse)) <- runState stateIterBegin $ do
        installEmits ((inj (loc stG), edSavedL) : (first inj <$> edsSavedR))
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
                      -- , stmtsFocusTrue
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
    installEmits = mapM (uncurry appendEmSt)
    rsSep = ranges $ part stSep
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
      let matchedVarsBE = both fst . snd <$> corrBeginEnd
      -- I don't remember the purpose of this line, purely sanity check?
      pure $ uncurry mkAssignment <$> matchedVarsBE


    errNoSep = "Insufficient knowledge to perform a separation for a EN01 partition "
    -- stmtAssignSlice el er idTo idFrom = idTo ::=: sliceV idFrom el er
    -- stmtAssignSelfRest eBegin idSelf =
    --   stmtAssignSlice eBegin (EEmit . ECard . EVar $ idSelf) idSelf idSelf


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
  => Locus -> Locus -> Var -> Block'
  -> m [Stmt']
codegenStmt'For'Had stB stG vIdx b = do
  -- 0. extract partition, this will not be changed
  let sB = part stB
  -- 1. duplicate the body
  (stmtsDupB, corrB) <- dupState sB
  () <- tracef ">>>>> \n%s" (showEmitI 4 (byLineT stmtsDupB))
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
  => Locus -> Locus -> Exp' -> Exp' -> m [Stmt']
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
  => Exp' -> Locus -> Locus -> Exp' -> Exp' -> m [Stmt']
mergeHadGuardWith eBase stG' stB cardBody cardStashed =
  retypePartition1 stG' TEn >>= maybe (return []) go
  where
    go (_, _, vGENow, tGENow) = do
      stG <- resolvePartition (part stG')
      mergeLociHadEN stB stG
      return $ hadGuardMergeExp vGENow tGENow cardBody cardStashed eBase

hadGuardMergeExp :: Var -> Ty -> Exp' -> Exp' -> Exp' -> [Stmt']
hadGuardMergeExp vEmit tEmit cardMain cardStash eBase =
  let ~(TSeq tInSeq) = tEmit
  in [ qComment "Merge: Body partition + the Guard partition."
     , (vEmit ::=:) $
       (EEmit . EMakeSeq tInSeq cardStash $ constLambda eBase) +
       (EEmit . EMakeSeq tInSeq cardMain $
         constLambda $ reduce $ eBase >+ (1 :: Exp'))
     ]

-- codegenMergePhase
--   :: ( Has (Gensym Emitter) sig m
--      , Has (Error String) sig m
--      )
--   => PhaseTy -> PhaseTy -> m (PhaseTy, [Stmt'])
-- codegenMergePhase p PT0 = return (p, [])
-- codegenMergePhase PT0 p = return (p, [])
-- codegenMergePhase (PTN n1 pr1) (PTN n2 pr2) = do
--    when (n1 /= n2) $
--      throwError' "I don't know how to merge two phases of different degrees."
--    if | prBase pr1 == prBase pr2 -> do
--           let vRepr1 = prRepr pr1
--               vRepr2 = prRepr pr2
--           return (PTN n1 pr1, [ vRepr1 ::=: (EVar vRepr1 + EVar vRepr2) ])
--       | otherwise -> do
--           throwError' "Merging phase types of differnt types is unimplemented. "



-- | Emit two expressions representing the number of kets in two states in
-- correspondence
codegenEnReprCard2
  :: ( Has (Error String) sig m )
  => [((Var, Ty), (Var, Ty))]
  -> m (Exp', Exp')
codegenEnReprCard2 (((vStash, _) ,(vMain, _)) : _) =
  return ( EEmit . ECard . EVar $ vStash
         , EEmit . ECard . EVar $ vMain)
codegenEnReprCard2 a =
  throwError "State cardinality of an empty correspondence is undefined!"


-- Merge the two partitions in correspondence
mergeEmitted :: [((Var, Ty), (Var, Ty))] -> [Var] -> [Stmt']
mergeEmitted corr excluded =
  [ vMain ::=: EOp2 OAdd (EVar vStash) (EVar vMain)
  | ((vMain, _), (vStash, _)) <- corr
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
      part = partition1 rV
  loc <- gensymLoc v
  xSt %= (at v . non [] %~ ((rV, loc) :))
  sSt %= (at loc ?~ (Partition [rV], (TNor, [0])))
  let locus = Locus{ loc, part, qty=TNor, degrees=[] }
  (edL, Identity (_, edR)) <- genEmStFromLocus locus
  (vEmit, _) <- visitEmBasis edR
  return $ vEmit ::=: eEmit
codegenAlloc v e@(EOp2 ONor _ _) _ =
  throwError "Internal: Attempt to create a Nor partition that's not of nor type"
codegenAlloc v e _ = return $ (::=:) v e



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
      (vEmitMerged, _) <- findEmitBasisByRange rMerged
      (vEmitMain, _)   <- findEmitBasisByRange rMain
      deleteEms $ inj <$> [rMerged, rMain]
      case (qtMain, qtMerged) of
        (TEn01, TNor) -> do
          -- append the merged value (ket) into each kets in the main value
          -- TODO: use `genEmStFromLocus` for phase compatibility
          (vEmitResult, _) <- genEmStByRange qtMain rResult >>= visitEmBasis
          vBind <- gensym "lambda_x"
          let stmt = vEmitResult ::=: callMap ef vEmitMain
              ef   = simpleLambda vBind (EVar vBind + EVar vEmitMerged)
          return (stmt, vEmitMain)
        (TEn, THad) -> do
          let (Range _ lBound rBound) = rMain
          let stmtAdd = addENHad1 vEmitMain (reduce (rBound - lBound))
          return (stmtAdd, vEmitMain)
        _             -> throwError' $ printf "No idea about %s to %s conversion."
    MEqual EqualStrategy { esRange = r, esQTy = qt
                         , esVMain = (v1, _), esVAux = (v2, _) } -> do
      -- This is all about "unsplit".
      case qt of
        TNor ->
          -- no "unsplit" should happen here!
          return (qComment "TNor has nothing to be merged!", v1)
        THad ->
          throwError' $ printf "This type (%s) cannot be handled: (%s)" (show qt) (show r)
        _ | qt `elem` [ TEn01, TEn ] ->
          -- TEn01 is emitted as seq<seq<nat>> representing Sum . Tensor,
          -- TEn   is emitted as seq<nat>      representing Sum . Tensor,
          -- It suffices to simply concat them
          pure (merge3 v1 v1 v2, v1)
        _ -> throwError' "This pattern shoule be complete!"
  where
    merge3 vS vRF vRT = vS ::=: (EVar vRF + EVar vRT)


