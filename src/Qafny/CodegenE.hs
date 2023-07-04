{-# LANGUAGE
    FlexibleContexts
  , RecordWildCards
  , ScopedTypeVariables
  , TupleSections
  , TypeApplications
  #-}

module Qafny.CodegenE where



-- | Code Generation through Fused Effects

-- Effects
import           Control.Effect.Catch
import           Control.Effect.Error           (Error, throwError)
import           Control.Effect.Labelled
import           Control.Effect.Lens
import           Control.Effect.Reader
import qualified Control.Effect.Reader.Labelled as L
import           Control.Effect.State           (State)
import           Control.Effect.Trace
import           Effect.Gensym                  (Gensym, gensym)

-- Handlers
import           Qafny.Gensym                   (resumeGensym)

-- Utils
import           Control.Lens                   (at, non, (%~), (?~), (^.))
import           Control.Lens.Tuple
import           Control.Monad                  (forM, forM_, unless, when)
import           Data.Functor                   ((<&>))
import qualified Data.Map.Strict                as Map
import           Text.Printf                    (printf)


-- Qafny
import           Carrier.Gensym.Emit            (runGensymEmit)
import           Data.Maybe                     (listToMaybe)
import           GHC.Stack                      (HasCallStack)
import           Qafny.AInterp                  (reduceExp)
import           Qafny.AST
import           Qafny.Config
import           Qafny.Env
    ( CastScheme (..)
    , STuple (..)
    , SplitScheme (..)
    , TEnv (..)
    , TState
    , kEnv
    , sSt
    , xSt
    )
import           Qafny.TypeUtils
import           Qafny.TypingE
    ( appkEnvWithBds
    , checkSubtype
    , checkSubtypeQ
    , collectMethodTypesM
    , mergeSTuples
    , resolvePartition
    , resolvePartitions
    , retypePartition
    , retypePartition1
    , splitScheme
    , splitThenCastScheme
    , typingExp
    , typingGuard
    )
import           Qafny.Utils
    ( bindingOfRangeQTy
    , findEmitRangeQTy
    , gensymEmit
    , gensymEmitRangeQTy
    , gensymLoc
    , gensymRangeQTy
    , removeEmitRangeQTys
    , throwError'
    )
import           Qafny.Variable                 (Variable (variable))

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
  let mkRequires s = QDafny $ "include \"" ++ path ++ "/" ++ s ++ "\""
  let requires =
        [ "QPreludeUntyped.dfy"
        , "libraries/src/Collections/Sequences/Seq.dfy"
        , "libraries/src/NonlinearArithmetic/Power2.dfy"
        ]
  let prelude =
        (mkRequires <$> requires)
          ++ [ QDafny ""
             , QDafny "// target Dafny version: 3.12.0"
             , QDafny "abstract module QafnyDefault {"
             , QDafny "import opened QPreludeUntyped"
             , QDafny "import opened Seq"
             , QDafny "import opened Power2"
             , QDafny ""
             ]
  let finale =
        [QDafny "}"]
  let methods = collectMethodTypesM ast
  main <- local (kEnv %~ Map.union methods) $ mapM codegenToplevel ast
  return $ prelude ++ main ++ finale

codegenToplevel
  :: ( Has (Reader TEnv) sig m
     , Has (State TState)  sig m
     , Has (Error String) sig m
     , Has Trace sig m
     )
  => Toplevel
  -> m Toplevel
codegenToplevel q@(QMethod v bds rts rqs ens (Just block)) = do
  (countMeta, (countEmit, (vsEmitR', vsEmitB), (rqsCG, blockCG))) <-
    local (appkEnvWithBds bds) $
    codegenRequires rqs `resumeGensym` codegenBlock block

  -- Gensym symbols are in the reverse order!
  let vsEmitR = reverse vsEmitR'

  -- todo: report on the gensym state with a report effect!
  let stmtsDeclare = [ SVar (Binding vEmit tEmit) Nothing
                     | (Binding _ tEmit, vEmit) <- vsEmitB ]
  let bdsCG = do
        bd@(Binding x ty) <- bds
        case ty of
          TQReg _ -> [ Binding vEmit tEmit
                     | (Binding y tEmit, vEmit) <- vsEmitR, x == y ]
          _    -> return bd

  let blockStmts =
        [ qComment "Forward Declaration" ]
        ++ stmtsDeclare
        ++ [ SDafny ""
           , qComment "Method Definition"
           ]
        ++ inBlock blockCG
  return $ QMethod v bdsCG rts rqsCG ens (Just . Block $ blockStmts)
codegenToplevel q = return q


codegenRequires
  :: ( Has (State TState)  sig m
     , Has (Error String) sig m
     , Has (Gensym String) sig m
     , Has (Gensym Binding) sig m
     )
  => Requires -> m Requires
codegenRequires rqs = forM rqs $ \rq ->
  -- TODO: I need to check if partitions from different `requires` clauses are
  -- indeed disjoint!
  case rq of
    ESpec s qt espec -> do
      sLoc <- gensymLoc "requires"
      sSt %= (at sLoc ?~ (s, qt))
      let xMap = [ (v, [(r, sLoc)]) | r@(Range v _ _) <- unpackPart s ]
      vsEmit <- forM (unpackPart s) (`gensymEmitRangeQTy` qt)
      xSt %= Map.unionWith (++) (Map.fromListWith (++) xMap)
      case espec of
        EQSpec v intv body -> codegenSpec vsEmit v intv body
        _                  -> undefined
    _ ->
      return rq

codegenSpec
  :: ( Has (Error String) sig m
     , Has (State TState) sig m
     )
  => [Var] -> Var -> Intv -> [Exp] -> m Exp
codegenSpec vsEmit bind (Intv l r) eValues = do
  unless (length vsEmit == length eValues) $
    throwError' $ printf
      "The number of values doesn't agree with that of partitions: %s %s"
      (show vsEmit) (show eValues)
  let eBound = Just (EEmit (EOpChained l [(OLe, EVar bind), (OLt, r)]))
  let eSelect x = EEmit (ESelect (EVar x) (EVar bind))
  let es = [ EForall (Binding bind TNat) eBound (EOp2 OEq (eSelect vE) eV)
           | (vE, eV) <- zip vsEmit eValues, eV /= EWildcard ]
  return $ case es of
    []     -> EBool True
    x : xs -> EEmit (EOpChained x [ (OAnd, x') | x' <- xs ])

codegenBlock
  :: ( Has (Reader TEnv) sig m
     , Has (State TState)  sig m
     , Has (Error String) sig m
     , Has (Gensym String) sig m
     , Has (Gensym Binding) sig m
     , Has Trace sig m
     )
  => Block
  -> m Block
codegenBlock (Block stmts) =
  Block <$> codegenStmts stmts

codegenStmts
  :: ( Has (Reader TEnv) sig m
     , Has (State TState)  sig m
     , Has (Error String) sig m
     , Has (Gensym String) sig m
     , Has (Gensym Binding) sig m
     , Has Trace sig m
     )
  => [Stmt]
  -> m [Stmt]
codegenStmts [] = return []
codegenStmts (stmt : stmts) = do
  stmts' <- codegenStmt stmt
  (stmts' ++) <$>
    case stmt of
      SVar (Binding v t) eM -> do
        local (kEnv %~ at v ?~ t) $ codegenStmts stmts
      _ -> do
        codegenStmts stmts

codegenStmt
  :: ( Has (Reader TEnv) sig m
     , Has (State TState)  sig m
     , Has (Error String) sig m
     , Has (Gensym String) sig m
     , Has (Gensym Binding) sig m
     , Has Trace sig m
     )
  => Stmt
  -> m [Stmt]
codegenStmt s@(SVar (Binding v t) Nothing)  = return [s]
codegenStmt s@(SVar (Binding v t) (Just e)) = do
  te <- typingExp e
  checkSubtype t te -- check if `t` agrees with the type of `e`
  codegenAlloc v e t <&> (: [])
codegenStmt (SApply s EHad) = do
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
  ret <- (stmtsSplit ++) <$> castWithOp opCast stSplit THad
  -- use sSt >>= \s' -> trace $ printf "[codegen] sSt: %s" (show s')
  return ret
  where
    opCastHad TNor = return "CastNorHad"
    opCastHad t = throwError $ "type `" ++ show t ++ "` cannot be casted to Had type"


-- | The semantics of a 'SApply' is tricky because of the timing to do the split
-- and cast. Here's the current strategy:
-- 
-- If the current session is not in EN or EN10 type, compute the
-- 'splitThenCastScheme' and apply the scheme to the codegen.
--
-- If however, the current session is in EN or EN10 type, perform no split at
-- all! (Although applying a lambda to a range that requires tearing a range
-- apart is not advised and is undefined. )
codegenStmt (SApply s@(Partition ranges) e@(EEmit (ELambda {}))) = do
  st'@(STuple (_, _, qt)) <- resolvePartition s
  checkSubtypeQ qt TEN
  r <- case ranges of
    []  -> throwError "Parser says no!"
    [x] -> return x
    _   -> throwError errRangeGt1
  (_, maybeScheme) <- splitThenCastScheme st' TEN r
  stmts <- codegenSplitThenCastEmit maybeScheme
  -- it's important not to use the fully resolved `s` here, because the OP should
  -- only be applied to the sub-partition specified in the annotation.
  vsEmit <- unpackPart s `forM` (`findEmitRangeQTy` qt)
  return $ mkMapCall `map` vsEmit
  where
    errRangeGt1 :: String
    errRangeGt1 = printf "%s contains more than 1 range no!" (show ranges)
    mkMapCall v = v `SAssign` EEmit (ECall "Map" [e, EVar v])
codegenStmt (SIf e seps b) = do
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

codegenStmt (SFor idx boundl boundr eG invs seps body) = do
  -- resolve the type of the guard
  stG@(STuple (_, sG, qtG)) <- typingGuard eG
  stB'@(STuple (_, sB, qtB)) <- resolvePartitions . leftPartitions . inBlock $ body
  (stmtsCastB, stB) <- case qtB of
    TEN -> return ([], stB')
    _   -> (,) <$> castPartitionEN stB' <*> resolvePartition (unSTup stB' ^. _2)
  -- what to do with the guard partition is unsure...
  (stmtsDupG, gCorr) <- dupState sG
  (rL, eConstraint) <- makeLoopRange sG boundl boundr

  (stmtsPrelude, stmtsBody) <- case qtG of
    THad ->
      do (stGSplited, schemeSMaybe) <- splitScheme stG rL
         stmtsSplitG <- codegenSplitEmitMaybe schemeSMaybe
         schemeC <- retypePartition stGSplited TEN
         let CastScheme { schVsNewEmit=(~[vEmitG])} = schemeC
         let cardVEmitG = EEmit . ECard . EVar $ vEmitG
         let stmtsInitG =
               [ qComment "Retype from Had to EN and initialize with 0"
               , SAssign vEmitG $
                   EEmit $ EMakeSeq TNat cardVEmitG $ constExp $ ENum 0 ]
         -- Make a temporary counter to record `Pow`s when coverting a Had
         -- to a EN partition (not added to `emitSt` on purpose!)
         -- vEmitCounter <- gensym (Binding "had_counter" TNat)
         -- let stmtsInitCounter =
         --       [ qComment "Initialize Had Power Counter"
         --       , SAssign vEmitCounter (ENum 1) ]
         -- Resolve again to get the new quantum type!
         stG' <- resolvePartition (unSTup stGSplited ^. _2)
         stmtsCGHad <-
           codegenStmt'For'Had stB stG' vEmitG idx body
         return $ ( stmtsInitG -- ++ stmtsInitCounter
                  , stmtsSplitG ++ stmtsCGHad)
    _    -> undefined
  let innerFor = SEmit $ SForEmit idx boundl boundr [] $ Block stmtsBody
  return $ stmtsCastB ++ stmtsDupG ++ stmtsPrelude ++ [innerFor]

codegenStmt s = error $ "Unimplemented:\n\t" ++ show s ++ "\n"


-- | Code Generation of an `If` statement with a Had partition
codegenStmt'If'Had
  :: ( Has (Reader TEnv) sig m
     , Has (State TState)  sig m
     , Has (Error String) sig m
     , Has (Gensym String) sig m
     , Has (Gensym Binding) sig m
     , Has Trace sig m
     )
  => STuple -> STuple -> Block
  -> m [Stmt]
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


-- | Code Generation of a `For` statement with a Had partition
codegenStmt'For'Had
  :: ( Has (Reader TEnv) sig m
     , Has (State TState)  sig m
     , Has (Error String) sig m
     , Has (Gensym String) sig m
     , Has (Gensym Binding) sig m
     , Has Trace sig m
     )
  => STuple -> STuple -> Var -> Var -> Block
  -> m [Stmt]
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

  -- 5. (Compromise) double the counter
  let stmtAdd1 = addENHad1 vEmitG vIdx
  mergeSTuples stB stG
  return $ stmtsDupB ++ [stmtB] ++ stmtsMergeB ++ [stmtAdd1]



-- | Assume `stG` is a Had guard, cast it into `EN` type and merge it with
-- the partition in`stB`. The number of kets in the generated states depends on
-- the number of kets in the body and that in the stashed body
mergeHadGuard
  :: ( Has (State TState) sig m
     , Has (Error String) sig m
     , Has (Gensym Binding) sig m
     )
  => STuple -> STuple -> Exp -> Exp -> m [Stmt]
mergeHadGuard = mergeHadGuardWith (ENum 0)

mergeHadGuardWith
  :: ( Has (State TState) sig m
     , Has (Error String) sig m
     , Has (Gensym Binding) sig m
     )
  => Exp -> STuple -> STuple -> Exp -> Exp -> m [Stmt]
mergeHadGuardWith eBase stG' stB cardBody cardStashed = do
  (_, _, vGENow, tGENow) <- retypePartition1 stG' TEN
  stG <- resolvePartition (unSTup stG' ^. _2)
  mergeSTuples stB stG
  return $ hadGuardMergeExp vGENow tGENow cardBody cardStashed eBase

hadGuardMergeExp :: Var -> Ty -> Exp -> Exp -> Exp -> [Stmt]
hadGuardMergeExp vEmit tEmit cardMain cardStash eBase =
  let ~(TSeq tInSeq) = tEmit
  in [ qComment "Merge: Body partition + the Guard partition."
     , vEmit
       `SAssign` EOp2 OAdd
        (EEmit $ EMakeSeq tInSeq cardMain $
          constExp $ EOp2 OAdd eBase (ENum 1))
        (EEmit $ EMakeSeq tInSeq cardStash $ constExp eBase)
     ]


-- Emit two expressions representing the number of kets in two states in
-- correspondence
cardStatesCorr
  :: (Has (Error String) sig m)
  => [(Binding, Var, Var)]
  -> m (Exp, Exp)
cardStatesCorr ((_, vStash ,vMain) : _) =
  return ( EEmit . ECard . EVar $ vStash
         , EEmit . ECard . EVar $ vMain)
cardStatesCorr a =
  throwError $ "State cardinality of an empty correspondence is undefined!"


-- Merge the two partitions in correspondence
mergeEmitted :: [(Binding, Var, Var)] -> [Stmt]
mergeEmitted corr =
  [ SAssign vMain (EOp2 OAdd (EVar vMain) (EVar vStash))
  | (_, vMain, vStash) <- corr ]


-- | Generate statements that allocate qubits if it's Nor; otherwise, keep the
-- source statement as is.
codegenAlloc
  :: ( Has (Gensym Binding) sig m
     , Has (Gensym String) sig m
     , Has (State TState)  sig m
     , Has (Error String) sig m
     )
  => Var -> Exp -> Ty -> m Stmt
codegenAlloc v e@(EOp2 ONor e1 e2) t@(TQReg _) = do
  let eEmit = EEmit $ EMakeSeq TNat e1 $ constExp e2
  let rV = Range v (ENum 0) e1
      sV = partition1 rV
  vEmit <- gensymEmitRangeQTy rV TNor
  loc <- gensymLoc v
  xSt %= (at v . non [] %~ ((rV, loc) :))
  sSt %= (at loc ?~ (sV, TNor))
  return $ SAssign vEmit eEmit
codegenAlloc v e@(EOp2 ONor _ _) _ =
  throwError "Internal: Attempt to create a Nor partition that's not of nor type"
codegenAlloc v e _ = return $ SAssign v e

--------------------------------------------------------------------------------
-- * Cast Semantics
--------------------------------------------------------------------------------
codegenCastEmit
  :: ( Has (Error String) sig m)
  => CastScheme -> m [Stmt]
codegenCastEmit
  CastScheme{ schVsOldEmit=vsOldEmits
            , schVsNewEmit=vsNewEmit
            , schQtNew=qtNew
            , schQtOld=qtOld
            } = do
  op <- mkOp qtOld qtNew
  return . concat $
      [ [ qComment $ "Cast " ++ show qtOld ++ " ==> " ++ show qtNew
        , SAssign vNew $ EEmit (op `ECall` [EEmit $ EDafnyVar vOld])
        ]
      | (vOld, vNew) <- zip vsOldEmits vsNewEmit ]
  where
    mkOp TNor TEN   = return "CastNorEN"
    mkOp TNor TEN01 = return "CastNorEN01"
    mkOp TNor THad  = return "CastNorHad"
    mkOp _    _     = throwError err
    err :: String = printf "Unsupport cast from %s to %s." (show qtOld) (show qtNew)

-- | Convert quantum type of `s` to `newTy` and emit a cast statement with a
-- provided `op`
castWithOp
  :: ( Has (Error String) sig m
     , Has (State TState) sig m
     , Has (Gensym Binding) sig m
     )
  => String -> STuple -> QTy -> m [Stmt]
castWithOp op s newTy =
  do
    schemeC <- retypePartition s newTy
    let CastScheme{ schVsOldEmit=vsOldEmits , schVsNewEmit=vsNewEmit} = schemeC
    let partitionTy = unSTup s ^. _3
    -- assemble the emitted terms
    return . concat $
      [ [ qComment $ "Cast " ++ show partitionTy ++ " ==> " ++ show newTy
        , SAssign vNew $ EEmit (op `ECall` [EEmit $ EDafnyVar vOld])
        ]
      | (vOld, vNew) <- zip vsOldEmits vsNewEmit ]


-- | Cast the given partition to EN type!
castPartitionEN
  :: ( Has (Error String) sig m
     , Has (State TState) sig m
     , Has (Gensym Binding) sig m
     )
  => STuple -> m [Stmt]
castPartitionEN st@(STuple (locS, s, qtS)) = do
  case qtS of
    TNor -> castWithOp "CastNorEN" st TEN
    THad -> castWithOp "CastHadEN" st TEN
    TEN -> throwError' $
      printf "Partition `%s` is already of EN type." (show st)


-- | Duplicate the data, i.e. sequences to be emitted, by generating statement
-- duplicating the data as well as the correspondence between the range
-- bindings, emitted variables from the fresh copy and the original emitted
-- varaibles
--
-- However, this does not add the generated symbols to the typing environment or
-- modifying the existing bindings!
dupState
  :: ( Has (Error String) sig m
     , Has (State TState) sig m
     , Has (Gensym Binding) sig m
     )
  => Partition -> m ([Stmt], [(Binding, Var, Var)])
dupState s' = do
  STuple (locS, s, qtS) <- resolvePartition s'
  -- let tEmit = typingQEmit qtS
  -- let bds = [ Binding x tEmit | x <- varFromPartition s]
  let rs = unpackPart s
  let bds = [ bindingOfRangeQTy r qtS | r <- rs ]
  -- generate a set of fresh emit variables as the stashed partition
  vsEmitFresh <- bds `forM` gensym    -- do not manipulate the `emitSt` here
  vsEmitPrev <- bds `forM` gensymEmit -- the only place where state is used!
  let stmts = [ SAssign vEmitFresh (EVar vEmitPrev)
              | (vEmitFresh, vEmitPrev) <- zip vsEmitFresh vsEmitPrev ]
  return (stmts, zip3 bds vsEmitPrev vsEmitFresh)

-- | Assemble a partition collected from the guard with bounds and emit a check.
--
-- Precondition: Split has been performed at the subtyping stage so that it's
-- guaranteed that only one range can be in the partition
--
makeLoopRange
  :: Has (Error String) sig m
  => Partition -> Exp -> Exp -> m (Range, Exp)
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
  -> m [Stmt]
codegenSplitEmitMaybe = maybe (return []) codegenSplitEmit

-- | Generate emit variables and split operations from a given split scheme.
codegenSplitEmit
  :: ( Has (Error String) sig m
     , Has Trace sig m
     )
  => SplitScheme
  -> m [Stmt]
codegenSplitEmit
  ss@SplitScheme { schQty=qty
                 , schROrigin=rOrigin@(Range x left _)
                 , schRTo=rTo
                 , schRsRem=rsRem
                 } =
  trace ("codegenSplitEmit: " ++ show ss) >>
  case qty of
    t | t `elem` [ TNor, THad, TEN01 ] -> do
      let offset e = reduceExp $ EOp2 OSub e left
      let stmtsSplit =
            [ SAssign vEmitNew $ EEmit (ESeqRange (EVar (schVEmitOrigin ss)) (offset el) (offset er))
            | (vEmitNew, Range _ el er) <- zip (schVsEmitAll ss) (rTo : rsRem) ]
      return stmtsSplit
    _    -> throwError @String $ printf "Splitting a %s partition is unsupported." (show qty)


-- -- | Given a Had Partition and a partition, if the partition contains more qubits
-- -- than the partition, then split the partition, return the STuple containing only
-- -- this partition and generates statements to perform the split in Dafny.n
-- splitHadPartition
--   :: ( Has (Error String) sig m
--      )
--   => STuple -> Partition
--   -> m (STuple, [Stmt])
-- splitHadPartition sFull@(STuple (locS, Partition [rS], THad)) (Partition [rS']) = do
--   if rS == rS'
--     then return (sFull, [])
--     else undefined -- TODO: implement the split
-- splitHadPartition sFull sPart =
--   throwError' $
--     printf "%s or %s is not a singleton Had partition!" (show sFull) (show sPart)

--------------------------------------------------------------------------------
-- * Split & Cast Semantics
--------------------------------------------------------------------------------
codegenSplitThenCastEmit
  :: ( Has (Error String) sig m
     , Has Trace sig m
     )
  => Maybe(CastScheme, Maybe SplitScheme)
  -> m [Stmt]
codegenSplitThenCastEmit =
  maybe (return []) inner
  where
    inner (schemeC, maybeSchemeS) =
      (++)
      <$> codegenSplitEmitMaybe maybeSchemeS
      <*> codegenCastEmit schemeC


--------------------------------------------------------------------------------
-- * Merge Semantics
--------------------------------------------------------------------------------
-- | Merge semantics of a Had qubit into one EN emitted state
-- uses the name of the emitted seq as well as the index name
addENHad1 :: Var -> Var -> Stmt
addENHad1 vEmit idx =
  SAssign vEmit $
    EOp2 OAdd (EVar vEmit) (EEmit $ ECall "Map" [eLamPlusPow2, EVar vEmit])
  where
    vfresh = "x__lambda"
    eLamPlusPow2 =
      EEmit . ELambda vfresh $
        EOp2 OAdd (EVar vfresh) (EEmit (ECall "Pow2" [EVar idx]))


-- | Multiply the Had coutner by 2
doubleHadCounter :: Var -> Stmt
doubleHadCounter vCounter =
  SAssign vCounter $ EOp2 OMul (ENum 2) (EVar vCounter)


