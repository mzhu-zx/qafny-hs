{-# LANGUAGE DataKinds, FlexibleContexts, FlexibleInstances,
             GeneralizedNewtypeDeriving, MultiParamTypeClasses, RankNTypes,
             ScopedTypeVariables, TupleSections, TypeApplications,
             TypeOperators, UndecidableInstances #-}

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
import           Effect.Gensym                  (Gensym, gensym)

-- Handlers
import           Control.Carrier.Error.Either   (runError)
import           Control.Carrier.Reader         (runReader)
import           Control.Carrier.State.Strict   (runState)
import           Qafny.Gensym                   (runGensym)

-- Utils
import           Control.Lens                   (at, (%~), (?~), (^.))
import           Control.Lens.Tuple
import           Data.Functor                   ((<&>))
import qualified Data.Map.Strict                as Map


-- Qafny
import           Carrier.Cache.One
    ( dropCache
    , dropCache_
    , readCache
    )
import           Control.Applicative            (Applicative (liftA2))
import           Control.Monad                  (forM)
import           Effect.Cache                   (Cache, drawDefault, drawErr, draw)
import           GHC.Stack                      (HasCallStack)
import           Qafny.AST
import           Qafny.Config
import           Qafny.Transform
    ( STuple
    , TEnv (..)
    , TState
    , initTEnv
    , initTState
    , kEnv
    , sSt
    , xSt
    )
import           Qafny.TypingE
    ( appkEnvWithBds
    , checkSubtype
    , checkSubtypeQ
    , collectMethodTypesM
    , mergeSTuples
    , resolveSession
    , resolveSessions
    , retypeSession
    , retypeSession1
    , typingExp
    , typingGuard
    , typingQEmit
    )
import           Qafny.Utils
    ( findEmitSym
    , gensymEmit
    , gensymLoc
    )
import           Text.Printf                    (printf)

--------------------------------------------------------------------------------
-- | Codegen
--------------------------------------------------------------------------------

codegenAST
  :: ( Has (Reader Configs) sig m
     , Has (Reader TEnv) sig m
     , Has (State TState)  sig m
     , Has (Error String) sig m
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
     )
  => Toplevel
  -> m Toplevel
codegenToplevel q@(QMethod v bds rts rqs ens (Just block)) = do
  (i, emitBdsNames, (j, block')) <-
    runGensym $ local (appkEnvWithBds bds) $ codegenBlock block
  -- todo: report on the gensym state with a report effect!
  let stmtsDeclare = [ SVar (Binding vEmit tEmit) Nothing
                     | (Binding _ tEmit, vEmit) <- emitBdsNames ]
  let blockStmts =
        [ SDafny "// Forward Declaration" ]
        ++ stmtsDeclare
        ++ [ SDafny ""
           , SDafny "// Method Definition"
           ]
        ++ inBlock block'
  return $ QMethod v bds rts rqs ens (Just . Block $ blockStmts)
codegenToplevel q = return q


codegenBlock
  :: ( Has (Reader TEnv) sig m
     , Has (State TState)  sig m
     , Has (Error String) sig m
     , Has (Gensym String) sig m
     , Has (Gensym Binding) sig m
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
     , HasCallStack
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
     )
  => Stmt
  -> m [Stmt]
codegenStmt s@(SVar (Binding v t) Nothing)  = return [s]
codegenStmt s@(SVar (Binding v t) (Just e)) = do
  te <- typingExp e
  checkSubtype t te -- check if `t` agrees with the type of `e`
  codegenAlloc v e t <&> (: [])
codegenStmt (SApply s EHad) = do
  st@(_, _, qt) <- resolveSession s
  opCast <- opCastHad qt
  castWithOp opCast st THad
  where
    opCastHad TNor = return "CastNorHad"
    opCastHad t = throwError $ "type `" ++ show t ++ "` cannot be casted to Had type"
codegenStmt (SApply s@(Session ranges) e@(EEmit (ELambda {}))) = do
  st@(_, _, qt) <- resolveSession s
  checkSubtypeQ TCH qt
  let tyEmit = typingQEmit qt
  -- it's important not to use a fully resolved `s` here, because you don't want
  -- to apply the op to the entire session but only a part of it. 
  let vsRange = varFromSession s 
  vsEmit <- forM vsRange $ findEmitSym . (`Binding` tyEmit)
  return $ mkMapCall `map` vsEmit
  where
    mkMapCall v = v `SAssign` EEmit (ECall "Map" [e, EVar v])
codegenStmt (SIf e seps b) = codegenStmt'If e seps b
codegenStmt s = error $ "Unimplemented:\n\t" ++ show s ++ "\n"


-- | Code Generation of the `If` Statement
codegenStmt'If
  :: ( Has (Reader TEnv) sig m
     , Has (State TState)  sig m
     , Has (Error String) sig m
     , Has (Gensym String) sig m
     , Has (Gensym Binding) sig m
     )
  => Exp -> Separates -> Block
  -> m [Stmt]
codegenStmt'If e seps b = do
  -- resolve the type of the guard
  stG@(locG, sG, qtG) <- typingGuard e
  stB <- resolveSessions . leftSessions . inBlock $ b
  -- act based on the type of the guard
  stmts <- case qtG of
    THad -> codegenStmt'If'Had stG stB b
    _    -> undefined
  return stmts

-- | Code Generation of an `If` statement with a Had session
codegenStmt'If'Had
  :: ( Has (Reader TEnv) sig m
     , Has (State TState)  sig m
     , Has (Error String) sig m
     , Has (Gensym String) sig m
     , Has (Gensym Binding) sig m
     )
  => STuple -> STuple -> Block
  -> m [Stmt]
codegenStmt'If'Had stG stB' b = do
  -- 0. extract session, this will not be changed
  let sB = stB' ^. _2
  -- 1. cast the guard and duplicate the body session
  stmtsCastG <- castSessionCH stB'
  (stmtsDupB, corr) <- dupState sB
  -- 2. codegen the body
  stmtB <- SEmit . SBlock <$> codegenBlock b
  -- TODO: left vs right merge strategy
  (cardMain, cardStash) <- cardStatesCorr corr
  -- 3. merge duplicated body sessions and merge the body with the guard
  stB <- resolveSession sB
  stmtsG <- mergeHadGuard stG stB cardMain cardStash
  let stmtsMerge = mergeEmitted corr
  return $ stmtsCastG ++ stmtsDupB ++ [stmtB] ++ stmtsMerge ++ stmtsG


-- | Assume `stG` is a Had guard, cast it into `CH` type and merge it with
-- the session in`stB`. The number of kets in the generated states depends on
-- the number of kets in the body and that in the stashed body
mergeHadGuard
  :: ( Has (State TState) sig m
     , Has (Error String) sig m
     , Has (Gensym Binding) sig m
     )
  => STuple -> STuple -> Exp -> Exp -> m [Stmt]
mergeHadGuard stG' stB cardBody cardStashed = do
  (_, _, vGENow, tGENow) <- retypeSession1 stG' TCH
  stG <- resolveSession (stG' ^. _2)
  mergeSTuples stB stG
  let ~(TSeq tInSeq) = tGENow
  return
    [ SDafny "// Body Session + Guard Session"
    , vGENow
        `SAssign` EOp2 OAdd
          (EEmit $ EMakeSeq tInSeq cardBody $ constExp (ENum 1))
          (EEmit $ EMakeSeq tInSeq cardStashed $ constExp (ENum 0))
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


-- Merge the two sessions in correspondence
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
codegenAlloc v e@(EOp2 ONor e1 e2) t@(TQ TNor) = do
  let tEmit = typingQEmit TNor
  let eEmit = EEmit $ EMakeSeq TNat e1 $ constExp e2
  vEmit <- gensymEmit (Binding v tEmit)
  let rV = Range v (ENum 0) e1
      sV = session1 rV
  loc <- gensymLoc v
  xSt %= (at v ?~ loc)
  sSt %= (at loc ?~ (sV, TNor))
  return $ SAssign vEmit eEmit
codegenAlloc v e@(EOp2 ONor _ _) _ =
  throwError "Internal: Attempt to create a Nor session that's not of nor type"
codegenAlloc v e _ = return $ SAssign v e


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
    (vOldEmits, tOldEmit, vNewEmits, tNewEmit) <- retypeSession s newTy
    let sessionTy = s ^. _3
    -- assemble the emitted terms
    return . concat $
      [ [ SDafny $ "// Cast " ++ show sessionTy ++ " ==> " ++ show newTy
        , SAssign vNew $ EEmit (op `ECall` [EEmit $ EDafnyVar vOld])
        ]
      | (vOld, vNew) <- zip vOldEmits vNewEmits ]


-- | Cast the given session to CH type!
castSessionCH
  :: ( Has (Error String) sig m
     , Has (State TState) sig m
     , Has (Gensym Binding) sig m
     )
  => STuple -> m [Stmt]
castSessionCH st@(locS, s, qtS) = do
  case qtS of
    TNor -> castWithOp "CastNorCH10" st TCH
    THad -> castWithOp "CastHadCH10" st TCH
    TCH -> throwError @String $
      printf "Session `%s` is already of CH type." (show st)
  

-- | Duplicate the data, i.e. sequences to be emitted, by generating statement
-- duplicating the data as well as the correspondence between the range
-- bindings, emitted variables from the fresh copy and the original emitted
-- varaibles
--
-- However, this does not add the generated symbols to the typing environment or
-- modifying the existing bindings!p
dupState
  :: ( Has (Error String) sig m
     , Has (State TState) sig m
     , Has (Gensym Binding) sig m
     )
  => Session -> m ([Stmt], [(Binding, Var, Var)])
dupState s' = do
  (locS, s, qtS) <- resolveSession s'
  let tEmit = typingQEmit qtS
  let bds = [ Binding x tEmit | x <- varFromSession s]
  -- generate a set of fresh emit variables as the stashed session
  vsEmitFresh <- forM bds gensym -- do not manipulate the `emitSt` here
  vsEmitPrev <- forM bds findEmitSym -- the only place where state is used!
  let stmts = [ SAssign vEmitFresh (EVar vEmitPrev)
              | (vEmitFresh, vEmitPrev) <- zip vsEmitFresh vsEmitPrev ]
  return (stmts, zip3 bds vsEmitPrev vsEmitFresh)
