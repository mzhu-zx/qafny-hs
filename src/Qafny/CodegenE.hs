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
import           Carrier.Cache.One              (dropCache)
import           Control.Monad                  (forM)
import           Effect.Cache                   (Cache, drawErr)
import           Qafny.AST
import           Qafny.Config
import           Qafny.Transform
    ( Production
    , STuple
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
    , resolveSessions
    , retypeSession
    , typingExp
    , typingQEmit
    , typingSession, typingGuard
    )
import           Qafny.Utils                    (findEmitSym, gensymLoc)


--------------------------------------------------------------------------------
-- | Runner
--------------------------------------------------------------------------------
runCodegen :: Configs -> AST -> (TState, Either String AST)
runCodegen conf ast = do
  run . run' $ codegenAST ast
  where
    run' =
      runReader conf .
      runReader initTEnv .
      runState initTState .
      runError

produceCodegen :: Configs -> AST -> Production AST
produceCodegen conf ast =
  let (st, res) = runCodegen conf ast
  in (res, st, [])


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
codegenToplevel q@(QMethod v bds rts rqs ens block) = do
  tEnv <- asks $ appkEnvWithBds bds
  (i, emitBds, (j, block')) <- runGensym $ codegenBlock block
  -- todo: report on the gensym state with a report effect!
  let stmtsDeclare = [ SVar bds' Nothing  | bds' <- emitBds ]
  let totalBlock =
        [SDafny "// Forward Declaration"]
          ++ stmtsDeclare
          ++ [ SDafny ""
             , SDafny "// Method Definition"
             ]
          ++ inBlock block'
  return $ QMethod v bds rts rqs ens (Block totalBlock)
codegenToplevel q@(QDafny _) = return q


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
codegenStmt (SApply s EHad) = dropCache @STuple $ do
  qt <- typingSession s
  opCast <- opCastHad qt
  castWithOp opCast s THad
  where
    opCastHad TNor = return "CastNorHad"
    opCastHad t = throwError $ "type `" ++ show t ++ "` cannot be casted to Had type"
codegenStmt (SApply s@(Session ranges) e@(EEmit (ELambda {}))) = dropCache @STuple $ do
  qt <- typingSession s
  checkSubtypeQ TCH qt
  let tyEmit = typingQEmit qt
  let vsRange = varFromSession s
  vsEmit <- forM vsRange $ findEmitSym . (`Binding` tyEmit)
  return $ mkMapCall `map` vsEmit
  where
    mkMapCall v = v `SAssign` EEmit (ECall "Map" [e, EVar v])


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
codegenStmt'If e seps b  = do
  (locG, sG, qtG) <- typingGuard e
  freeSession <- resolveSessions . leftSessions . inBlock $ b
  codegenStmt'If'Had e seps b

-- | Code Generation of an `If` statement with a Had session
codegenStmt'If'Had
  :: ( Has (Reader TEnv) sig m
     , Has (State TState)  sig m
     , Has (Error String) sig m
     , Has (Gensym String) sig m
     , Has (Gensym Binding) sig m
     )
  => Exp -> Separates -> Block
  -> m [Stmt]
codegenStmt'If'Had = undefined


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
  vEmit <- gensym (Binding v tEmit)
  let rV = Range v (ENum 0) e1
      sV = session1 rV
  loc <- gensymLoc v
  xSt %= (at v ?~ loc)
  sSt %= (at loc ?~ (sV, TNor))
  return $ SAssign vEmit eEmit
codegenAlloc v e@(EOp2 ONor _ _) _ =
  throwError "Internal: Attempt to create a Nor session that's not of nor type"
codegenAlloc v e _ = return $ SAssign v e


-- Cast
castWithOp
  :: ( Has (Error String) sig m
     , Has (State TState) sig m
     , Has (Gensym Binding) sig m
     , Has (Cache STuple) sig m
     )
  => String -> Session -> QTy -> m [Stmt]
castWithOp op s newTy =
  do
    (vOldEmits, tOldEmit, vNewEmits, tNewEmit) <- retypeSession s newTy
    sessionTy <- drawErr @STuple <&> (^. _3)
    -- assemble the emitted terms
    return . concat $
      [ [ SDafny $ "// Cast " ++ show sessionTy ++ " ==> " ++ show newTy
        , SAssign vNew $ EEmit (op `ECall` [EEmit $ EDafnyVar vOld])
        ]
      | (vOld, vNew) <- zip vOldEmits vNewEmits ]
