{-# LANGUAGE FlexibleContexts, FlexibleInstances, GeneralizedNewtypeDeriving,
             MultiParamTypeClasses, RankNTypes, TupleSections, TypeOperators,
             UndecidableInstances #-}

module Qafny.CodegenE where

-- | Code Generation through Fused Effects

import           Control.Effect.Catch
import           Control.Effect.Error         (Error)
import           Control.Effect.Lens
import           Control.Effect.Reader
import           Control.Effect.State         (State)
import           Control.Effect.Throw
import           Control.Effect.Writer        (Writer)

import           Control.Lens                 ((%~), (^.))
import qualified Data.Map.Strict              as Map

import           Control.Carrier.Error.Either (runError)
import           Control.Carrier.Reader       (runReader)
import           Control.Carrier.State.Strict (runState)
import           Control.Monad.Identity       (IdentityT (runIdentityT))
import           Qafny.AST
import           Qafny.Config
import           Qafny.Transform
    ( Production
    , TEnv (..)
    , TState
    , initTEnv
    , initTState
    , kEnv
    , kSt
    )
import           Qafny.Typing
    ( appkEnvWithBds
    , collectMethodTypesM
    )



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
  path <- view stdlibPath
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
  -- sync kState with kEnv because when handling Stmts, environment becomes
  -- a state!
  kSt .= tEnv ^. kEnv
  -- (block', eVts) <- listen $ only1 $ local (const tEnv) $ aug block
  -- let stmtsDeclare = map (\(s, t) -> SVar (Binding s t) Nothing) eVts
  -- let totalBlock =
  --       [SDafny "// Forward Declaration"]
  --         ++ stmtsDeclare
  --         ++ [ SDafny ""
  --            , SDafny "// Method Definition"
  --            ]
  --         ++ inBlock block'
  return $ QMethod v bds rts rqs ens block
codegenToplevel q@(QDafny _) = return q

--------------------------------------------------------------------------------
-- | Algebra
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
