module Qafny.Runner where
import           Control.Algebra              (run)
import qualified Control.Carrier.Error.Church as ErrC (runError)
import qualified Control.Carrier.Error.Either as ErrE (runError)

import           Control.Carrier.Reader       (runReader)
import           Control.Carrier.State.Strict (runState)

import           Qafny.AST                    (AST, Ty)
import           Qafny.CodegenE               (codegenAST)
import           Qafny.Config                 (Configs)
import           Qafny.Env

--------------------------------------------------------------------------------
-- Wrapper
--------------------------------------------------------------------------------
type Production a = (Either String a, TState, [(String, Ty)])

--------------------------------------------------------------------------------
-- | Runner
--------------------------------------------------------------------------------
debugCodegen :: Configs -> AST -> Production AST
debugCodegen conf ast = 
  let (st, a) = run . run' $ codegenAST ast
  in (Right a, st, [])
  where
    run' =
      runReader conf .
      runReader initTEnv .
      runState initTState .
      ErrC.runError error return


runCodegen :: Configs -> AST -> (TState, Either String AST)
runCodegen conf ast = do
  run . run' $ codegenAST ast
  where
    run' =
      runReader conf .
      runReader initTEnv .
      runState initTState .
      ErrE.runError

produceCodegen :: Configs -> AST -> Production AST
produceCodegen conf ast =
  let (st, res) = runCodegen conf ast
  in (res, st, [])
