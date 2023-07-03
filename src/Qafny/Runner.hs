module Qafny.Runner where
import           Control.Algebra                 (run)
import qualified Control.Carrier.Error.Church    as ErrC (runError)
import qualified Control.Carrier.Error.Either    as ErrE (runError)

import           Control.Carrier.Reader          (runReader)
import           Control.Carrier.State.Strict    (runState)
import           Control.Carrier.Trace.Returning (runTrace)

import           Control.Carrier.Trace.Returning (runTrace)
import           Qafny.AST                       (AST, Ty)
import           Qafny.CodegenE                  (codegenAST)
import           Qafny.Config                    (Configs)
import           Qafny.Env

--------------------------------------------------------------------------------
-- Wrapper
--------------------------------------------------------------------------------
data Production a = Production
  { pResult ::  Either String a
  , pState  :: TState
  , pTrace  :: String
  }

--------------------------------------------------------------------------------
-- | Runner
--------------------------------------------------------------------------------
-- debugCodegen :: Configs -> AST -> Production AST
-- debugCodegen conf ast =
--   let (tr, (st, a)) = run . run' $ codegenAST ast
--   in (Right a, st, [], tr)
--   where
--     run' =
--       runTrace .
--       runReader conf .
--       runReader initTEnv .
--       runState initTState .
--       ErrC.runError error return


runCodegen :: Configs -> AST -> ([String], (TState, Either String AST))
runCodegen conf ast = do
  run . run' $ codegenAST ast
  where
    run' =
      runTrace .
      runReader conf .
      runReader initTEnv .
      runState initTState .
      ErrE.runError

produceCodegen :: Configs -> AST -> Production AST
produceCodegen conf ast =
  let (trace, (st, res)) = runCodegen conf ast
  in Production { pResult = res
                , pState = st
                , pTrace = "Trace:\n" ++ concatMap (\s -> "\t" ++ "\n") trace
                }
