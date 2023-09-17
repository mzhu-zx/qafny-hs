module Qafny.Runner where
import           Control.Algebra                 (run)
import qualified Control.Carrier.Error.Either    as ErrE (runError)

import           Control.Carrier.Reader          (runReader)
import           Control.Carrier.State.Strict    (runState)
import           Control.Carrier.Trace.Returning (runTrace)
import           Qafny.Codegen                   (codegenAST)
import           Qafny.Config                    (Configs)
import           Qafny.Env
import           Qafny.Syntax.AST                (AST, Var)
import           Qafny.Syntax.Parser             (scanAndParse)

--------------------------------------------------------------------------------
-- Wrapper
--------------------------------------------------------------------------------
data Production a = Production
  { pResult ::  Either String a
  , pState  :: [(Var, TState)]
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


runCodegen :: Configs -> AST -> ([String], ([(Var, TState)], Either String AST))
runCodegen conf ast = do
  run . run' $ codegenAST ast
  where
    run' =
      runTrace .
      runReader conf .
      runReader initTEnv

produceCodegen :: Configs -> AST -> Production AST
produceCodegen conf ast =
  let (trace, (st, res)) = runCodegen conf ast
  in Production { pResult = res
                , pState = st
                , pTrace = sep ++ "Trace:\n\n" ++ unlines trace ++ sep
                }
  where
    sep = replicate 80 '=' ++ "\n"

-- Load a source file (specified by its name w/o the extension) and parse it
-- into an AST
loadFileIO :: String -> IO AST
loadFileIO prog = do
  file <- readFile $ "./test/Resource/" ++ prog ++ ".qfy"
  either fail return $ scanAndParse file
