module Main (main) where

import           Qafny.AST          (Ty)
import           Qafny.Codegen      (codegen)
import           Qafny.Emit         (texify)
import           Qafny.Parser       (scanAndParse)
import           Qafny.Transform    (TState)
import           Qafny.CodegenE     (produceCodegen)
import           Qafny.Config

import qualified Data.Text.Lazy     as Txt
import qualified Data.Text.Lazy.IO  as Txt.IO

import           System.Environment (getArgs)
import           System.Exit        (exitFailure)



parseArg :: IO String
parseArg = fmap (head :: [String] -> String) getArgs

pipeline :: String -> Either String (Txt.Text, TState, [(String, Ty)])
pipeline s =
  do ast <- scanAndParse s
     let (result, state, ev) = codegen ast
     ir <- result
     return (texify ir, state, ev)

pipelineE :: String -> Either String (Txt.Text, TState, [(String, Ty)])
pipelineE s =
  do ast <- scanAndParse s
     let configs = Configs { _stdlibPath = "../../external/" }
     let (result, state, ev) = produceCodegen configs ast
     ir <- result
     return (texify ir, state, ev)


main :: IO ()
main =
  do
    prog <- parseArg
    withProg prog
  where
    withProg prog = do
      s <- readFile src
      writeOrReport $ pipelineE s
      putStrLn $ "\ESC[32mSuccess: target is emited as `" ++ tgt ++ "` \ESC[0m"
      where
        writeOrReport (Right (txt, st, emittedVars)) =
          do
            putStrLn $ "Pipeline Finished!\nStatistics from Codegen:\n" ++ show st
            putStrLn $ "Writer Result:\n  " ++ show emittedVars
            Txt.IO.writeFile tgt txt
        writeOrReport (Left e) =
          do
            putStrLn $ "\ESC[31m[Error]\ESC[93m " ++ e ++ "\ESC[0m"
            exitFailure
        src = "./test/Resource/" ++ prog ++ ".qfy"
        tgt = "./test/Resource/" ++ prog ++ ".dfy"

-- loadDefaultFile :: IO String
-- loadDefaultFile =
--   let src = "./test/Resource/3.qfy" in
--     readFile src
