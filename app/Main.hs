module Main (main) where

import           Qafny.AST          (AST)
import           Qafny.Config
import           Qafny.Emit         (texify)
import           Qafny.Parser       (scanAndParse)
import           Qafny.Runner       (Production (..), produceCodegen)

import qualified Data.Text.Lazy     as Txt
import qualified Data.Text.Lazy.IO  as Txt.IO

import           System.Environment (getArgs)
import           System.Exit        (exitFailure)



parseArg :: IO String
parseArg = fmap (head :: [String] -> String) getArgs

pipeline :: String -> Either String (IO (Production Txt.Text))
pipeline s =
  -- do parsing, rethrow error if any
  withAST <$> scanAndParse s
  where
    configs = Configs { stdlibPath = "../../external/" }
    withAST :: AST -> IO (Production Txt.Text)
    withAST ast = do
      let prod = produceCodegen configs ast
      -- print trace
      putStr $ pTrace prod
      return $ prod { pResult = texify <$> pResult prod }

main :: IO ()
main =
  do
    prog <- parseArg
    withProg prog
  where
    withProg prog = do
      src <- readFile srcFile
      either ((>> exitFailure) . putStrLn) (>>= writeOrReportP) (pipeline src)
      putStrLn $ "\ESC[32mSuccess: target is emited as `" ++ tgtFile ++ "` \ESC[0m"
      where
        writeOrReportP :: Production Txt.Text -> IO ()
        writeOrReportP (Production {pResult=res, pState=st})  = do
          wrapUp <- case res of
            Left err -> do
              putStrLn $ "\ESC[31m[Error]\ESC[93m " ++ err ++ "\ESC[0m"
              return exitFailure
            Right txt -> do
              putStrLn "Pipeline Finished!\n"
              Txt.IO.writeFile tgtFile txt
              return (return ())
          putStrLn $ "Statistics from Codegen:\n" ++ show st
          wrapUp
        srcFile = "./test/Resource/" ++ prog ++ ".qfy"
        tgtFile = "./test/Resource/" ++ prog ++ ".dfy"

-- loadDefaultFile :: IO String
-- loadDefaultFile =
--   let src = "./test/Resource/3.qfy" in
--     readFile src
