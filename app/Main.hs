module Main (main) where

import           Qafny.Config
import           Qafny.Runner
    ( Production (..)
    , collectErrors
    , produceCodegen
    )
import           Qafny.Syntax.Emit   (texify)
import           Qafny.Syntax.Parser (scanAndParse)

import qualified Data.Text.Lazy      as Txt
import qualified Data.Text.Lazy.IO   as Txt.IO

import           Control.Monad       (forM_)
import           Qafny.FileUtils     (countDepth)
import           System.Environment  (getArgs)
import           System.Exit         (exitFailure)
import           Text.Printf         (printf)


parseArg :: IO (String, Int)
parseArg = do
  path <- fmap (head :: [String] -> String) getArgs
  return (path, countDepth path)

pipeline :: String -> Configs -> Either String (IO (Production Txt.Text))
pipeline s configs =
  -- do parsing, rethrow error if any
  withAST <$> scanAndParse s
  where
    -- withAST :: AST -> IO (Production Txt.Text)
    withAST ast = do
      let prod = produceCodegen configs ast
      -- print trace
      putStr $ pTrace prod
      return $ prod { pResult = texify <$> pResult prod }

main :: IO ()
main =
  do
    (prog, depth') <- parseArg
    withProg prog (defaultConfigs { depth=depth' })
  where
    withProg prog config = do
      src <- readFile srcFile
      either ((>> exitFailure) . putStrLn) (>>= writeOrReportP) (pipeline src config)
      putStrLn $ "\ESC[32mSuccess: target is emited as `" ++ tgtFile ++ "` \ESC[0m"
      where
        writeOrReportP :: Production Txt.Text -> IO ()
        writeOrReportP prod@(Production {pResult=res, pState=st, pDetail=details})  = do
          wrapUp <- case res of
            Left _ -> do
              forM_ (collectErrors prod) (pError . formatMethodError)
              return exitFailure
            Right txt -> do
              putStrLn "Pipeline Finished!\n"
              Txt.IO.writeFile tgtFile txt
              return (return ())
          putStrLn $ "Statistics from Codegen:\n" ++
            concatMap showEachSt st
          wrapUp

        formatMethodError (m, e) = printf "(\ESC[3m%s\ESC[0m\ESC[93m): %s" m e
        pError err = putStrLn $ "\ESC[31m[Error]\ESC[93m " ++ err ++ "\ESC[0m"

        showEachSt (v, st) =
          printf "\nThe final state of the method `%s`:\n%s\n" v (show st)
        srcFile = "./test/Resource/" ++ prog ++ ".qfy"
        tgtFile = "./test/Resource/" ++ prog ++ ".dfy"

-- loadDefaultFile :: IO String
-- loadDefaultFile =
--   let src = "./test/Resource/3.qfy" in
--     readFile src
