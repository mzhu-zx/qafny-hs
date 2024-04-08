{-# LANGUAGE
    OverloadedStrings
  #-}

module Main (main) where

import           Control.Monad
    (forM_, unless)
import           Data.Text.Lazy
    (Text)
import qualified Data.Text.Lazy      as L
import qualified Data.Text.Lazy.IO   as L.IO

import           Qafny.Config
import           Qafny.FileUtils
    (countDepth)
import           Qafny.Runner
    (Production (..), collectErrors, produceCodegen)
import           Qafny.Syntax.Emit
    (prettyIO, texify)
import           Qafny.Syntax.Parser
    (scanAndParse)
import           System.Directory
    (doesFileExist)
import           System.Environment
    (getArgs)
import           System.Exit
    (exitFailure)
import           System.FilePath
    ((-<.>))
import           Text.Printf
    (PrintfType, printf)

pathPrefix :: FilePath
pathPrefix = "./test/Resource/"

parseFilepath :: FilePath -> (FilePath, Int)
parseFilepath path = (path, countDepth path)

help :: Text
help =
  "\
  \Usage:\n\
  \  qafny [command] <file>\n\
  \Commands:\n\
  \  help             Show usage.\n\
  \  verify <file>    Translate the program to Dafny.\n\
  \  format <file>    Scan, parse, and print the formatted program to stdout.\
  \"

parseArgs :: IO (FilePath, Mode)
parseArgs = do
  args <- getArgs
  (path, mode) <- case args of
    []            -> showUsage
    ["help"]      -> showUsage
    ["verify", s] -> return (s, Verify)
    ["format", s] -> return (s, Format)
    [s] | s `elem` ["verify", "format"] ->
          pError "No input file was specified." >> exitFailure
    [s] -> return (srcFile s, Verify)
    _   -> exitUnknownCmd args
  exists <- doesFileExist path
  unless exists $
    pErrorf "The input file %s doesn't exist." path >> exitFailure

  return (path, mode)
  where
    showUsage =
      L.IO.putStrLn help >> exitFailure
    exitUnknownCmd args =
      pErrorf "Unknown command: %s" (unwords args)
      >> L.IO.putStrLn help
      >> exitFailure
    srcFile s = pathPrefix ++ s ++ ".qfy"

pipeline :: FilePath -> Configs -> Either String (IO (Production L.Text))
pipeline s configs =
  -- do parsing, rethrow error if any
  withAST <$> scanAndParse s
  where
    withAST ast = do
      let prod = produceCodegen configs ast
      -- print trace
      putStr $ pTrace prod
      return $ prod { pResult = texify <$> pResult prod }

main :: IO ()
main =
  do
    (path, mode) <- parseArgs
    let (prog, depth) = parseFilepath path
    withProg prog (defaultConfigs { depth, mode })


withProg :: FilePath -> Configs -> IO ()
withProg srcFile config@Configs{mode=Format} = do
  printf "[Info] format %s\n" srcFile
  src <- readFile srcFile
  case scanAndParse src of
    Left s  -> pError s
    Right p ->
      putStrLn "============================================================"
      >> prettyIO p

withProg srcFile config@Configs{mode=Verify} = do
  printf "[Info] verify %s\n" srcFile
  srcText <- readFile srcFile
  either ((>> exitFailure) . putStrLn) (>>= writeOrReportP)
    (pipeline srcText config)
  putStrLn $ "\ESC[32mSuccess: target is emited as `" ++ tgtFile ++ "` \ESC[0m"
  where
    writeOrReportP :: Production L.Text -> IO ()
    writeOrReportP prod@(Production {pResult=res, pState=st, pDetail=details})  = do
      wrapUp <- case res of
        Left txt -> do
          if null (pDetail prod)
            then pError txt
            else forM_ (collectErrors prod) (pError . formatMethodError)
          return exitFailure
        Right txt -> do
          putStrLn "Pipeline Finished!\n"
          L.IO.writeFile tgtFile txt
          return (return ())
      putStrLn $ "Statistics from Codegen:\n" ++
        concatMap showEachSt st
      wrapUp

    formatMethodError (m, e) = printf "(\ESC[3m%s\ESC[0m\ESC[93m): %s" m e
    showEachSt (v, st) =
      printf "\nThe final state of the method `%s`:\n%s\n" v (show st)
    tgtFile = srcFile -<.> "dfy"


pError :: String -> IO ()
pError err = putStrLn $ "\ESC[31m[Error]\ESC[93m " ++ err ++ "\ESC[0m\n"

pErrorf :: PrintfType r => String -> r
pErrorf s = printf ("\ESC[31m[Error]\ESC[93m " ++ s ++ "\ESC[0m\n")
