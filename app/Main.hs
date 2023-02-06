module Main (main) where

import           Qafny.AST
import           Qafny.Parser(scanAndParse)
import           Qafny.Codegen(gen, runGen, TState)

import           Data.Text.Lazy
import qualified Data.Text.Lazy.IO as Txt

pipeline :: String -> Either String (Text, TState)
pipeline s =
  do ast <- scanAndParse s
     let (result, state) = runGen $ gen ast
     ir <- result
     return $ (texify ir, state)

main :: IO ()
main = 
  do s <- readFile src
     writeOrReport $ pipeline s
     where writeOrReport (Right (txt, st)) = 
             do
               putStrLn $ "Pipeline Finished!\nStatistics from Codegen:\n" ++ show st
               Txt.writeFile tgt txt
           writeOrReport (Left e) = putStrLn ("[Error] " ++ e)
           src = "./test/Resource/3.qfy"
           tgt = "./test/Resource/3.dfy" 

loadDefaultFile :: IO String
loadDefaultFile = 
  let src = "./test/Resource/3.qfy" in
    readFile src
