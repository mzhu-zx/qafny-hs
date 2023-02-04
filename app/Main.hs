module Main (main) where

import Qafny.Parser(scanAndParse)
import Qafny.Codegen(gen, runGen)
import System.Exit
import Data.Text.Lazy
import qualified Data.Text.Lazy.IO as Txt
import Qafny.AST

pipeline :: String -> Either String Text
pipeline s =
  do ast <- scanAndParse s 
     ir <- runGen $ gen ast
     return $ texify ir

main :: IO ()
main = 
  do s <- readFile src
     writeOrReport $ pipeline s
     where writeOrReport (Right txt) = Txt.writeFile tgt txt
           writeOrReport (Left e) = putStrLn ("[Error] " ++ e)
           src = "./test/Resource/3.qfy"
           tgt = "./test/Resource/3.dfy" 

loadDefaultFile :: IO String
loadDefaultFile = 
  let src = "./test/Resource/3.qfy" in
    readFile src

-- let src = "./test/Resource/DeutschJozsa.qfy"
--     tgt = "./test/Resource/DeutschJozsa.dfy" 
-- main :: IO ()
-- main = 
--   let src = "./test/Resource/2.qfy"
--       tgt = "./test/Resource/2.dfy" 
--   in
--     do s <- readFile src
--        let Right toks = runScanner s
--        print toks

