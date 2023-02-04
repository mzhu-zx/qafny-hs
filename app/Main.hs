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
     let ir = runGen $ gen ast
     return $ texify ir

main :: IO ()
main = 
  let src = "./test/Resource/3.qfy"
      tgt = "./test/Resource/3.dfy" 
  in
    do s <- readFile src
       case pipeline s of
         Left e -> die e
         Right t -> 
           Txt.writeFile tgt t

-- main :: IO ()
-- main = 
--   let src = "./test/Resource/2.qfy"
--       tgt = "./test/Resource/2.dfy" 
--   in
--     do s <- readFile src
--        let Right toks = runScanner s
--        print toks

