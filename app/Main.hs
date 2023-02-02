module Main (main) where

import Qafny.Parser(scanAndParse)
import Qafny.Codegen(gen, runGen)
import System.Exit
import Data.Text
import qualified Data.Text.IO as Txt
import Qafny.AST (DafnyPrinter(texify))


pipeline :: String -> Either String Text
pipeline s =
  do ast <- scanAndParse s 
     let ir = runGen $ gen ast
     return $ texify ir


main :: IO ()
main = 
  let src = "/home/mzhu/qafny-hs/test/Resource/1.qfy"
      tgt = "/home/mzhu/qafny-hs/test/Resource/1.dfy" 
  in
    do s <- readFile src
       case pipeline s of
         Left e -> die e
         Right t -> -- Txt.writeFile tgt t
           print  t
