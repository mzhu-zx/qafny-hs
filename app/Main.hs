module Main (main) where

-- import           Qafny.AST
import           Qafny.Parser(scanAndParse)
import           Qafny.Codegen(codegen)
import           Qafny.Emit(texify)
import           Qafny.Transform(TState)

import           Data.Text.Lazy
import qualified Data.Text.Lazy.IO as Txt

pipeline :: String -> Either String (Text, TState)
pipeline s =
  do ast <- scanAndParse s
     let (result, state, _) = codegen ast
     ir <- result
     return $ (texify ir, state)

main :: IO ()
main = 
  do s <- readFile src
     writeOrReport $ pipeline s
     putStrLn $ "\ESC[32mSuccess: target is emited as `" ++ tgt ++ "` \ESC[0m"
     where writeOrReport (Right (txt, st)) = 
             do
               putStrLn $ "Pipeline Finished!\nStatistics from Codegen:\n" ++ show st
               Txt.writeFile tgt txt
           writeOrReport (Left e) = putStrLn ("\ESC[31m[Error]\ESC[93m " ++
                                              e ++ "\ESC[0m")
           src = "./test/Resource/3.qfy"
           tgt = "./test/Resource/3.dfy" 

loadDefaultFile :: IO String
loadDefaultFile = 
  let src = "./test/Resource/3.qfy" in
    readFile src
