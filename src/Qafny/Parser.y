{
module Qafny.Parser(scanAndParse) where
import qualified Qafny.Lexer as L
import Qafny.AST
import Control.Monad

}

%name runParser
%tokentype { L.Token }
%error { parseError }
%monad { Parser }{ >>= }{ return }

%token
dafny                  { L.TDafny $$ }

%%
AST
  : Toplevels          { $1 }

Toplevels
  : Toplevel           { [$1] }
  | Toplevels Toplevel { $2 : $1 }
  
Toplevel
  :  dafny             { QDafny $1 }

{
type Parser a = Either String a

parseError :: [L.Token] -> Parser a
parseError [] = Left "Expect more tokens"
parseError xs = Left $ show $ take 1 xs

scanAndParse :: String -> Parser AST
scanAndParse = runParser <=< L.runScanner

}
