{
module Qafny.Parser(AST, parse) where
import qualified Qafny.Lexer as L
import Qafny.AST
}

%name qafny
%tokentype { L.Token }
%error { parseError }
%monad { Either String }{ >>= }{ return }

%token
dafny { L.TDafny $$ }

%%
AST
  : dafny { [QDafny $1] }

-- Toplevel
--   : "method" 

-- Binding
--   : 

{

parseError :: [L.Token] -> Either String a
parseError [] = Left "End of Token List"
parseError xs = Left $ show $ take 1 xs

parse :: String -> Either String AST
parse s = do ts <- L.runScanner s
             qafny $ take 1 ts
}
