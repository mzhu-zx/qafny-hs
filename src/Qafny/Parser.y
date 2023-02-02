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
dafny      { L.TDafny $$  }
ident      { L.TId $$      }
"method"   { L.TMethod    }
"ensures"  { L.TEnsures   }
"requires" { L.TRequires  }
'|'        { L.TBar       }
'('        { L.TLPar      }
')'        { L.TRPar      }
'{'        { L.TLBrace    }
'}'        { L.TRBrace    }
"returns"  { L.TReturns   }
"nat"      { L.TNat       }
"int"      { L.TInt       }
"bool"     { L.TBool      }
"seq"      { L.TSeq       }
"nor"      { L.TNor       }
"had"      { L.THad       }
"ch"       { L.TCH        }
','        { L.TComma     }
':'        { L.TColon     }

%%
AST
  : toplevels               { $1 }

toplevels
  : toplevel                { [$1] }
  | toplevels toplevel      { $2 : $1 }
  
toplevel
  :  dafny                  { QDafny $1 }
  | "method" id '(' bindings ')' "returns" '(' bindings ')'  
                            { QMethod $2 $4 $8 [] [] [] }

bindings
  : binding                 { [$1] }
  | bindings ',' binding    { $2 : $1 }

binding
  : id ':' ty               { Binding $1 $3 }

id
  : ident                   { $1 }

ty
  : "nat"                   { TNat }
  | "int"                   { TInt }
  | "bool"                  { TBool }
  | "seq" ty                { TSeq $2 }
  | "nor"                   { TNor }
  | "had"                   { THad }
  | "ch"                    { TCH }

{
type Parser a = Either String a

parseError :: [L.Token] -> Parser a
parseError [] = Left "Expect more tokens"
parseError xs = Left $ show $ take 1 xs

scanAndParse :: String -> Parser AST
scanAndParse = runParser <=< L.runScanner

}
