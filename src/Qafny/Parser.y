{
module Qafny.Parser(scanAndParse) where
import qualified Qafny.Lexer as L
import Qafny.AST
import Control.Monad
import Debug.Trace
}

%name runParser
%tokentype { L.Token }
%error { parseError }
%monad { Parser }{ >>= }{ return }

%token
digits     { L.TLitInt $$ }
dafny      { L.TDafny $$  }
"method"   { L.TMethod    }
"ensures"  { L.TEnsures   }
"requires" { L.TRequires  }
'|'        { L.TBar       }
'('        { L.TLPar      }
')'        { L.TRPar      }
'<'        { L.TLAng      }
'>'        { L.TRAng      }
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
id         { L.TId $$     }
','        { L.TComma     }
':'        { L.TColon     }

%%
AST
  : toplevels               { reverse $1 }

toplevels
  : toplevel                { [$1] }
  | toplevels toplevel      { $2 : $1 }
  
toplevel
  :  dafny                  { QDafny $1 }
  | "method" id '(' bindings ')'
    requireEnsures 
                            { let (rs, es) = $6 in 
                                  QMethod $2 $4 [] rs es [] }
  | "method" id '(' bindings ')' "returns" '(' bindings ')'
    requireEnsures 
                            { let (rs, es) = $10 in 
                                  QMethod $2 $4 $8 rs es [] }

requireEnsures
  : conds                   { (reverse [e | (Requires e) <- $1], 
                               reverse [e | (Ensures  e) <- $1]) }

conds
  : {- empty -}             { [] }
  | conds cond              { $2 : $1 }

cond
  : "requires" expr         { Requires $2 }
  | "ensures" expr          { Ensures $2 }


bindings
  : bindings_               { reverse $1 }

bindings_
  : {- empty -}             { [] }
  | binding                 { [$1] }
  | bindings_ ',' binding   { $3 : $1 }

binding
  : id ':' ty               { Binding $1 $3 }

ty
  : "nat"                   { TNat }
  | "int"                   { TInt }
  | "bool"                  { TBool }
  | "seq" '<' ty '>'        { TSeq $3 }
  | "nor"                   { TNor }
  | "had"                   { THad }
  | "ch"                    { TCH }

expr
  : digits                  { ENum $1 }


{
type Parser a = Either String a

parseError :: [L.Token] -> Parser a
parseError [] = Left "Parser Error: Expect more tokens"
parseError xs = Left $ "Parser Error: " ++ (show $ xs)

scanAndParse :: String -> Parser AST
scanAndParse = runParser <=< L.runScanner
}
