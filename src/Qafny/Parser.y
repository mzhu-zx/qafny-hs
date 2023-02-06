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
digits     { L.TLitInt $$ }
dafny      { L.TDafny $$  }
"method"   { L.TMethod    }
"ensures"  { L.TEnsures   }
"requires" { L.TRequires  }
"||"        { L.TOr       }
"&&"        { L.TAnd      }
'+'        { L.TAdd       }
'*'        { L.TMul      }
'\%'        { L.TMod     }
'|'        { L.TBar       }
'('        { L.TLPar      }
')'        { L.TRPar      }
'<'        { L.TLAng      }
'>'        { L.TRAng      }
'['        { L.TLBracket   }
']'        { L.TRBracket    }
'{'        { L.TLBrace    }
'}'        { L.TRBrace    }
"returns"  { L.TReturns   }
"not"      { L.TNot       }
"nat"      { L.TNat       }
"int"      { L.TInt       }
"bool"     { L.TBool      }
"seq"      { L.TSeq       }
"nor"      { L.TNor       }
"had"      { L.THad       }
 "H"       { L.THApp  }
 "QFT"     { L.TQFT  }
 "RQFT"    { L.TRQFT  }
 "meas"    { L.TMea  }
"ch"       { L.TCH        }
"var"      { L.TVar  }
"if"       { L.TIf  }
"assert"   { L.TAssert    }
id         { L.TId $$     }
','        { L.TComma     }
':'        { L.TColon     }
';'        { L.TSemi      }
"=="       { L.TEq        }
":="       { L.TAssign    }
"*="       { L.TApply    }
".."       { L.TDot    }

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
  | "nor"                   { TQ $ TNor }
  | "had"                   { TQ $ THad }
  | "ch"                    { TQ $ TCH }

block
  : '{' stmts '}'           { $2 }

stmts
  : stmts_                  { reverse $1 }

stmts_ 
  : stmt                    { [$1] }
  | stmts_ stmt             { $2 : $1 }
 

stmt
  : "assert" expr ';'           { SAssert $2 }
  | "var" binding ';'           { SVar $2 Nothing }
  | "var" binding ":=" expr ';' { SVar $2 (Just $4) }
  | id ":=" expr ';'            { SAssign $1 $3  }
  | session "*=" expr ';'       { SApply $1 $3  }
  | "if" expr block             { SIf $2 $3 }

session
  : range {$1}
  | range session {$1 ++ $2}

range 
  : id '[' atomic ".." atomic ']' {(Ran $1 $3 $5):[] }

expr
  : atomic                             { $1 }
  | "H"                              {EHad }
  | "QFT"                              {EQFT }
  | "RQFT"                              {ERQFT }
  | "meas" id                            {EMea $2}
  | "not" atomic                        { EOp1 ONot $2 }
  | id '(' atomic ')'              { EApp $1 $3 }
  | atomic '+' atomic                 { EOp2 OAdd $1 $3 }
  | atomic "&&" atomic                 { EOp2 OAnd $1 $3 }
  | atomic "||" atomic                  { EOp2 OOr $1 $3 }
  | atomic '*' atomic                 { EOp2 OMul $1 $3 }
  | atomic '*' atomic '\%' atomic     { EOp2 OMod (EOp2 OMul $1 $3) $5 }

atomic
  : digits                             { ENum $1 }
  | id                                 { EVar $1 }

{
type Parser a = Either String a

parseError :: [L.Token] -> Parser a
parseError [] = Left "Parser Error: Expect more tokens"
parseError xs = Left $ "Parser Error: " ++ (show $ xs)

scanAndParse :: String -> Parser AST
scanAndParse = runParser <=< L.runScanner
}
