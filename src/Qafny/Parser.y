{
module Qafny.Parser(scanAndParse) where
import qualified Qafny.Lexer as L
import           Qafny.ParserUtils
import           Qafny.AST
import           Control.Monad
}

%name runParser
%tokentype { L.SToken }
%error { parseError }
%monad { Parser }{ >>= }{ return }

%token
digits                { ( _, L.TLitInt $$ ) }
dafny                 { ( _, L.TDafny $$  ) }
"method"              { ( _, L.TMethod    ) }
"ensures"             { ( _, L.TEnsures   ) }
"requires"            { ( _, L.TRequires  ) }
"separates"           { ( _, L.TSeparates ) }
"invariant"           { ( _, L.TInv       ) }
"with"                { ( _, L.TWith      ) }
"for"                 { ( _, L.TFor       ) }
"returns"             { ( _, L.TReturns   ) }
"not"                 { ( _, L.TNot       ) }
"nat"                 { ( _, L.TNat       ) }
"int"                 { ( _, L.TInt       ) }
"in"                  { ( _, L.TIn        ) }
"bool"                { ( _, L.TBool      ) }
"seq"                 { ( _, L.TSeq       ) }
"nor"                 { ( _, L.TNor       ) }
"had"                 { ( _, L.THad       ) }
"H"                   { ( _, L.THApp      ) }
"QFT"                 { ( _, L.TQFT       ) }
"RQFT"                { ( _, L.TRQFT      ) }
"meas"                { ( _, L.TMea       ) }
"ch"                  { ( _, L.TCH        ) }
"var"                 { ( _, L.TVar       ) }
"if"                  { ( _, L.TIf        ) }
"λ"                   { ( _, L.TCl        ) }
"Σ"                   { ( _, L.TUnicodeSum        ) }
"∈"                   { ( _, L.TUnicodeIn        ) }
"↦"                   { ( _, L.TUnicodeMap        ) }
"assert"              { ( _, L.TAssert    ) }
"||"                  { ( _, L.TOr        ) }
"&&"                  { ( _, L.TAnd       ) }
'+'                   { ( _, L.TAdd       ) }
'-'                   { ( _, L.TSub       ) }
'*'                   { ( _, L.TMul       ) }
'\%'                  { ( _, L.TMod       ) }
'|'                   { ( _, L.TBar       ) }
'('                   { ( _, L.TLPar      ) }
')'                   { ( _, L.TRPar      ) }
'<'                   { ( _, L.TLAng      ) }
'>'                   { ( _, L.TRAng      ) }
'['                   { ( _, L.TLBracket  ) }
']'                   { ( _, L.TRBracket  ) }
'{'                   { ( _, L.TLBrace    ) }
'}'                   { ( _, L.TRBrace    ) }
id                    { ( _, L.TId $$     ) }
','                   { ( _, L.TComma     ) }
':'                   { ( _, L.TColon     ) }
'.'                   { ( _, L.TDot       ) }
';'                   { ( _, L.TSemi      ) }
"=="                  { ( _, L.TEq        ) }
"=>"                  { ( _, L.TArrow     ) }
">="                  { ( _, L.TGe        ) }
"<="                  { ( _, L.TLe        ) }
":="                  { ( _, L.TAssign    ) }
"*="                  { ( _, L.TApply     ) }
".."                  { ( _, L.TDots      ) }

%%
AST
  : toplevels                         { reverse $1                           }
                                                                          
toplevels                                                                 
  : toplevel                          { [$1]                                 }
  | toplevels toplevel                { $2 : $1                              }
                                                                          
toplevel                                                                  
  :  dafny                            { QDafny $1                            }
  | "method" id '(' bindings ')'                                          
    requireEnsures blockOpt                                                  
                                      { let (rs, es) = $6 in                 
                                          QMethod $2 $4 [] rs es $7          }
  | "method" id '(' bindings ')' "returns" '(' bindings ')'               
    requireEnsures blockOpt                                                  
                                      { let (rs, es) = $10 in                
                                          QMethod $2 $4 $8 rs es $11         }

requireEnsures
  : conds                             { (reverse [e | (Requires e) <- $1], 
                                         reverse [e | (Ensures  e) <- $1])   }
invs
  : conds                             { reverse [e | (Invariants e) <- $1]   }

separates :: { Session }
  : "separates" session               { $2                                   }

conds
  : {- empty -}                       { []                                   }
  | conds cond                        { $2 : $1                              }
                                                                          
cond                                                                      
  : "requires" expr                   { Requires $2                          }
  | "ensures" expr                    { Ensures $2                           }
  | "invariant" expr                  { Invariants $2                        }
                                                                          
bindings
  : manyComma(binding)                     { $1 }

manyComma(p)                                                                  
  : manyComma_(p)                     { reverse $1                           }
                                                                          
manyComma_(p)
  : {- empty -}                       { []                                   }
  | p                                 { [$1]                                 }
  | manyComma_(p) ',' p               { $3 : $1                              }
                                                                          
binding                                                                   
  : id ':' ty                         { Binding $1 $3                        }
                                                                          
ty                                                                        
  : "nat"                             { TNat                                 }
  | "int"                             { TInt                                 }
  | "bool"                            { TBool                                }
  | "seq" '<' ty '>'                  { TSeq $3                              }
  | qty                               { TQ $ $1 }
          
qty :: { QTy }
  : "nor"                             { TNor                            }
  | "had"                             { THad                            }
  | "ch"                              { TCH                             }
                                                                

blockOpt                                                                     
  : {- empty -}                       { Nothing                              }
  | block                             { Just $1                              }

block                                                                     
  : '{' stmts '}'                     { Block $2                             }
                                                                          

many(p)                                                                  
  : many_(p)                          { reverse $1                           }
                                                                          
many_(p)
  : {- empty -}                       { []                                   }
  | many_(p) p                        { $2 : $1                              }


stmts                                                                     
  : many(stmt)                        { reverse $1                           }
                                                                          
                                                                          
stmt                                                                      
  : "assert" expr ';'                 { SAssert $2                           }
  | "var" binding ';'                 { SVar $2 Nothing                      }
  | "var" binding ":=" expr ';'       { SVar $2 (Just $4)                    }
  | id ":=" expr ';'                  { SAssign $1 $3                        }
  | session "*=" expr ';'             { SApply $1 $3                         }
  | "if" '(' expr ')' separates block
                                      { SIf $3 $5 $6                         }
  | "for" id "in" '[' expr ".." expr ']' "with" expr invs separates block
                                      { SFor $2 $5 $7 $10 $11 $12 $13        }
                                                                          
session :: { Session }                                                               
  : session_                          { Session $ reverse $1                 }
                                                                          
session_                                                                  
  : range                             { [$1]                                 }
  | session_ range                    { $2 : $1                              }
                                                                          
range                                                                     
  : id '[' expr ".." expr ']'         { Range $1 $3 $5                       }
                                                                
spec ::   { Exp }
  : '{' session ':'  qty "↦" qspec '}' { ESpec $2 $4 $6                      }

qspec ::  { Exp }
  : "Σ" id "∈" '[' expr ".." expr ']' '.' tuple(expr)
                                      { EQSpec $2 (Intv $5 $7) $10    }

tuple(p)
  : '(' manyComma(p) ')'              { $2 }

expr                                                                      
  : atomic                            { $1                     }
  | spec                              { $1                     }
  | session                           { ESession $1            }
  | "H"                               { EHad                   }
  | "QFT"                             { EQFT                   }
  | "RQFT"                            { ERQFT                  }
  | "meas" id                         { EMea $2                }
  | "not" atomic                      { EOp1 ONot $2           }
  | "nor" '(' atomic ',' digits ')'   { EOp2 ONor $3 (ENum $5) }
  | "λ" '(' id "=>" expr ')'          { EEmit $ ELambda $3 $5  }
  | id '(' atomic ')'                 { EApp $1 $3             }
  | atomic "&&" atomic                { EOp2 OAnd $1 $3        }
  | atomic "||" atomic                { EOp2 OOr $1 $3         }
  | cmpExpr                           { $1                     }
  | arithExpr                         { $1                     }
  | '(' expr ')'                      { $2                     }

cmpExpr :: { Exp }
 : expr cmp expr            { EOp2 $2 $1 $3 }

cmp :: { Op2 }
 : '>'                      { OGt }
 | '<'                      { OLt }
 | ">="                     { OGe }
 | "<="                     { OLe }

arithExpr :: { Exp }
 : expr arith expr            { EOp2 $2 $1 $3 }

arith :: { Op2 }
 : '+'                      { OAdd }
 | '-'                      { OSub }
 | '*'                      { OMul }
 | '\%'                     { OMod }


atomic                                                                      
  : digits                            { ENum $1                              }
  | id                                { EVar $1                              }

{
scanAndParse :: String -> Parser AST
scanAndParse = runParser <=< L.runScanner
}
