{
module Qafny.Parser(scanAndParse) where
import qualified Qafny.Lexer as L
import           Qafny.ParserUtils
import           Qafny.AST
import           Control.Monad
}

%name runParser
%tokentype { L.Token }
%error { parseError }
%monad { Parser }{ >>= }{ return }

%token
digits                { L.TLitInt $$  }
dafny                 { L.TDafny $$   }
"method"              { L.TMethod     }
"ensures"             { L.TEnsures    }
"requires"            { L.TRequires   }
"separates"           { L.TSeparates  }
"invariants"          { L.TInv        }
"with"                { L.TWith       }
"for"                 { L.TFor        }
"returns"             { L.TReturns    }
"not"                 { L.TNot        }
"nat"                 { L.TNat        }
"int"                 { L.TInt        }
"in"                  { L.TIn         }
"bool"                { L.TBool       }
"seq"                 { L.TSeq        }
"nor"                 { L.TNor        }
"had"                 { L.THad        }
"H"                   { L.THApp       }
"QFT"                 { L.TQFT        }
"RQFT"                { L.TRQFT       }
"meas"                { L.TMea        }
"ch"                  { L.TCH         }
"var"                 { L.TVar        }
"if"                  { L.TIf         }
"λ"                   { L.TCl         }
"assert"              { L.TAssert     }
"||"                  { L.TOr         }
"&&"                  { L.TAnd        }
'+'                   { L.TAdd        }
'*'                   { L.TMul        }
'\%'                  { L.TMod        }
'|'                   { L.TBar        }
'('                   { L.TLPar       }
')'                   { L.TRPar       }
'<'                   { L.TLAng       }
'>'                   { L.TRAng       }
'['                   { L.TLBracket   }
']'                   { L.TRBracket   }
'{'                   { L.TLBrace     }
'}'                   { L.TRBrace     }
id                    { L.TId $$      }
','                   { L.TComma      }
':'                   { L.TColon      }
';'                   { L.TSemi       }
"=="                  { L.TEq         }
"=>"                  { L.TArrow      }
":="                  { L.TAssign     }
"*="                  { L.TApply      }
".."                  { L.TDot        }

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
{-  : "separates" session               {% separatesOnly $1                    } -}

conds
  : {- empty -}                       { []                                   }
  | conds cond                        { $2 : $1                              }
                                                                          
cond                                                                      
  : "requires" expr                   { Requires $2                          }
  | "ensures" expr                    { Ensures $2                           }
  | "invariants" expr                 { Invariants $2                        }
                                                                          
bindings                                                                  
  : bindings_                         { reverse $1                           }
                                                                          
bindings_                                                                 
  : {- empty -}                       { []                                   }
  | binding                           { [$1]                                 }
  | bindings_ ',' binding             { $3 : $1                              }
                                                                          
binding                                                                   
  : id ':' ty                         { Binding $1 $3                        }
                                                                          
ty                                                                        
  : "nat"                             { TNat                                 }
  | "int"                             { TInt                                 }
  | "bool"                            { TBool                                }
  | "seq" '<' ty '>'                  { TSeq $3                              }
  | "nor"                             { TQ $ TNor                            }
  | "had"                             { TQ $ THad                            }
  | "ch"                              { TQ $ TCH                             }
                                                                          

blockOpt                                                                     
  : {- empty -}                       { Nothing                              }
  | block                             { Just $1                              }

block                                                                     
  : '{' stmts '}'                     { Block $2                             }
                                                                          
stmts                                                                     
  : stmts_                            { reverse $1                           }
                                                                          
stmts_                                                                    
  : {- empty -}                       { []                                   }
  | stmts_ stmt                       { $2 : $1                              }
                                                                          
                                                                          
stmt                                                                      
  : "assert" expr ';'                 { SAssert $2                           }
  | "var" binding ';'                 { SVar $2 Nothing                      }
  | "var" binding ":=" expr ';'       { SVar $2 (Just $4)                    }
  | id ":=" expr ';'                  { SAssign $1 $3                        }
  | session "*=" expr ';'             { SApply $1 $3                         }
  | "if" '(' expr ')' separates block
                                      { SIf $3 $5 $6                         }
  | "for" id "in" '[' atomic ".." atomic ']' "with" expr invs separates block
                                      { SFor $2 $5 $7 $10 $11 $12 $13        }
                                                                          
session :: { Session }                                                               
  : session_                          { Session $ reverse $1                 }
                                                                          
session_                                                                  
  : range                             { [$1]                                 }
  | session_ range                    { $2 : $1                              }
                                                                          
range                                                                     
  : id '[' expr ".." expr ']'         { Range $1 $3 $5                       }
                                                                          
expr                                                                      
  : atomic                            { $1                                   }
  | session                           { ESession $1                          }
  | "H"                               { EHad                                 }
  | "QFT"                             { EQFT                                 }
  | "RQFT"                            { ERQFT                                }
  | "meas" id                         { EMea $2                              }
  | "not" atomic                      { EOp1 ONot $2                         }
  | "nor" '(' atomic ',' digits ')'   { EOp2 ONor $3 (ENum $5)               }
  | "λ" '(' id "=>" expr ')'          { EEmit $ ELambda $3 $5                }
  | id '(' atomic ')'                 { EApp $1 $3                           }
  | atomic '+' atomic                 { EOp2 OAdd $1 $3                      }
  | atomic "&&" atomic                { EOp2 OAnd $1 $3                      }
  | atomic "||" atomic                { EOp2 OOr $1 $3                       }
  | atomic '*' atomic                 { EOp2 OMul $1 $3                      }
  | expr '\%' expr                    { EOp2 OMod $1 $3                      }
  | expr '>' expr                     { EOp2 OGt $1 $3                      }
  | '(' expr ')'                      { $2                                   }
                                                                            
atomic                                                                      
  : digits                            { ENum $1                              }
  | id                                { EVar $1                              }

{
scanAndParse :: String -> Parser AST
scanAndParse = runParser <=< L.runScanner
}
