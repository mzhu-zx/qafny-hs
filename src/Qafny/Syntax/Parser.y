{
{-# LANGUAGE TypeFamilies, FlexibleContexts, FlexibleInstances #-}


module Qafny.Syntax.Parser(scanAndParse) where
import qualified Qafny.Syntax.Lexer as L
import           Qafny.Syntax.ParserUtils
import           Qafny.Syntax.AST
import           Control.Monad
import           Data.Sum
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
"at"                  { ( _, L.TAt      ) }
"split"               { ( _, L.TSplit      ) }
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
"repr"                { ( _, L.TRepr      ) }
"meas"                { ( _, L.TMea       ) }
"en"                  { ( _, L.TEN        ) }
"qreg"                { ( _, L.TQReg      ) }
"en01"                { ( _, L.TEN01      ) }
"var"                 { ( _, L.TVar       ) }
"if"                  { ( _, L.TIf        ) }
"λ"                   { ( _, L.TCl        ) }
"Σ"                   { ( _, L.TUnicodeSum    ) }
"⊗"                   { ( _, L.TUnicodeTensor ) }
"ω"                   { ( _, L.TUnicodeOmega ) }
"Ω"                   { ( _, L.TUnicodeSumOmega ) }
"∈"                   { ( _, L.TUnicodeIn     ) }
"↦"                   { ( _, L.TUnicodeMap    ) }
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
'_'                   { ( _, L.TWildcard  ) }
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
  : toplevels                         { $1                                   }
                                                                          
toplevels                                                                 
  : many(toplevel)                    { $1                                   }
                                                                          
toplevel  :: { Toplevel' }
  :  dafny                            { inj (QDafny $1) }
  | "method" id '(' bindings ')' "returns" '(' bindings ')' conds opt(block)                           
    {%  ((\(rs, es) -> inj (QMethod $2 $4 $8 rs es $11)) `fmap` (requireEnsures $10)) }
  | "method" id '(' bindings ')' conds opt(block)                                                  
    {%  ((\(rs, es) -> inj (QMethod $2 $4 [] rs es $7)) `fmap` (requireEnsures $6)) }

conds :: { [ Conds ] }
  : many(cond)                        { $1                                   }
                                                                          
cond :: { Conds }
  : "requires" expr                   { Requires $2                          }
  | "ensures" expr                    { Ensures $2                           }
  | "invariant" expr                  { Invariants $2                        }
  | "separates" partition             { Separates $2                         }

                                                                          
bindings
  : manyComma(binding)                     { $1 }

binding                                                                   
  : id ':' ty                         { Binding $1 $3                        }
                                                                          
ty                                                                        
  : "nat"                             { TNat                                 }
  | "int"                             { TInt                                 }
  | "bool"                            { TBool                                }
  | "seq" '<' ty '>'                  { TSeq $3                              }
  | "qreg" '[' digits ']'             { TQReg (ANat $3)                      }
  | "qreg" '[' id ']'                 { TQReg (AVar $3)                      }
          
qty :: { QTy }
  : "nor"                             { TNor                            }
  | "had"                             { THad                            }
  | "en"                              { TEN                             }
  | "en01"                            { TEN01                           }
                                                                
block                                                                     
  : '{' stmts '}'                     { Block $2                             }
                                                                          

stmts                                                                     
  : many(stmt)                        { $1                                   }
                                                                          
                                                                          
stmt :: { Stmt' }
  : dafny                             { SDafny $1                            }
  | "assert" expr ';'                 { SAssert $2                           }
  | "var" binding ';'                 { SVar $2 Nothing                      }
  | "var" binding ":=" expr ';'       { SVar $2 (Just $4)                    }
  | id ":=" expr ';'                  { $1 ::=: $3                           }
  | partition "*=" expr ';'           { $1 :*=: $3                           }
  | "if" '(' guardExpr ')' cond block
    {% do sep <- separatesOnly $5; return $ SIf $3 sep $6                    }
  | "for" id "in" '[' expr ".." expr ']' "with" guardExpr conds block
    {% do (invs, sep) <- invariantSeperates $11; return $ SFor $2 $5 $7 $10 invs sep $12 }
  | id tuple(expr) ';'                { SCall $1 $2 }


splitAt :: { Exp' }
  : "split" "at" expr                 { $3 }

guardExpr :: { GuardExp }
  : partition opt(splitAt)            { GEPartition $1 $2 }
                                                                          
partition :: { Partition }                                                               
  : manyComma(range)                  { Partition $ $1                       }
                                                                          
range                                                                     
  : id '[' expr ".." expr ']'         { Range $1 $3 $5                       }
                                                                
spec ::   { Exp' }
  : '{' partition ':'  qty "↦" qspec '}'
                                      { ESpec $2 $4 $6                       }

qspec ::  { (SpecExp', PhaseExp) }
  : "⊗" id '.' pspec tuple(expr)
                                      { (SESpecNor $2 $5, $4)                   }
  | "Σ" id "∈" '[' expr ".." expr ']' '.' pspec tuple(expr)
                                      { (SESpecEN $2 (Intv $5 $7) $11, $10)  }
  | "Σ" id "∈" '[' expr ".." expr ']' '.'             {- 9  -}
    pspec                                             {- 10 -}
    "⊗" id "∈" '[' expr ".." expr ']' '.'             {- 19 -}
    tuple(expr)
                                      { (SESpecEN01 $2 (Intv $5 $7) $12 (Intv $15 $17) $20, $10) }
  | '_'                               { (SEWildcard, PhaseZ) }

-- phase specification
pspec :: { PhaseExp }
  : {- empty -}                            { PhaseZ                 }
  | "ω" '(' expr ',' expr ')'              { PhaseOmega $3 $5       }
  | "Ω" id '.' '(' expr ',' expr ')'       { PhaseSumOmega $2 $5 $7 }


tuple(p)
  : '(' manyComma(p) ')'              { $2 }

expr                                                                      
  : atomic                            { $1                     }
  | '_'                               { EWildcard              }
  | spec                              { $1                     }
  | partition                         { EPartition $1          }
  | qops                              { $1                     }
  | "meas" id                         { EMea $2                }
  | "not" atomic                      { EOp1 ONot $2           }
  | "nor" '(' atomic ',' digits ')'   { EOp2 ONor $3 (ENum $5) }
  | "λ" '(' id "=>" expr ')'          { EEmit $ ELambda $3 $5  }
  | id tuple(expr)                    { EApp $1 $2             }
  | "repr" '(' range ')'              { ERepr $3               }
  | logicOrExp                        { $1                     }

qops
  : "H"                               { EHad                   }
  | "QFT"                             { EQFT                   }
  | "RQFT"                            { ERQFT                  }

logicOrExp :: { Exp' } 
  : logicAndExp "||" logicOrExp       { EOp2 OOr $1 $3         }
  | logicAndExp                       { $1 } 

logicAndExp :: { Exp' } 
  : cmpExpr "&&" logicAndExp          { EOp2 OAnd $1 $3        }
  | cmpExpr                           { $1 }

cmpPartial
 : cmp arithExpr  { ($1, $2) }

cmpExpr :: { Exp' }
 : arithExpr many(cmpPartial)         { unchainExps $1 $2  }

cmp :: { Op2 }
 : '>'                      { OGt }
 | '<'                      { OLt }
 | ">="                     { OGe }
 | "<="                     { OLe }

arithExpr :: { Exp' }
 : atomic arith arithExpr   { EOp2 $2 $1 $3 }
 | atomic                   { $1 }

arith :: { Op2 }
 : '+'                      { OAdd }
 | '-'                      { OSub }
 | '*'                      { OMul }
 | '\%'                     { OMod }

atomic                                                                      
  : digits                            { ENum $1                }
  | id                                { EVar $1                }
  | '(' expr ')'                      { $2                     }


-- | Combinators 
many(p)                                                                  
  : many_(p)                          { reverse $1 }
                                                                          
many_(p)
  : {- empty -}                       { []      }
  | many_(p) p                        { $2 : $1 }

manyComma(p)                                                                  
  : manyComma_(p)                     { reverse $1 }
                                                                          
manyComma_(p)
  : {- empty -}                       { []      }
  | p                                 { [$1]    }
  | manyComma_(p) ',' p               { $3 : $1 }
    
opt(p)
  : {- empty -}                       { Nothing }
  | p                                 { Just $1 }

{
scanAndParse :: String -> Parser AST
scanAndParse = runParser <=< L.runScanner
}
