{
{-# LANGUAGE
    TypeFamilies
  , FlexibleContexts
  , FlexibleInstances
  , NamedFieldPuns

  #-}


module Qafny.Syntax.Parser(scanAndParse) where
import qualified Qafny.Syntax.Lexer as L
import           Qafny.Syntax.ParserUtils
import           Qafny.Syntax.AST
import           Control.Monad
import           Data.Sum
import           Data.Maybe
}

%name runParser
%tokentype { L.SToken }
%error { parseError }
%errorhandlertype explist
%monad { Parser }{ >>= }{ return }

%token
'_'                   { ( _, L.TWildcardName ""  ) }
'1'                 { ( _, L.TWildcardName "1" ) }
'S'                   { ( _, L.TWildcardName "_S" ) }
'T'                   { ( _, L.TWildcardName "_T" ) }
'o'                   { ( _, L.TWildcardName "_o" ) }
'O'                   { ( _, L.TWildcardName "_O" ) }

namedW                { ( _, L.TWildcardName $$ ) }
digits                { ( _, L.TLitInt $$ ) }
dafny                 { ( _, L.TDafny $$  ) }
"method"              { ( _, L.TMethod    ) }
"ensures"             { ( _, L.TEnsures   ) }
"requires"            { ( _, L.TRequires  ) }
"separates"           { ( _, L.TSeparates ) }
"invariant"           { ( _, L.TInv       ) }
"with"                { ( _, L.TWith      ) }
"at"                  { ( _, L.TAt        ) }
"split"               { ( _, L.TSplit     ) }
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
"Qft"                 { ( _, L.TQFT       ) }
"iQft"                { ( _, L.TRQFT      ) }
"repr"                { ( _, L.TRepr      ) }
"measure"             { ( _, L.TMeasure   ) }
"measured"            { ( _, L.TMeasured  ) }
"en"                  { ( _, L.TEn        ) }
"qreg"                { ( _, L.TQReg      ) }
"en01"                { ( _, L.TEn01      ) }
"var"                 { ( _, L.TVar       ) }
"if"                  { ( _, L.TIf        ) }

"isqrt"               { ( _, L.TISqrt     ) }
"sin"                 { ( _, L.TSin       ) }
"cos"                 { ( _, L.TCos       ) }


"λ"                   { ( _, L.TCl            ) }
"Σ"                   { ( _, L.TUnicodeSum    ) }
"⊗"                   { ( _, L.TUnicodeTensor ) }
"ω"                   { ( _, L.TUnicodeOmega  ) }
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
','                   { ( _, L.TComma     ) }
':'                   { ( _, L.TColon     ) }
'.'                   { ( _, L.TDot       ) }
';'                   { ( _, L.TSemi      ) }
"=="                  { ( _, L.TEq        ) }
'->'                  { ( _, L.TTyArrow   ) }
"=>"                  { ( _, L.TArrow     ) }
">="                  { ( _, L.TGe        ) }
"<="                  { ( _, L.TLe        ) }
":="                  { ( _, L.TAssign    ) }
"*="                  { ( _, L.TApply     ) }
".."                  { ( _, L.TDots      ) }
'~'                   { ( _, L.TTilde     ) }

%expect 0
%right '->' 

%%
AST
  : toplevels                         { $1                                   }
                                                                          
toplevels                                                                 
  : many(toplevel)                    { $1                                   }
                                                                          
toplevel  :: { Toplevel' }
  :  dafny                            { inj (QDafny $1) }
  | "method" id parens(bindings) returns conds opt(block)                           
    {%  ((\(rs, es) -> inj (QMethod $2 $3 $4 rs es $6)) `fmap` (requireEnsures $5)) }

returns :: { [Binding'] }
  : {- empty -}                       { [] }
  | "returns" '(' bindings ')'        { $3 }

conds :: { [ Conds ] }
  : many(cond)                        { $1                                   }
                                                                          
cond :: { Conds }
  : "requires" expr                   { Requires $2                          }
  | "ensures" expr                    { Ensures $2                           }
  | "invariant" expr                  { Invariants $2                        }
  | "separates" partition             { Separates $2                         }

                                                                          
bindings
  : manyComma(binding)                { $1 }

binding                                                                   
  : id ':' ty                         { Binding $1 $3                        }
                                                                          
ty :: { Ty }  
  : baseTy                            { $1             }
  | baseTy '->' ty                    { TArrow [$1] $3 }
  | tuple(ty) '->' ty   %shift        { TArrow $1   $3 }

baseTy
  : "nat"                             { TNat              }
  | "int"                             { TInt              }
  | "measured"                        { TMeasured         }
  | "bool"                            { TBool             }
  | "seq" '<' ty '>'                  { TSeq $3           }
  | "qreg" '[' digits ']'             { TQReg (ANat $3)   }
  | "qreg" '[' id ']'                 { TQReg (AVar $3)   }
--  | parens(ty)                        { $1                }
-- so far, don't allow higher order functions
          
qty :: { QTy }
  : "nor"                             { TNor                            }
  | "had"                             { THad                            }
  | "en"                              { TEn                             }
  | "en01"                            { TEn01                           }
                                                                
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
  | id tuple(argExpr) ';'                { SCall $1 $2 }


splitAt :: { Exp' }
  : "split" "at" expr                 { $3 }

guardExpr :: { GuardExp }
  : partition opt(splitAt)            { GEPartition $1 $2 }
                                                                          
partition :: { Partition }
  : manyComma(range)                  { Partition $ $1 }
                                                                          
range                                                                     
  : id '[' expr ".." expr ']'         { Range $1 $3 $5 }
                                                                
spec ::   { Exp' }
  : '{' partition ':'  qty "↦" list(qspec) '}'
                                      { ESpec $2 $4 $6                       }
  | '{' partition ':'  qty "↦" qspec '}'
                                      { ESpec $2 $4 [$6]                     }

nullableId :: { Var }
  : id                                { $1 }
  | {- empty -}                       { "_" }

intv :: { Intv }
  : '[' expr ".." expr ']'            { Intv $2 $4 }

symT : alt("⊗", 'T') { $1 }
symS : alt("Σ", 'S') { $1 }

qspec ::  { SpecExp }
  : symT nullableId '.' pspec
                                      { SESpecHad (SpecHadF $2 $4) }
  | symT nullableId '.' expr
                                      { SESpecNor (SpecNorF $2 $4) }
  | symS id "∈" intv '.' ampExp pspec tuple(expr)
                                      { SESpecEn (SpecEnF $2 $4 $6 $7 $8) }
  | symS id "∈" intv '.'              {- 5  -}
    ampExp pspec                      {- 7  -}
    symT id "∈" intv '.'              {- 12 -}
    tuple(expr)
                                      { SESpecEn01 (SpecEn01F $2 $4 $6 $7 $9 $11 $13) }
  | '_'                               { SEWildcard }




ampExp :: { AmpExp }
  : {- empty -}                            { ADefault         }
  | "isqrt" '(' expr ',' expr ')'          { AISqrt $3 $5     }
  | "sin" '(' expr ')'                     { ASin $3          }
  | "cos" '(' expr ')'                     { ASin $3          }

symo : alt("ω", 'o') { $1 }
symO : alt("Ω", 'O')  { $1 }

-- phase specification
pspec :: { PhaseExp }
  : {- empty -}                            { PhaseWildCard          }
  | '1' '~'                                { PhaseZ                 }
  | symo '(' expr ',' expr ')' '~'         { PhaseOmega $3 $5       }
  | symO id "∈" '[' expr ".." expr ']' '.' '(' expr ',' expr ')' '~'
                                           { PhaseSumOmega (Range $2 $5 $7) $11 $13 }

pbinder :: { PhaseBinder }
  : '_'                                    { PhaseWildCard          }
  | '1'                                    { PhaseZ                 }
  | "ω" '(' id ',' id ')'                  { PhaseOmega $3 $5       }
  | "Ω" id "∈" '[' expr ".." expr ']' '.' '(' id ',' id ')'
                                           { PhaseSumOmega (Range $2 $5 $7) $11 $13 }

mayTuple(p)
  : p                                 { [$1] }
  | tuple(p)                          { $1 }

tuple(p)
  : '(' manyComma(p) ')'              { $2 }

list(p)
  : '[' manyComma(p) ']'              { $2 }


expr                                                                      
  : '_'                               { EWildcard              }
  | spec                              { $1                     }
  | qops                              { $1                     }
  | "measure" partition               { EMeasure $2            }
  | "not" atomic                      { EOp1 ONot $2           }
  | "nor" '(' atomic ',' digits ')'   { EOp2 ONor $3 (ENum $5) }
  | "repr" parens(range)              { ERepr $2               }
  | logicOrExp                        { $1                     }
  | lamExpr                           { $1                     }

argExpr
  : expr                              { $1        }
  | range                             { ERange $1 }


lamExpr :: { Exp' }
  : "λ" lamBinder "=>" pspec tuple(expr) 
    { let (bPhase, bBases) = $2
      in ELambda (LambdaF { bPhase, bBases, ePhase = $4, eBases = $5 })
    }
  | "λ" '(' lamBinder "=>" pspec tuple(expr) ')'
    { let (bPhase, bBases) = $3
      in ELambda (LambdaF { bPhase, bBases, ePhase = $5, eBases = $6 })
    }

lamBinder :: { (PhaseBinder, [Var]) }
  : pbinder '~' tuple(id)             { ($1, $3)               }
  | tuple(id)                         { (PhaseWildCard, $1)    }
  | id                                { (PhaseWildCard, [$1])  }

qops
  : "H"                               { EHad                   }
  | "Qft"                             { EQft False             }
  | "iQft"                            { EQft True              }

logicOrExp :: { Exp' } 
  : logicAndExp "||" logicOrExp       { EOp2 OOr $1 $3         }
  | logicAndExp                       { $1 } 

logicAndExp :: { Exp' } 
  : cmpExpr "&&" logicAndExp          { EOp2 OAnd $1 $3        }
  | cmpExpr                           { $1 }

cmpExpr :: { Exp' }
 : arithExpr many(cmpPartial)         { unchainExps $1 $2  }

cmpPartial
 : cmp arithExpr  { ($1, $2) }

cmp :: { Op2 }
 : '>'                      { OGt }
 | '<'                      { OLt }
 | ">="                     { OGe }
 | "<="                     { OLe }
 | "=="                     { OEq }

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
  | id tuple(expr)                    { EApp $1 $2             }
  | id                                { EVar $1                }
  | '(' expr ')'                      { $2                     }


-- | Combinators
parens(p)
  : '(' p ')'                         { $2 }

braces(p)
  : '{' p '}'                         { $2 }

many(p)                                                                  
  : many_(p)                          { reverse $1 }
                                                                          
many_(p)
  : {- empty -}                       { []      }
  | many_(p) p                        { $2 : $1 }

-- prefer to match the longest comma-sep list
manyComma(p)                                                                  
  : manyComma_(p)        %shift       { reverse $1 }
  | {- empty -}                       { []         }
                                                                          
manyComma_(p)
  : manyComma_(p) ',' p               { $3 : $1 }
  | p                                 { [$1]    }

    
opt(p)
  : {- empty -}                       { Nothing }
  | p                                 { Just $1 }


alt(p, q)
 : p { $1 }
 | q { $1 }


{
scanAndParse :: String -> Parser AST
scanAndParse = runParser <=< L.runScanner
}
