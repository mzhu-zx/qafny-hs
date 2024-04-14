{
module Qafny.Syntax.Lexer(
  runScanner,
  module Qafny.Syntax.Token
) where

import Qafny.Syntax.Token
}

%wrapper "posn"

$alpha = [a-zA-Z]
$digit = 0-9

@digits = ($digit)+
@dafny = \#(~\n)*
@comment = (\/\/)(~\n)*
@id = ($alpha) ($alpha | $digit | \_ | \')*
@wname=(\_)($alpha|$digit)*
@assign = (:=)
@qassign = (\*=)
@aand = (&&)
@aor = (\|\|)
@adots = (\.\.)
@adot = (\.)
@age = (>=)
@ale = (\<\=)
@eq = (==)
@arrow = (=>)

token :-
  $white+          ;
  @comment         ;
  @wname           { pushToken $ TWildcardName . tail }
  @dafny           { pushToken $ TDafny . tail        }
  method           { emit $  TMethod             }
  ensures          { emit $  TEnsures            }
  separates        { emit $  TSeparates          }
  requires         { emit $  TRequires           }
  returns          { emit $  TReturns            }
  assert           { emit $  TAssert             }
  nat              { emit $  TNat                }
  int              { emit $  TInt                }
  bool             { emit $  TBool               }
  seq              { emit $  TSeq                }
  nor              { emit $  TNor                }
  not              { emit $  TNot                }
  had              { emit $  THad                }
  en               { emit $  TEn                 }
  en01             { emit $  TEn01               }
  qreg             { emit $  TQReg               }
  var              { emit $  TVar                }
  if               { emit $  TIf                 }
  split            { emit $  TSplit              }
  at               { emit $  TAt                 }
  cl               { emit $  TCl                 }
  "λ"              { emit $  TCl                 }
  "\lambda"        { emit $  TCl                 }
  for              { emit $  TFor                }
  in               { emit $  TIn                 }
  "∈"              { emit $  TUnicodeIn          }
  "\in"            { emit $  TUnicodeIn          }
  "Σ"              { emit $  TUnicodeSum         }
  "∑"              { emit $  TUnicodeSum         }
  "ω"              { emit $  TUnicodeOmega       }
  "\omega"         { emit $  TUnicodeOmega       }
  "Ω"              { emit $  TUnicodeSumOmega    }
  "\Omega"         { emit $  TUnicodeSumOmega    }
  "\Sum"           { emit $  TUnicodeSum         }
  "⊗"              { emit $  TUnicodeTensor      }
  "\otimes"        { emit $  TUnicodeIn          }
  "|->"            { emit $  TTyArrow            }
  "↦"              { emit $  TUnicodeMap         }
  "\mapsto"        { emit $  TUnicodeMap         }
  "->"             { emit $  TTyArrow            }
  repr             { emit $  TRepr               }
  with             { emit $  TWith               }
  measured         { emit $  TMeasured           }
  invariant        { emit $  TInv                }
  isqrt            { emit $  TISqrt              }
  sin              { emit $  TSin                }
  cos              { emit $  TCos                }  
  H                { emit $  THApp               }
  QFT              { emit $  TQFT                }
  RQFT             { emit $  TRQFT               }
  measure          { emit $  TMeasure           }
  @id              { pushToken $ TId             }
  @digits          { pushToken $ TLitInt . read  }
  @assign          { emit $  TAssign             }
  @qassign         { emit $  TApply              }
  @eq              { emit $  TEq                 }
  @arrow           { emit $  TArrow              }
  @age             { emit $  TGe                 }
  @ale             { emit $  TLe                 }
  \~               { emit $  TTilde              }
  \*               { emit $  TMul                }
  \+               { emit $  TAdd                }
  \-               { emit $  TSub                }
  \%               { emit $  TMod                }
  \[               { emit $  TLBracket           }
  \]               { emit $  TRBracket           }
  @aand            { emit $  TAnd                }
  @aor             { emit $  TOr                 }
  @adots           { emit $  TDots               }
  @adot            { emit $  TDot                }
  \|               { emit $  TBar                }
  \(               { emit $  TLPar               }
  \)               { emit $  TRPar               }
  \{               { emit $  TLBrace             }
  \}               { emit $  TRBrace             }
  \<               { emit $  TLAng               }
  \>               { emit $  TRAng               }
  \,               { emit $  TComma              }
  \:               { emit $  TColon              }
  \;               { emit $  TSemi               }
{
-- alexScanTokens str = go (alexStartPos, '\n', [], str)
--   where
--     go inp@(pos, _, _, str) =
--       case alexScan inp 0 of
--         AlexEOF                -> []
--         AlexSkip  inp' len     -> go inp'
--         AlexToken inp' len act -> act pos (take len str) : go inp'
--         AlexError (AlexPn _ line column, _, _, _) -> error $ unwords
--           [ "lexical error at", show line, "line,", show column, "column" ]
-- 
runScanner :: String -> Either String [SToken]
runScanner = return . alexScanTokens

srclocFromPosn :: AlexPosn -> SrcLoc
srclocFromPosn (AlexPn _ l c) = SrcLoc {sLine = l, sColumn = c}

pushToken f p s = (srclocFromPosn p, f s)
emit t p _ = (srclocFromPosn p, t)

}
