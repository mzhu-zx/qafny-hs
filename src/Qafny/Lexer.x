{
module Qafny.Lexer(runScanner, Token (..)) where
}

%wrapper "posn"

$alpha = [a-zA-Z]
$digit = 0-9

@dafny = \#(~\n)*
@id = ($alpha) ($alpha | $digit | \_ | \')*
@assign = (:=)
@qassign = (\*=)
@aand = (&&)
@aor = (\|\|)
@adot = (..)
@eq = (==)

token :-
  $white+          ;
  @dafny           { pushToken $ TDafny . tail }
  method           { emit $  TMethod }
  ensures          { emit $  TEnsures }
  requires         { emit $  TRequires }
  returns          { emit $  TReturns }
  assert           { emit $  TAssert }
  nat              { emit $  TNat  }
  int              { emit $  TInt  }
  bool             { emit $  TBool }
  seq              { emit $  TSeq  }
  nor              { emit $  TNor  }
  not              { emit $  TNot  }
  had              { emit $  THad  }
  ch               { emit $  TCH   }
  var              { emit $  TVar   }
  if               { emit $  TIf   }
  H              { emit $  THApp  }
  QFT              { emit $  TQFT  }
  RQFT              { emit $  TRQFT  }
  meas              { emit $  TMea  }
  @id              { pushToken $ TId }
  $digit           { pushToken $ TLitInt . read }
  @assign          { emit $  TAssign }
  @qassign          { emit $  TApply }
  @eq              { emit $  TEq }
  \*               { emit $ TMul }
  \+               { emit $ TAdd }
  \%               { emit $ TMod }
  \[               { emit $ TLBracket   }
  \]               { emit $ TRBracket    }
  @aand             { emit $ TAnd }
  @aor              { emit $ TOr }
  @adot              { emit $ TDot }
  \|               { emit $  TBar }
  \(               { emit $  TLPar }
  \)               { emit $  TRPar }
  \{               { emit $  TLBrace }
  \}               { emit $  TRBrace }
  \<               { emit $  TLAng      }
  \>               { emit $  TRAng      }
  \,               { emit $  TComma }
  \:               { emit $  TColon }
  \;               { emit $  TSemi }
{

data Token = TDafny String
           | TLitInt Int
           | TRequires
           | TEnsures
           | TMethod
           | TAssert
           | TLPar
           | TRPar
           | TLAng
           | TRAng
           | TLBrace
           | TRBrace
           | TLBracket
           | TRBracket
           | TForall
           | TBar
           | TEOF
           | TReturns
           | TNat
           | TInt
           | TBool
           | TSeq
           | TNor
           | THad
           | TCH
           | TId String
           | TComma
           | TColon
           | TAssign
           | TApply
           | TEq
           | TSemi
           | TVar
           | TIf
           | TMul
           | TAdd
           | TMod
           | TAnd
           | TOr
           | TNot
           | TDot
           | THApp
           | TQFT
           | TRQFT
           | TMea
           deriving (Show, Eq)

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
runScanner :: String -> Either String [Token]
runScanner = return . alexScanTokens

pushToken f p = f
emit t p s = t 

}
