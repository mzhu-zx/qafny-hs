{
module Qafny.Lexer(runScanner, Token (..)) where
}

%wrapper "monad"
@dafny = \#(~\n)*\n

token :-
  $white+          ;
  @dafny           { pushToken $ TDafny . drop 1 }
{

data Token = TDafny String
           | TRequire
           | TEnsures
           | TMethod
           | TAssert
           | TForall
           | TBar
           | TEOF
           deriving (Show, Eq)


pushToken f =  token (\(_, _, _, s) _ -> [f s])

runScanner :: String -> Either String [Token]
runScanner s = runAlex s $
  do let loop toks = do t <- alexMonadScan
                        if t == []
                        then return toks
                        else loop (t ++ toks)
     loop []

alexEOF = pure [] 

}
