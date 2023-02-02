{
module Qafny.Lexer(runScanner, Token (..)) where
}

%wrapper "posn"

@dafny = \#(~\n)*\n

token :-
  $white+          ;
  method           { emit $  TMethod }
  @dafny           { pushToken $ TDafny . takeWhile (/= '\n') . tail }
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

/* pushToken f =  token (\(_, _, _, s) _ -> [f s]) */


/* runScanner :: String -> Either String [Token] */
/* runScanner s = runAlex s $ */
/*   do let loop toks = do t <- alexMonadScan */
/*                         if t == [] */
/*                         then return toks */
/*                         else loop (t ++ toks) */
/*      loop [] */

/* alexEOF = pure []  */

}
