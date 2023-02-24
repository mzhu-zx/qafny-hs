module Qafny.ParserUtils where
import           Qafny.AST
import qualified Qafny.Lexer as L

type Parser a = Either String a

withParse :: String -> String
withParse = ("Parser Error: " ++)

separatesOnly :: Conds -> Parser Session
separatesOnly (Separates s) = return s
separatesOnly c             =
  Left $ withParse $ show c ++ "is not a `separates` specification"

parseError :: [L.Token] -> Parser a
parseError [] = Left $ withParse "Expect more tokens"
parseError xs = Left $ withParse (show xs)
