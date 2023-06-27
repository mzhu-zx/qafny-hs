module Qafny.ParserUtils where
import           Qafny.AST
import qualified Qafny.Lexer as L
import           Qafny.SrcLoc
import           Text.Printf (printf)

type Parser a = Either String a

withParse :: String -> String
withParse = ("Parser Error: " ++)

-- separatesOnly :: Conds -> Parser Partition
-- separatesOnly (Separates s) = return s
-- separatesOnly c             =
--   Left $ withParse $ show c ++ "is not a `separates` specification"

parseError :: [L.SToken] -> Parser a
parseError [] = Left $ withParse "Expect more tokens"
parseError ((SrcLoc {sLine=sLine, sColumn=sColumn}, tok) : xs) = Left . withParse $
  printf "at line %s, col %s, token %s\nRest tokens: %s"
    (show sLine) (show sColumn) (show tok) (show (snd <$> xs))

--------------------------------------------------------------------------------
-- | SrcLoc Structure
--------------------------------------------------------------------------------
