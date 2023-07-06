module Qafny.ParserUtils where
import           Qafny.AST
import qualified Qafny.Lexer as L
import           Text.Printf (printf)

type Parser a = Either String a

withParse :: String -> String
withParse = ("Parser Error: " ++)

separatesOnly :: Conds -> Parser Partition
separatesOnly (Separates s) = return s
separatesOnly c             =
  Left $ withParse $ show c ++ "is not a `separates` specification"

parseError :: [L.SToken] -> Parser a
parseError [] = Left $ withParse "Expect more tokens"
parseError ((L.SrcLoc {L.sLine=sLine, L.sColumn=sColumn}, tok) : xs) = Left . withParse $
  printf "at line %s, col %s, token %s\nRest tokens: %s"
    (show sLine) (show sColumn) (show tok) (show (snd <$> xs))

requireEnsures :: [Conds] -> Parser (Requires, Ensures)
requireEnsures =
  foldr inner (return ([], [])) 
  where
    inner cond mrqens = do
      (rqs, ens) <- mrqens
      case cond of
        Ensures e  -> return (rqs, e : ens)
        Requires r -> return (r : rqs, ens)
        _          -> Left . err $ show cond
    err = printf "%s is not one of `requires` or `ensures`"

invariantSeperates :: [Conds] -> Parser (Invariants, Separates)
invariantSeperates conds = do
  (invs, seps) <- foldr inner (return ([], [])) conds
  case seps of
    [sep] -> return (invs, sep)
    _     -> Left . errSep $ show seps
  where
    inner cond mrqens = do
      (ins, ses) <- mrqens
      case cond of
        Invariants i  -> return (i : ins, ses)
        Separates  s  -> return (ins, s : ses)
        _             -> Left $ err (show cond)
    err = printf "%s is not one of `invariant` or `separates`"
    errSep = printf "There should be exactly one `separates` condition, given %s."

