import           Test.Tasty

import           Qafny.Test.AST (astTests, interpTests)
import           Qafny.Test.Parser (parserTests)

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Qafny"
  [ astTests
  , parserTests
  ]
