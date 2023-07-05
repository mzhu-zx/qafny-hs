import           Test.Tasty

import           Qafny.Test.AST (astTests, interpTests)

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "Qafny"
  [ astTests
  ]
