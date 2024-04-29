module Qafny.Test.Parser where

import           Qafny.Syntax.AST
import           Qafny.Syntax.ParserUtils (unchainExps)
import           Test.Tasty
import           Test.Tasty.HUnit

parserTests :: TestTree
parserTests = testGroup "Parser Related Tests"
  [ unchainTests
  ]


unchainTests :: TestTree
unchainTests = testGroup "unchainExps Tests"
  [ testCase "x" $
    EVar "x" @=?
    unchainExps (EVar "x") []
  , testCase "x < y" $
    e1 @=?
    unchainExps (EVar "x") [(OLt, EVar "y")]
  , testCase "x < y <= z" $
    eA12 @=?
    unchainExps (EVar "x") [(OLt, EVar "y"), (OLe, EVar "z")]
  , testCase "1 <= x < y <= z" $
    eA012 @=?
    unchainExps (ENum 1) [(OLe, EVar "x"), (OLt, EVar "y"), (OLe, EVar "z")]
  ]
  where e1 = EOp2 OLt (EVar "x") (EVar "y")
        e2 = EOp2 OLe (EVar "y") (EVar "z")
        e0 = EOp2 OLe (ENum 1) (EVar "x")
        eA12 = EOp2 OAnd e1 e2
        eA012 = EOp2 OAnd e0 (EOp2 OAnd e1 e2)
