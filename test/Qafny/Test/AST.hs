module Qafny.Test.AST where

import           Qafny.AInterp    (interpExp, interpExpEnv)
import           Qafny.AST
import           Test.Tasty
import           Test.Tasty.HUnit

astTests :: TestTree
astTests = testGroup "AST Related Tests"
  [ substTest
  , interpTests
  ]

substTest :: TestTree
substTest = testGroup "Subtitution Tests"
  [ testCase "(1 + x) [ 2 / x ]" $
    EOp2 OAdd (ENum 1) (ENum 2) @=?
    substE [("x", ENum 2)] (EOp2 OAdd (ENum 1) (EVar "x"))
  ]

interpTests :: TestTree
interpTests = testGroup "AInterp Tests"
  [ testCase "Interpret ((1 - 1) - 2)" $
    ([], -2) @=?
    interpExpEnv [("y", e1), ("x", e2)] exp1
  , testCase "Interpret (1 - x)" $
    ([(OSub, "x")], 1) @=?
    interpExp exp2
  , testCase "Interpret (x - 1)" $
    ([(OAdd, "x")], -1) @=?
    interpExp exp3
  , testCase "interpExp ((1 - y) - x)" $
    ([(OSub, "y"), (OSub, "x")], 1) @=?
    interpExp exp1
  , testCase "interpExp (x - (1 - y))" $
    ([(OAdd, "x"), (OAdd, "y")], -1) @=?
    interpExp exp4
  , testCase "interpExp (x - (y - 1))" $
    ([(OAdd, "x"), (OSub, "y")], 1) @=?
    interpExp exp5
  ]
  where e1 = ENum 1
        e2 = ENum 2
        exp1 = EOp2 OSub (EOp2 OSub (ENum 1) (EVar "y")) (EVar "x")
        exp2 = EOp2 OSub (ENum 1) (EVar "x")
        exp3 = EOp2 OSub (EVar "x") (ENum 1)
        exp4 = EOp2 OSub (EVar "x") (EOp2 OSub (ENum 1) (EVar "y"))
        exp5 = EOp2 OSub (EVar "x") (EOp2 OSub (EVar "y") (ENum 1))

