module Qafny.Test.AST where

import           Qafny.Partial    (evalP, PEval (evalP))
import           Qafny.AST
import qualified Data.Map.Strict  as Map
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
    (Map.empty, -2) @=?
     evalP (substE [("y", e1), ("x", e2)] exp1)
  , testCase "Interpret (1 - x)" $
    (Map.fromList [("x", -1)], 1) @=?
    evalP exp2
  , testCase "Interpret (x - 1)" $
    (Map.fromList [("x", 1)], -1) @=?
    evalP exp3
  , testCase "interpExp ((1 - y) - x)" $
    (Map.fromList [("y", -1), ("x", -1)], 1) @=?
    evalP exp1
  , testCase "evalP (x - (1 - y))" $
    (Map.fromList [("x", 1), ("y", 1)], -1) @=?
    evalP exp4
  , testCase "evalP (x - (y - 1))" $
    (Map.fromList [("x", 1), ("y", -1)], 1) @=?
    evalP exp5
  ]
  where e1 = ENum 1
        e2 = ENum 2
        exp1 = EOp2 OSub (EOp2 OSub (ENum 1) (EVar "y")) (EVar "x")
        exp2 = EOp2 OSub (ENum 1) (EVar "x")
        exp3 = EOp2 OSub (EVar "x") (ENum 1)
        exp4 = EOp2 OSub (EVar "x") (EOp2 OSub (ENum 1) (EVar "y"))
        exp5 = EOp2 OSub (EVar "x") (EOp2 OSub (EVar "y") (ENum 1))

