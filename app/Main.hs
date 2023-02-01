module Main (main) where

import Qafny.Parser


main :: IO ()
main = do s <- readFile "/home/mzhu/qafny-hs/test/Resource/DeutschJozsa.dfy"
          print $ parse s
