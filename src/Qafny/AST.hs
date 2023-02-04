{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, FlexibleContexts #-}

module Qafny.AST where

import           Data.Text.Lazy(Text)
import qualified Data.Text.Lazy.Builder as TB
-- import           GHC.List(foldl')

data Ty = TNat
        | TInt
        | TBool
        | TSeq Ty
        | TQ QTy
        | TMethod Var [Ty] [Ty] -- parameter and return types
        deriving (Show, Eq)

data QTy = TNor
         | THad
         | TCH
         deriving (Show, Eq)

type Var = String

data Binding = Binding Var Ty
             deriving (Show, Eq)

type Bindings = [Binding]

data Op2 = OAnd
         | OOr
         deriving (Show, Eq)

data Op1 = ONot
         deriving (Show, Eq)

data Exp = ENum Int
         | EBool Bool
         | EOp1 Op1 Exp
         | EOp2 Op2 Exp Exp
         | EForall Binding (Maybe Exp) Exp
         | EDafny String
         deriving (Show, Eq)

type Returns = [Binding]

data Conds = Requires Exp
           | Ensures Exp

type Requires = [Exp]
type Ensures = [Exp]
type Body = [Stmt]

data Toplevel = QMethod Var Bindings Returns Requires Ensures Body
              | QDafny String
              deriving (Show, Eq)
              -- | QFunction Var Bindings Ty

data Stmt = SAssert Exp
          | SCall Exp [Exp]
          | SVar Binding (Maybe Exp)
          | SAssign Var
          deriving (Show, Eq)

type AST = [Toplevel]

line :: TB.Builder
line = TB.singleton '\n'

space :: TB.Builder
space = TB.singleton ' '


class DafnyPrinter a where
  build :: a -> TB.Builder

instance DafnyPrinter Char where
  build = TB.singleton
  
instance DafnyPrinter String where
  build = TB.fromString

instance DafnyPrinter AST where
  build = foldr (\x xs -> build x <> line <> xs) line

instance DafnyPrinter Ty where
  build TNat = build "nat"
  build _    = undefined 

instance DafnyPrinter Binding where
  build (Binding x t) = build x <> build " : " <> build t

instance DafnyPrinter Bindings where
  build [] = build ""
  build (x:xs) = foldl (\ys y -> ys  <> build ", " <> build y) (build x) xs

instance DafnyPrinter Toplevel where
  build (QDafny s) = build s 
  build (QMethod idt bds rets reqs ens block) =
    build "method" <> space <>
    build idt <> space <>
    build '(' <> build bds <> build ')' <>
    buildRets rets
    where buildRets [] = build ""
          buildRets r  = build " returns " <>
                         build '(' <> build r <> build ')'

instance DafnyPrinter Exp where
  build = undefined

buildRequires :: Requires -> TB.Builder
buildRequires = foldr (\x xs -> build "requires" <> build x <> build '\n' <> xs) (build "")

texify :: DafnyPrinter a => a -> Text
texify = TB.toLazyText . build
