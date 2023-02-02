{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}

module Qafny.AST where
import Data.Text (Text, intersperse, pack, intercalate, singleton)

data Ty = TNat
        | TInt
        | TBool
        | TSeq Ty
        | TNor
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
type Requires = [Exp]
type Ensures = [Exp]

data Toplevel = QMethod Var Bindings Returns Requires Ensures [Stmt]
              | QDafny String
              deriving (Show, Eq)
              -- | QFunction Var Bindings Ty

data Stmt = SAssert Exp
          | SCall Exp [Exp]
          | SVar Binding (Maybe Exp)
          | SAssign Var
          deriving (Show, Eq)

type AST = [Toplevel]

class DafnyPrinter a where
  texify :: a -> Text

instance DafnyPrinter AST where
  texify = intercalate (singleton '\n') . map texify

 
instance DafnyPrinter Toplevel where
  texify (QDafny s) = pack s
  texify _          = undefined
