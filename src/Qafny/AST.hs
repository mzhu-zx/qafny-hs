module Qafny.AST where

data Ty = TNat
        | TInt
        | TBool
        | TSeq Ty
        | TNor
        | THad
        | TCH
        deriving (Show, Eq)

type Var = String

data Binding = Binding (Var, Ty)
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
         deriving (Show, Eq)

type Returns = [Binding]
type Requires = [Exp]
type Ensures = [Exp]

data Toplevel = QMethod Var Bindings Returns Requires Ensures [Stmt]
              deriving (Show, Eq)
              -- | QFunction Var Bindings Ty

data Stmt = QAssert Exp
          | QCall Exp [Exp]
          | QVar Binding (Maybe Exp)
          | QAssign Var
          deriving (Show, Eq)

newtype QDafny = QDafny { toDafny :: String }
  
type AST = [Toplevel]
