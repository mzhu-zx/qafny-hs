module Qafny.AST where

data Ty = TNat
        | TInt
        | TBool
        | TSeq Ty
        | TQ QTy
        | TMethod [Ty] [Ty] -- parameter and return types
        deriving (Show, Eq, Ord)

data QTy = TNor
         | THad
         | TCH
         deriving (Show, Eq, Ord)

type Var = String

data Binding = Binding Var Ty
             deriving (Show, Eq, Ord)

type Bindings = [Binding]

data Op2 = OAnd
         | OOr
         | OAdd
         | OMul
         | OMod
         | ONor
         deriving (Show, Eq, Ord)

data Op1 = ONot
         deriving (Show, Eq, Ord)

data Exp = ENum Int
         | EVar Var
         | EHad
         | EQFT
         | ERQFT
         | EMea Var
         | EBool Bool
         | EApp Var Exp
         | EOp1 Op1 Exp
         | EOp2 Op2 Exp Exp
         | EForall Binding (Maybe Exp) Exp
         | EDafny String
         | EEmit EmitExp
         deriving (Show, Eq, Ord)

wild :: Var
wild =  "_"

-- EmitExp : Unsafe Expressions for Codegen Only
data EmitExp = ELambda Var Exp
             | EMakeSeq Ty Exp EmitExp
             deriving  (Show, Eq, Ord)

type Returns = [Binding]

data Conds = Requires Exp
           | Ensures Exp

type Requires = [Exp]
type Ensures = [Exp]

newtype Block = Block { inBlock :: [Stmt] }
  deriving (Show, Eq)

data Toplevel = QMethod Var Bindings Returns Requires Ensures Block
              | QDafny String
              deriving (Show, Eq)

data Range = Ran Var Exp Exp 
        deriving (Show, Eq, Ord)

newtype Session = Session [Range]
  deriving (Show, Eq, Ord)

data Stmt = SAssert Exp
          | SCall Exp [Exp]
          | SVar Binding (Maybe Exp)
          | SAssign Var Exp
          | SApply Session Exp
          | SDafny String
          | SIf Exp Block
          deriving (Show, Eq)

type AST = [Toplevel]

typeTag :: Ty -> String
typeTag TNat     = "nat"
typeTag TInt     = "int"
typeTag TBool    = "bool"
typeTag (TSeq t) = "seq__" ++ typeTag t ++ "__"
typeTag _        = "unsupported"
