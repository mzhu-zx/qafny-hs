module Qafny.AST where

data Ty
  = TNat
  | TInt
  | TBool
  | TSeq Ty
  | TQ QTy
  | TMethod [Ty] [Ty] -- parameter and return types
  | TEmit EmitTy
  deriving (Show, Eq, Ord)

-- | EmitExp : Unchecked Types for Codegen Only
data EmitTy
  = TAny String
  deriving (Show, Eq, Ord)

data QTy
  = TNor
  | THad
  | TCH
  deriving (Show, Eq, Ord)

type Var = String
  
data Binding
  = Binding Var Ty
  deriving (Show, Eq, Ord)

type Bindings = [Binding]

data Op2
  = OAnd
  | OOr
  | OAdd
  | OMul
  | OMod
  | ONor
  deriving (Show, Eq, Ord)

data Op1
  = ONot
  deriving (Show, Eq, Ord)

data Exp
  = ENum Int
  | EVar Var
  | EHad
  | EQFT
  | ERQFT
  | EMea Var
  | EBool Bool
  | ECl Var Exp
  | EApp Var Exp
  | EOp1 Op1 Exp
  | EOp2 Op2 Exp Exp
  | EForall Binding (Maybe Exp) Exp
  | EDafny String
  | EEmit EmitExp
  | ESession Session
  deriving (Show, Eq, Ord)

wild :: Var
wild =  "_"

-- | EmitExp : Unsafe Expressions for Codegen Only
data EmitExp
  = ELambda Var Exp
  | EMakeSeq Ty Exp EmitExp
  | ECall Var [Exp]
  | EDafnyVar Var 
  deriving  (Show, Eq, Ord)

type Returns = [Binding]

data Conds
  = Requires Exp
  | Ensures Exp
  | Invariants Exp
  | Separates Exp
  deriving Show

type Requires = [Exp]
type Ensures = [Exp]
type Invariants = [Exp]
type Separates = Exp

newtype Block = Block { inBlock :: [Stmt] }
  deriving (Show, Eq)

data Toplevel
  = QMethod Var Bindings Returns Requires Ensures Block
  | QDafny String
  deriving (Show, Eq)

data Range = Ran Var Exp Exp 
           deriving (Show, Eq, Ord)

newtype Session = Session [Range]
  deriving (Show, Eq, Ord)

data Stmt
  = SAssert Exp
  | SCall Exp [Exp]
  | SVar Binding (Maybe Exp)
  | SAssign Var Exp
  | SApply Session Exp
  | SDafny String
  | SIf Exp Separates Block
  --     id left right guard invarants separates Body
  | SFor Var Exp Exp   Exp   [Exp]     Exp       Block
  | SEmit EmitStmt
  deriving (Show, Eq)

data EmitStmt
  = SIfDafny Exp Block 
  deriving (Show, Eq)

type AST = [Toplevel]

typeTag :: Ty -> String
typeTag TNat     = "nat"
typeTag TInt     = "int"
typeTag TBool    = "bool"
typeTag (TSeq t) = "seq__" ++ typeTag t ++ "__"
typeTag _        = "unsupported"

--------------------------------------------------------------------------------
-- | Session Utils
--------------------------------------------------------------------------------

range1 :: Var -> Range
range1 v = Ran v (ENum 0) (ENum 1)

session1 :: Range -> Session
session1 =  Session . (: [])

varFromSession :: Session -> [Var]
varFromSession (Session s) = map (\(Ran x _ _) -> x) s
