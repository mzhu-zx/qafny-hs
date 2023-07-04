{-# LANGUAGE DeriveFunctor #-}

module Qafny.AST where

import           Control.Monad (guard)
import           Text.Printf   (printf)

data AExp
  = ANat Int
  | AVar Var
  deriving (Show, Eq, Ord)

data Ty
  = TNat
  | TInt
  | TBool
  | TSeq Ty
  | TQReg AExp
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
  | TEN
  | TEN01
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
  | OSub
  | OMul
  | OMod
  | ONor
  | OLt
  | OLe
  | OGt
  | OGe
  | OEq
  deriving (Show, Eq, Ord)

data Op1
  = ONot
  deriving (Show, Eq, Ord)

-- the exp is not reversible
data Exp
  = ENum Int
  | EVar Var
  | EWildcard
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
  | EPartition Partition
  | ESpec Partition QTy Exp
  | EQSpec Var Intv [Exp]
  | EQSpec01 Var Intv Var Intv [Exp] 
  -- ?
  | RInd Var Exp -- boolean at var[exp], var must be Q type
  | REq Exp Exp Var Exp -- compare exp == exp and store the value in var[exp], var must be Q type
  | RLt Exp Exp Var Exp -- compare exp < exp and store the value in var[exp], var must be Q type
  deriving (Show, Eq, Ord)


showExp :: Exp -> String
showExp (ENum n) = show n
showExp (EVar v) = v
showExp (EOp2 op e1 e2) = showExp e1 ++ sop ++ showExp e2
  where
    sop =
      case op of
        OAdd -> " + "
        OSub -> " - "
        OMul -> " * "
        _    -> undefined
showExp e = show e

-- | EmitExp : Unsafe Expressions for Codegen Only
data EmitExp
  = ELambda Var Exp
  | EMtSeq
  | EMakeSeq Ty Exp EmitExp
  | ECard Exp
  | ECall Var [Exp]
  | ESelect Exp Exp
  | ESeqRange Exp Exp Exp
  | EDafnyVar Var
  | EOpChained Exp [(Op2, Exp)]
  deriving  (Show, Eq, Ord)

type Returns = [Binding]

data Conds
  = Requires Exp
  | Ensures Exp
  | Invariants Exp
  | Separates Partition
  deriving Show

type Requires = [Exp]
type Ensures = [Exp]
type Invariants = [Exp]
type Separates = Partition

newtype Block = Block { inBlock :: [Stmt] }
  deriving (Show, Eq)

data Toplevel
  = QMethod Var Bindings Returns Requires Ensures (Maybe Block)
  | QDafny String
  deriving (Show, Eq)

data Intv = Intv Exp Exp
  deriving (Eq, Show, Ord)

data Range = Range Var Exp Exp
  deriving (Eq, Ord)

instance Show Range where
  show (Range x y z) = printf "%s[%s .. %s]" x (showExp y) (showExp z)

newtype Loc = Loc { deref :: Var }
  deriving (Eq, Ord)

instance Show Loc where
  show = deref

newtype Partition = Partition { unpackPart :: [Range] }
  deriving (Eq, Ord)


instance Show Partition where
  show = showPP . unpackPart
    where
      showPP [] = "∅"
      showPP (r : rs) = foldr (\r' s -> show r' ++ " ⊎ " ++ s) (show r) rs

data Stmt
  = SAssert Exp
  | SCall Exp [Exp]
  | SVar Binding (Maybe Exp)
  | SAssign Var Exp
  | SApply Partition Exp
  | SDafny String
  | SIf Exp Separates Block
  --     id left right guard invarants separates Body
  | SFor Var Exp Exp   Exp   [Exp]     Partition   Block
  | SEmit EmitStmt
  deriving (Show, Eq)

data EmitStmt
  = SIfDafny Exp Block
  | SBlock Block
  | SForEmit Var Exp Exp [Exp] Block
  deriving (Show, Eq)

type AST = [Toplevel]

--------------------------------------------------------------------------------
-- | AST Constants
-------------------------------------------------------------------------------
wild :: Var
wild =  "_"

constExp :: Exp -> EmitExp
constExp = ELambda wild


typeTag :: Ty -> String
typeTag TNat     = "nat"
typeTag TInt     = "int"
typeTag TBool    = "bool"
typeTag (TSeq t) = "_seqL_" ++ typeTag t ++ "_R_"
typeTag _        = "unsupported"

qComment :: String -> Stmt
qComment = SDafny . ("// " ++)

--------------------------------------------------------------------------------
-- * Partition Utils
--------------------------------------------------------------------------------

range1 :: Var -> Range
range1 v = Range v (ENum 0) (ENum 1)


partition1 :: Range -> Partition
partition1 =  Partition . (: [])


-- | Extract all variables for each range in a partition
varFromPartition :: Partition -> [Var]
varFromPartition (Partition s) = [ x | (Range x _ _) <- s ]


-- | Compute all free partitions/ranges mentioned in the LHS of application
leftPartitions :: [Stmt] -> [Partition]
leftPartitions =
  concatMap perStmt
  where
    perStmt (SApply s _) = [s]
    -- TODO: query If and For recursively
    perStmt _            = []


(.:) :: (c -> d) -> (a -> b -> c) -> a -> b -> d
(.:) g f2 x y = g (f2 x y)


--------------------------------------------------------------------------------
-- * Exp Utils
--------------------------------------------------------------------------------
fVars :: Exp -> [Var]
fVars (ENum _)       = []
fVars (EVar x)       = [x]
fVars (EOp1 _ e)     = fVars e
fVars (EOp2 _ e1 e2) = fVars e1 ++ fVars e2
