{-# LANGUAGE DeriveFunctor, RankNTypes, UndecidableInstances #-}

module Qafny.AST where

import           Text.Printf              (printf)

newtype Mu f = Mu { unroll :: f (Mu f) }

(.$) :: (f (Mu f) -> c) -> Mu f -> c
(.$) = (. unroll)

($.) :: (a -> f (Mu f)) -> a -> Mu f
($.) = (Mu .)


instance Show (f (Mu f)) => Show (Mu f) where
  show = show . unroll

instance Ord (f (Mu f)) => Ord (Mu f) where
  compare a b = compare (unroll a) (unroll b)

instance Eq (f (Mu f)) =>  Eq (Mu f) where
  a == b = unroll a == unroll b

data TyF m
  = TNat
  | TInt
  | TBool
  | TSeq m
  | TQReg Int
  | TMethod [m] [m] -- parameter and return types
  | TEmit EmitTy
  deriving (Show, Eq, Ord, Functor)

type Ty = Mu TyF

-- | EmitExp : Unchecked Types for Codegen Only
data EmitTy
  = TAny String
  deriving (Show, Eq, Ord)

data QTy
  = TNor
  | THad
  | TCH
  | TCH01
  deriving (Show, Eq, Ord)

type Var = String

data BindingF m
  = Binding Var (TyF m)
  deriving (Show, Eq, Ord, Functor)

type Binding = Mu BindingF

type BindingsF f = [BindingF f]

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
data ExpF m
  = ENum Int
  | EVar Var
  | EWildcard
  | EHad
  | EQFT
  | ERQFT
  | EMea Var
  | EBool Bool
  | EApp Var m
  | EOp1 Op1 m
  | EOp2 Op2 m m
  | EForall Binding (Maybe m) m
  | EDafny String
  | EEmit EmitExp
  | EPartition Partition
  | ESpec Partition QTy m
  | EQSpec Var Intv [m]
  | EQSpec01 Var Intv Var Intv [m]
  deriving (Show, Eq, Ord, Functor)

type Exp = Mu ExpF

-- | EmitExp : Unsafe Expressions for Codegen Only
data EmitExp
  = ELambda Var Exp
  | EMtSeq
  | EMakeSeq Ty Exp EmitExp
  | ECard Exp
  | ECall Var [Exp]
  | ESelect Exp Exp
  | EDafnyVar Var
  | EOpChained Exp [(Op2, Exp)]
  deriving  (Show, Eq, Ord)

type ReturnsF m = [BindingF m]

data CondsF m
  = Requires (ExpF m)
  | Ensures (ExpF m)
  | Invariants (ExpF m)
  | Separates Partition
  deriving (Eq, Ord, Show, Functor)

type RequiresF m = [ExpF m]
type EnsuresF m = [ExpF m]
type InvariantsF m = [ExpF m]
type Separates = Partition

newtype BlockF m = BlockF { inBlock :: [StmtF m] }
  deriving (Show, Eq, Functor)

type Block = Mu BlockF

data ToplevelF m
  = QMethod Var (BindingsF m) (ReturnsF m) (RequiresF m) (EnsuresF m) (Maybe (BlockF m))
  | QDafny String
  deriving (Show, Eq, Functor)

data Intv = Intv Exp Exp
  deriving (Eq, Show, Ord)

data Range = Range Var Exp Exp
  deriving (Eq, Ord)

instance Show Range where
  show (Range x y z) = printf "%s[%s .. %s]" x (show y) (show z)

newtype Loc = Loc { deref :: Var }
  deriving (Eq, Ord)

instance Show Loc where
  show = deref

newtype Partition = Partition { unpackPartition :: [Range] }
  deriving (Eq, Ord)

instance Show Partition where
  show = show . unpackPartition

data StmtF m
  = SAssert (ExpF m)
  | SCall (ExpF m) [ExpF m]
  | SVar Binding (Maybe (ExpF m))
  | SAssign Var (ExpF m)
  | SApply Partition (ExpF m)
  | SDafny String
  | SIf (ExpF m) Separates Block
  --     id  left     right    guard    invarants separates Body
  | SFor Var (ExpF m) (ExpF m) (ExpF m) [ExpF m]  Partition Block
  | SEmit EmitStmt
  deriving (Show, Eq, Functor)

type Stmt = Mu StmtF

data EmitStmt
  = SIfDafny Exp Block
  | SBlock Block
  | SForEmit Var Exp Exp [Exp] Block
  deriving (Show, Eq)

newtype ASTF m = ASTF [ToplevelF m]
  deriving (Show, Eq, Functor)

type AST = Mu ASTF

--------------------------------------------------------------------------------
-- | Recursion Schemes
--------------------------------------------------------------------------------
-- makeBaseFunctor ''Toplevel
-- makeBaseFunctor ''Stmt
-- makeBaseFunctor ''Exp
-- makeBaseFunctor ''Ty

--------------------------------------------------------------------------------
-- | AST Constants
-------------------------------------------------------------------------------
wild :: Var
wild =  "_"

constExp :: Exp -> EmitExp
constExp = ELambda wild


typeTag :: Ty -> String
typeTag = typeTag' . unroll 
  where
    typeTag' TNat     = "nat"
    typeTag' TInt     = "int"
    typeTag' TBool    = "bool"
    typeTag' (TSeq t) = "seq__" ++ typeTag t ++ "__"
    typeTag' _        = "unsupported"

qComment :: String -> Stmt
qComment = Mu . SDafny . ("// " ++)

--------------------------------------------------------------------------------
-- | Partition Utils
--------------------------------------------------------------------------------

range1 :: Var -> Range
range1 v = Range v (ENum $. 0) (ENum $. 1)


partition1 :: Range -> Partition
partition1 =  Partition . (: [])


-- | Extract all variables for each range in a partition
varFromPartition :: Partition -> [Var]
varFromPartition (Partition s) = [ x | (Range x _ _) <- s ]


-- | Compute all free partitions/ranges mentioned in the LHS of application
leftPartitions :: [Stmt] -> [Partition]
leftPartitions =
  concatMap (perStmt .$)
  where
    perStmt (SApply s _) = [s]
    -- TODO: query If and For recursively
    perStmt _            = []


(.:) :: (c -> d) -> (a -> b -> c) -> a -> b -> d
(.:) g f2 x y = g (f2 x y)
