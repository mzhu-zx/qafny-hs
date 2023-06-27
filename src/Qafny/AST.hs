{-# LANGUAGE FlexibleInstances, Rank2Types, RankNTypes, StandaloneDeriving,
             TypeSynonymInstances #-}

module Qafny.AST where

import           Control.Monad.Identity (Identity)
import           Qafny.HKD
import           Text.Printf            (printf)


data TyK f
  = TNat
  | TInt
  | TBool
  | TSeq (HKD f (TyK f))
  | TQReg Int
  | TMethod [HKD f (TyK f)] [HKD f (TyK f)] -- parameter and return types
  | TEmit EmitTy
  -- deriving (Show, Eq, Ord)

type Ty = TyK Identity
deriving instance Show Ty
deriving instance Eq Ty
deriving instance Ord Ty

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

data BindingK f
  = Binding Var (TyK f)

type Binding = BindingK Identity
deriving instance Show Binding
deriving instance Eq Binding
deriving instance Ord Binding

type BindingsK  f = [BindingK f]

type Bindings = BindingsK Identity

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
data ExpK f
  = ENum Int
  | EVar Var
  | EWildcard
  | EHad
  | EQFT
  | ERQFT
  | EMea Var
  | EBool Bool
  | EApp Var (HKD f (ExpK f))
  | EOp1 Op1 (HKD f (ExpK f))
  | EOp2 Op2 (HKD f (ExpK f)) (HKD f (ExpK f))
  | EForall (BindingK f) (Maybe (HKD f (ExpK f))) (HKD f (ExpK f))
  | EDafny String
  | EEmit EmitExp
  | EPartition Partition
  | ESpec Partition QTy (HKD f (ExpK f))
  | EQSpec Var Intv [HKD f (ExpK f)]
  | EQSpec01 Var Intv Var Intv [HKD f (ExpK f)]
  -- ?
  -- | RInd Var (f Exp) -- boolean at var[exp], var must be Q type
  -- | REq (f Exp) (f Exp) Var (f Exp) -- compare exp == exp and store the value in var[exp], var must be Q type
  -- | RLt (f Exp) (f Exp) Var (f Exp) -- compare exp < exp and store the value in var[exp], var must be Q type

type Exp = ExpK Identity
deriving instance Show Exp
deriving instance Eq Exp
deriving instance Ord Exp

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

type Returns f = [BindingK f]

data CondsK f
  = Requires (ExpK f)
  | Ensures (ExpK f)
  | Invariants (ExpK f)
  | Separates Partition

type Conds = CondsK Identity

type RequiresK f = [ExpK f]
type EnsuresK f = [ExpK f]
type InvariantsK f = [ExpK f]
type Separates = Partition

type Requires = RequiresK Identity
type Ensures = EnsuresK Identity
type Invariants = InvariantsK Identity


newtype BlockK f = Block { inBlock :: [StmtK f] }

type Block = BlockK Identity
deriving instance Show Block
deriving instance Eq Block

data ToplevelK f
  = QMethod Var (BindingsK f) (Returns f) (RequiresK f) (EnsuresK f) (Maybe (BlockK f))
  | QDafny (HKD f String)

type Toplevel = ToplevelK Identity

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

data StmtK f
  = SAssert (ExpK f)
  | SCall (ExpK f) [ExpK f]
  | SVar (BindingK f) (Maybe (ExpK f))
  | SAssign Var (ExpK f)
  | SApply Partition (ExpK f)
  | SDafny String
  | SIf (ExpK f) Separates (BlockK f)
  --     id  left     right    guard    invarants separates Body
  | SFor Var (ExpK f) (ExpK f) (ExpK f) [ExpK f]  Partition (BlockK f)
  | SEmit EmitStmt

type Stmt = StmtK Identity
deriving instance Show Stmt
deriving instance Eq Stmt

data EmitStmt
  = SIfDafny Exp Block
  | SBlock Block
  | SForEmit Var Exp Exp [Exp] Block
  deriving (Show, Eq)

type ASTK f = [ToplevelK f]
type AST = ASTK Identity

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
typeTag (TSeq t) = "seq__" ++ typeTag t ++ "__"
typeTag _        = "unsupported"

qComment :: String -> Stmt
qComment = SDafny . ("// " ++)

--------------------------------------------------------------------------------
-- | Partition Utils
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
