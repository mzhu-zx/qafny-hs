{-# LANGUAGE
    DeriveFoldable
  , DeriveFunctor
  , DeriveTraversable
  , FlexibleContexts
  , FlexibleInstances
  , MultiParamTypeClasses
  , TemplateHaskell
  , TypeFamilies
  , TypeOperators
  , TupleSections
  , UndecidableInstances
  #-}

module Qafny.AST where

import           Control.Monad            (forM)
import           Data.Functor.Foldable
    ( Corecursive (embed)
    , Recursive (cata, project)
    )
import           Data.Functor.Foldable.TH (makeBaseFunctor)
import           Data.List.NonEmpty (NonEmpty (..))
import           Data.Maybe               (fromMaybe)
import           Data.Sum
import           Text.Printf              (printf)

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

newtype RBinding = RBinding { unRBinding :: (Range, Ty) }
  deriving (Eq, Ord)

instance Show RBinding where
  show = show . unRBinding 

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


data GuardExp
  = GEPartition Partition (Maybe Exp) -- guard partition with a split at
  deriving (Show, Eq)

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
  | ESpec Partition QTy SpecExp
  -- ?
  | RInd Var Exp -- boolean at var[exp], var must be Q type
  | REq Exp Exp Var Exp -- compare exp == exp and store the value in var[exp], var must be Q type
  | RLt Exp Exp Var Exp -- compare exp < exp and store the value in var[exp], var must be Q type
  deriving (Show, Eq, Ord)

data SpecExp
  = SESpecNor  Var [Exp]
  | SESpecEN   Var Intv [Exp]
  | SESpecEN01 Var Intv Var Intv [Exp]
  | SEWildcard
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
  | ESlice Exp Exp Exp
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

data QMethod = QMethod Var Bindings Returns Requires Ensures (Maybe Block)
  deriving (Show)
newtype QDafny = QDafny String
  deriving (Show)

newtype Toplevel = Toplevel { unTop :: QMethod :+: QDafny }
  deriving (Show)

instance (Injection q (QMethod :+: QDafny)) =>Injection q Toplevel where
  inj = Toplevel . inj

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
      showPP []       = "∅"
      showPP (r : rs) = foldr (\r' s -> show r' ++ " ⊎ " ++ s) (show r) rs

data Stmt
  = SAssert Exp
  | SCall Exp [Exp]
  | SVar Binding (Maybe Exp)
  | SAssign Var Exp
  | SApply Partition Exp
  | SDafny String
  | SIf GuardExp Separates Block
  --     id left right guard    invarants separates Body
  | SFor Var Exp Exp   GuardExp [Exp]     Partition   Block
  | SEmit EmitStmt
  deriving (Show, Eq)

data EmitStmt
  = SIfDafny Exp Block
  | SBlock Block
  | SForEmit Var Exp Exp [Exp] Block
  deriving (Show, Eq)

type AST = [Toplevel]


typeTag :: Ty -> String
typeTag TNat     = "nat"
typeTag TInt     = "int"
typeTag TBool    = "bool"
typeTag (TSeq t) = "_seqL_" ++ typeTag t ++ "_R_"
typeTag _        = "unsupported"


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

-- | Collect all partitions with their types from spec expressions
specPartitionQTys :: [Exp] -> [(Partition, QTy)]
specPartitionQTys es = [ (p, qty) | (ESpec p qty _) <- es ]


(.:) :: (c -> d) -> (a -> b -> c) -> a -> b -> d
(.:) g f2 x y = g (f2 x y)


--------------------------------------------------------------------------------
-- * Recursion Schemes
--------------------------------------------------------------------------------
makeBaseFunctor ''Exp

--------------------------------------------------------------------------------
-- * Exp Utils
--------------------------------------------------------------------------------
instance Num Exp where
  e1 + e2 = EOp2 OAdd e1 e2 
  e1 - e2 = EOp2 OSub e1 e2 
  e1 * e2 = EOp2 OMul e1 e2 
  negate = (0 -) 
  abs = undefined
  signum = undefined
  fromInteger a = ENum (fromInteger a)

  

fVars :: Exp -> [Var]
fVars = cata go
  where
    go :: ExpF [Var] -> [Var]
    go (EVarF x) = [x]
    go fvs       = concat fvs


type AEnv = [(Var, Exp)]
type IEnv = [(Var, NonEmpty Exp)]

nondetIEnv :: IEnv -> NonEmpty AEnv
nondetIEnv = traverse (\(v, ne) -> (v,) <$> ne) 

initAEnv :: AEnv
initAEnv = []

initIEnv :: IEnv
initIEnv = []


-- | Perform expression subtitution
--
class Substitutable a where
  subst :: AEnv -> a -> a
  
instance Substitutable Exp where
  subst = substE

instance Substitutable Partition where
  subst = substP

instance Substitutable Range where
  subst = substR

substE :: AEnv -> Exp -> Exp
substE [] = id
substE env = go
  where
    go :: Exp -> Exp
    go (EVar x)       = EVar x `fromMaybe` lookup x env
    go (ESpec p q e)  = ESpec (substP env p) q e
    go (EPartition p) = EPartition (substP env p)
    go e              = embed $ go <$> project e


substP :: AEnv -> Partition -> Partition
substP [] = id
substP env =
  Partition . (substR env <$> ) . unpackPart


substR :: AEnv -> Range -> Range
substR [] r = r
substR env (Range x l r) =
  Range x (go l) (go r)
  where
    go = substE env
