{-# LANGUAGE
    DeriveAnyClass
  , DeriveDataTypeable
  , DeriveFoldable
  , DeriveFunctor
  , DeriveGeneric
  , DeriveTraversable
  , FlexibleContexts
  , FlexibleInstances
  , MultiParamTypeClasses
  , StandaloneDeriving
  , TemplateHaskell
  , TupleSections
  , TypeFamilies
  , TypeOperators
  , UndecidableInstances
  #-}

module Qafny.Syntax.AST where

import           Qafny.TTG

--------------------------------------------------------------------------------
import           Data.Bifunctor
import           Data.Data
import           Data.Functor.Foldable
    ( Base
    , Corecursive (embed)
    , Recursive (cata, project)
    )
import           Data.Functor.Foldable.TH (makeBaseFunctor)
import           Data.List.NonEmpty       (NonEmpty (..))
import qualified Data.Map.Strict          as Map
import           Data.Maybe               (fromMaybe)
import           Data.Sum
import           GHC.Generics             hiding ((:+:))
import           Text.Printf              (printf)

--------------------------------------------------------------------------------

data AExp
  = ANat Int
  | AVar Var
  deriving (Show, Eq, Ord, Data, Typeable)

data Ty
  = TNat
  | TInt
  | TBool
  | TSeq Ty
  | TQReg AExp
  | TMethod [Ty] [Ty] -- parameter and return types
  | TEmit EmitTy
  deriving (Show, Eq, Ord, Data, Typeable)

-- | EmitExp : Unchecked Types for Codegen Only
data EmitTy
  = TAny String
  deriving (Show, Eq, Ord, Data, Typeable)

data QTy
  = TNor
  | THad
  | TEN
  | TEN01
  deriving (Show, Eq, Ord, Data, Typeable)

type Var = String

data Binding x
  = Binding (XRec x Var) (XRec x Ty)

deriving instance (Typeable (Binding Source))
deriving instance (Typeable (Binding ()))
deriving instance (Data (Binding Source))
deriving instance (Data (Binding ()))

deriving instance (Show (XRec x Var), Show (XRec x Ty)) => Show (Binding x)
deriving instance (Eq (XRec x Var), Eq (XRec x Ty)) => Eq (Binding x)
deriving instance (Ord (XRec x Var), Ord (XRec x Ty)) => Ord (Binding x)

type Bindings x = [XRec x (Binding x)]

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
  deriving (Show, Eq, Ord, Data, Typeable)

data Op1
  = ONot
  | ONeg
  deriving (Show, Eq, Ord, Data, Typeable)


data GuardExp
  = GEPartition Partition (Maybe (Exp ())) -- guard partition with a split at
  deriving (Show, Eq)

-- the exp is not reversible
data Exp x
  = ENum Int
  | EVar Var
  | EWildcard
  | EHad
  | EQFT
  | ERQFT
  | EMea Var
  | EBool Bool
  | EApp Var (XRec x (Exp x))
  | EOp1 Op1 (XRec x (Exp x))
  | EOp2 Op2 (XRec x (Exp x)) (XRec x (Exp x))
  | EForall (Binding x) (Maybe (XRec x (Exp x))) (XRec x (Exp x))
  | EDafny String
  | EEmit EmitExp
  | EPartition Partition
  | ESpec Partition QTy (XRec x (SpecExp x))
  -- ?
  -- | RInd Var Exp -- boolean at var[exp], var must be Q type
  -- | REq Exp Exp Var Exp -- compare exp == exp and store the value in var[exp], var must be Q type
  -- | RLt Exp Exp Var Exp -- compare exp < exp and store the value in var[exp], var must be Q type


deriving instance (Typeable (Exp ()))
deriving instance (Data (Exp ()))
deriving instance (Typeable (Exp Source))
deriving instance (Data (Exp Source))
deriving instance (Generic (Exp ()))
deriving instance (Show (Exp ()))
deriving instance (Show (Exp Source))
deriving instance (Eq (Exp ()))
deriving instance (Eq (Exp Source))
deriving instance (Ord (Exp ()))
deriving instance (Ord (Exp Source))

-- deriving instance (Show (XRec x (Exp x))) => Show (Exp x)
-- deriving instance (Eq (XRec x (Exp x))) => Eq (Exp x)
-- deriving instance (Ord (XRec x (Exp x))) => Ord (Exp x)



data SpecExp x
  = SESpecNor  Var [XRec x (Exp x)]
  | SESpecEN   Var Intv [XRec x (Exp x)]
  | SESpecEN01 Var Intv Var Intv [XRec x (Exp x)]
  | SEWildcard
deriving instance (Show (XRec x (Exp x))) => Show (SpecExp x)
deriving instance (Eq (XRec x (Exp x))) => Eq (SpecExp x)
deriving instance (Ord (XRec x (Exp x))) => Ord (SpecExp x)
deriving instance (Typeable (SpecExp ()))
deriving instance (Data (SpecExp ()))
deriving instance (Typeable (SpecExp Source))
deriving instance (Data (SpecExp Source))

showExp :: Exp () -> String
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
  = ELambda Var (Exp ())
  | EMtSeq
  | EMakeSeq Ty (Exp ()) EmitExp
  | ECard (Exp ())
  | ECall Var [Exp ()]
  | ESelect (Exp ()) (Exp ())
  | ESlice (Exp ()) (Exp ()) (Exp ())
  | EDafnyVar Var
  | EOpChained (Exp ()) [(Op2, Exp ())]
  deriving  (Show, Eq, Ord, Data, Typeable)

data Conds
  = Requires (Exp ())
  | Ensures (Exp ())
  | Invariants (Exp ())
  | Separates Partition
  deriving Show

newtype Block x = Block { inBlock :: [XRec x (Stmt x)] }

deriving instance (Show (XRec x (Stmt x))) => Show (Block x)
deriving instance (Eq (XRec x (Stmt x))) => Eq (Block x)
deriving instance (Ord (XRec x (Stmt x))) => Ord (Block x)


-- TODO: refactor into record
data QMethod x = QMethod Var (Bindings x) [(XRec x (Binding x))] [(XRec x (Exp x))] [(XRec x (Exp x))] (Maybe (Block x))

deriving instance Show (QMethod ())
deriving instance Show (QMethod Source)


newtype QDafny = QDafny String
  deriving (Show)

newtype Toplevel x = Toplevel { unTop :: (QMethod x) :+: QDafny }

deriving instance Show (Toplevel ())
deriving instance Show (Toplevel Source)

instance (Injection q (QMethod x :+: QDafny)) => Injection q (Toplevel x) where
  inj = Toplevel . inj

data Intv = Intv (Exp ()) (Exp ())
  deriving (Eq, Show, Ord, Data, Typeable)

data Range = Range Var (Exp ()) (Exp ())
  deriving (Eq, Ord, Data, Typeable)

instance Show Range where
  show (Range x y z) = printf "%s[%s .. %s]" x (showExp y) (showExp z)

newtype Loc = Loc { deref :: Var }
  deriving (Eq, Ord)

instance Show Loc where
  show = deref

newtype Partition = Partition { unpackPart :: [Range] }
  deriving (Eq, Ord, Data, Typeable)


instance Show Partition where
  show = showPP . unpackPart
    where
      showPP []       = "∅"
      showPP (r : rs) = foldr (\r' s -> show r' ++ " ⊎ " ++ s) (show r) rs

data Stmt x
  = SAssert (XRec x (Exp x))
  | SCall (XRec x (Exp x)) [(XRec x (Exp x))]
  | SVar (XRec x (Binding x)) (Maybe (XRec x (Exp x)))
  | Var ::=: (XRec x (Exp x))
  | Partition :*=: (XRec x (Exp x))
  | SDafny String
  | SIf GuardExp Partition (Block x)
  -- TODO: Refactor 'For' with a record
  --     id  left             right            guard    invarants          separates Body
  | SFor Var (XRec x (Exp x)) (XRec x (Exp x)) GuardExp [(XRec x (Exp x))] Partition (Block x)
  | SEmit EmitStmt

deriving instance Show (Stmt ())
deriving instance Show (Stmt Source)
deriving instance Eq (Stmt ())
deriving instance Eq (Stmt Source)

data EmitStmt
  = SIfDafny (Exp ()) (Block ())
  | SBlock (Block ())
  | SForEmit Var (Exp ()) (Exp ()) [Exp ()] (Block ())
  deriving (Show, Eq)

type AST = [Toplevel ()]

type LAST = [Toplevel Source]


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
leftPartitions :: [Stmt x] -> [Partition]
leftPartitions =
  concatMap perStmt
  where
    perStmt ((:*=:) s _) = [s]
    -- TODO: query If and For recursively
    perStmt _            = []

-- | Collect all partitions with their types from spec expressions
specPartitionQTys :: [Exp x] -> [(Partition, QTy)]
specPartitionQTys es = [ (p, qty) | (ESpec p qty _) <- es ]


(.:) :: (c -> d) -> (a -> b -> c) -> (a -> b -> d)
(.:) = (.) . (.)

--------------------------------------------------------------------------------
-- * Recursion Schemes
--------------------------------------------------------------------------------
data ExpF f
  = ENumF Int
  | EVarF Var
  | EWildcardF
  | EHadF
  | EQFTF
  | ERQFTF
  | EMeaF Var
  | EBoolF Bool
  | EAppF Var f
  | EOp1F Op1 f
  | EOp2F Op2 f f
  | EForallF (Binding ()) (Maybe f) f
  | EDafnyF String
  | EEmitF EmitExp
  | EPartitionF Partition
  | ESpecF Partition QTy (XRec () (SpecExp ()))
  deriving (Functor, Foldable, Traversable, Show, Generic)

type instance Base (Exp ()) = ExpF
instance Recursive (Exp ())
instance Corecursive (Exp ())


--------------------------------------------------------------------------------
-- * Exp Utils
--------------------------------------------------------------------------------
instance Num (Exp ()) where
  e1 + e2 = EOp2 OAdd e1 e2
  e1 - e2 = EOp2 OSub e1 e2
  e1 * e2 = EOp2 OMul e1 e2
  negate = (0 -)
  abs = undefined
  signum = undefined
  fromInteger a = ENum (fromInteger a)



type AEnv = [(Var, Exp ())]
type IEnv = [(Var, NonEmpty (Exp ()))]

-- | Remove from 'IEnv' variables that are not in the free variable list
filterIEnv :: [Var] -> IEnv -> IEnv
filterIEnv fvs = filter (\(v, _) -> v `elem` fvs)

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
  fVars :: a -> [Var]

instance Substitutable (Exp ()) where
  subst = substE
  fVars = cata go
    where
      go :: ExpF [Var] -> [Var]
      go (EVarF x) = [x]
      go fvs       = concat fvs

instance Substitutable Partition where
  subst = substP
  fVars = concatMap fVars . unpackPart

instance Substitutable Range where
  subst = substR
  fVars (Range _ e1 e2) = fVars e1 ++ fVars e2

instance (Substitutable a) => Substitutable [a] where
  subst a = fmap (subst a)
  fVars = concatMap fVars

instance (Substitutable a, Substitutable b) => Substitutable (a, b) where
  subst a = bimap (subst a) (subst a)
  fVars = uncurry (++) . bimap fVars fVars

instance (Ord k, Substitutable k) => Substitutable (Map.Map k v) where
  subst a = Map.mapKeys (subst a)
  fVars = fVars . Map.keys

-- instance Substitutable QTy where
--   subst = const id
--   fVars = const []

-- instance Substitutable Loc where
--   subst = const id
--   fVars = const []



substE :: AEnv -> Exp () -> Exp ()
substE [] = id
substE env = go
  where
    go :: Exp () -> Exp ()
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


--------------------------------------------------------------------------------
-- * Vanilla Types

type Stmt' = Stmt ()
type Exp' = Exp ()
type Binding' = Binding ()
type Block' = Block ()
type SpecExp' = SpecExp ()
type Toplevel' = Toplevel ()

-- * Annotated Types
type LExp = XRec Source (Exp Source)
type LStmt = XRec Source (Stmt Source)

--------------------------------------------------------------------------------
-- unL :: LExp -> Exp'
-- unL (L _ e) = gmapT unL e
