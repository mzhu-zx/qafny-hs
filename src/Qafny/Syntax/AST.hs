{-# LANGUAGE
    DataKinds
  , DeriveAnyClass
  , DeriveFoldable
  , DeriveFunctor
  , DeriveGeneric
  , DeriveTraversable
  , FlexibleContexts
  , FlexibleInstances
  , GADTs
  , ImpredicativeTypes
  , MultiParamTypeClasses
  , NamedFieldPuns
  , RankNTypes
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
-- import           Data.Data
import           Data.Functor.Foldable
    (Base, Corecursive (embed), Recursive (cata, project))
import           Data.Kind
    (Type)
import           Data.List.NonEmpty
    (NonEmpty (..))
import qualified Data.Map.Strict       as Map
import           Data.Maybe
    (fromMaybe)
import           Data.Sum
import           GHC.Generics          hiding
    ((:+:))
import           Text.Printf
    (printf)
--------------------------------------------------------------------------------

data AExp
  = ANat Int
  | AVar Var
  deriving (Show, Eq, Ord)

aexpToExp :: AExp -> Exp ()
aexpToExp (ANat i) = ENum i
aexpToExp (AVar v) = EVar v

-- | The good thing about this design is that I don't need to modify the
-- emitState when creating a new phaseRef.
--
-- The only bad thing is that everytime
-- I want to get the pointer to the phase, I need to resolve through `sSt`,
-- which is not too bad because phase are designed to live with partitiions
-- instead of with ranges :)
--
-- TODO: move this into the proposal
--
data PhaseRef = PhaseRef
  { prBase :: Var -- | pointer to the base
  , prRepr :: Var -- | pointer to its representation
  }
  deriving (Show, Eq, Ord)

mkPhaseRef :: Var -> Var -> PhaseRef
mkPhaseRef prBase prRepr = PhaseRef { prBase, prRepr }

-- | PhaseTy associated with corresponding emitted vars
data PhaseTy
  = PT0
  | PTN Int PhaseRef
  deriving (Show, Eq, Ord)

phaseTyN :: Int -> Var -> Var -> PhaseTy
phaseTyN n vBase vRepr = PTN n $ PhaseRef { prBase=vBase, prRepr=vRepr }

data Ty
  = TNat
  | TInt
  | TBool
  | TSeq Ty
  | TQReg AExp
  -- | TMethod [Ty] [Ty] -- parameter and return types
  | TEmit EmitTy
  deriving (Show, Eq, Ord)

data MethodElem
  = MTyPure Var Ty
  | MTyQuantum Var Exp'
  deriving (Show, Eq, Ord)

data MethodType = MethodType
  -- Parameters for the source method (Type resolution level)
  { mtSrcParams   :: [MethodElem]
  , mtSrcReturns  :: [MethodElem]
  , mtInstantiate :: Map.Map Var Range -> [(Partition, QTy, [Int])]
  , mtReceiver    :: Map.Map Var Range -> [(Partition, QTy, [Int])]
  -- , mtDebugInit :: [(Partition, QTy)]
  }

instance Show MethodType where
  show MethodType {mtSrcParams=ts, mtSrcReturns=ts'} =
    show ts ++ "\n" ++ show ts'

-- | EmitExp : Unchecked Types for Codegen Only
data EmitTy
  = TAny String
  deriving (Show, Eq, Ord)

tyReal :: Ty
tyReal = TEmit $ TAny "real"

data QTy
  = TNor
  | THad
  | TEN
  | TEN01
  deriving (Show, Eq, Ord)

type Var = String

newtype MTy = MTy { unMTy :: Ty :+: MethodType }

instance Show MTy where
  show (MTy (Inl t)) = show t
  show (MTy (Inr m)) = show (mtSrcParams m) ++ show (mtSrcReturns m)

projTy :: MTy -> Maybe Ty
projTy = projLeft . unMTy

projMethodTy :: MTy -> Maybe MethodType
projMethodTy = projRight . unMTy

instance Injection Ty MTy where
  inj = MTy . inj

instance Injection MethodType MTy where
  inj = MTy . inj



data Binding x
  = Binding (XRec x Var) Ty



-- deriving instance (Typeable (Binding Source))
-- deriving instance (Typeable (Binding ()))
-- deriving instance (Data (Binding Source))
-- deriving instance (Data (Binding ()))

deriving instance (Show (XRec x Var), Show (XRec x Ty)) => Show (Binding x)
deriving instance (Eq (XRec x Var), Eq (XRec x Ty)) => Eq (Binding x)
deriving instance (Ord (XRec x Var), Ord (XRec x Ty)) => Ord (Binding x)

type Bindings x = [XRec x (Binding x)]

-- type EBinds = QTy :+: PhaseTy :+: Ty


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
  deriving (Show, Eq, Ord-- , Data, Typeable
           )

data Op1
  = ONot
  | ONeg
  deriving (Show, Eq, Ord-- , Data, Typeable
           )


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
  | EApp Var [XRec x (Exp x)]
  | EOp1 Op1 (XRec x (Exp x))
  | EOp2 Op2 (XRec x (Exp x)) (XRec x (Exp x))
  | EForall (Binding x) (Maybe (XRec x (Exp x))) (XRec x (Exp x))
  | EDafny String
  | EEmit EmitExp
  | EPartition Partition
  | ESpec Partition QTy [QSpecF (XRec x (Exp x))]
  | ERepr Range
  | ELambda PhaseBinder Var (Maybe PhaseExp) (XRec x (Exp x))

-- Amplitude expression
data AmpExpF f
  = ADefault
  | AISqrt f f
  | ASin f
  | ACos f
  deriving (Functor, Traversable, Foldable)

deriving instance Generic (AmpExpF f)
deriving instance Show f => Show (AmpExpF f)
deriving instance Eq f => Eq (AmpExpF f)
deriving instance Ord f => Ord (AmpExpF f)

type AmpExp = AmpExpF Exp'

data PhaseExpF f :: Type where
  PhaseZ :: PhaseExpF f
  PhaseOmega :: f -> f -> PhaseExpF f
  PhaseSumOmega :: Range -> f -> f -> PhaseExpF f
  PhaseWildCard :: PhaseExpF f
  deriving (Functor, Traversable, Foldable)

type PhaseExp = PhaseExpF Exp'
type PhaseBinder = PhaseExpF Var

deriving instance Generic (PhaseExpF f)
deriving instance Show f => Show (PhaseExpF f)
deriving instance Eq f => Eq (PhaseExpF f)
deriving instance Ord f => Ord (PhaseExpF f)

deriving instance (Generic (Exp ()))
deriving instance (Generic (Exp Source))
deriving instance (Show (Exp ()))
deriving instance (Show (Exp Source))
deriving instance (Eq (Exp ()))
deriving instance (Eq (Exp Source))
deriving instance (Ord (Exp ()))
deriving instance (Ord (Exp Source))


data SpecExpF f
  = SESpecNor  Var f
  | SESpecEN   Var Intv [f]
  | SESpecEN01 Var Intv Var Intv [f]
  | SEWildcard
  deriving (Functor, Foldable, Traversable)

deriving instance Generic (SpecExpF f)
deriving instance (Show f) => Show (SpecExpF f)
deriving instance (Eq f) => Eq (SpecExpF f)
deriving instance (Ord f) => Ord (SpecExpF f)

type SpecExp = SpecExpF Exp'

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
  = EMtSeq
  | EMakeSeq Ty (Exp ()) Exp'
  | ECard (Exp ())
  | ECall Var [Exp ()]
  | ESelect (Exp ()) (Exp ())
  | ESlice (Exp ()) (Exp ()) (Exp ())
  | EDafnyVar Var
  | EMultiLambda [Var] (Exp ())
  | EOpChained (Exp ()) [(Op2, Exp ())]
  deriving  (Show, Eq, Ord-- , Data, Typeable
            )

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
  deriving (Eq, Show, Ord-- , Data, Typeable
           )

-- Range includes the left but exclude the right
data Range = Range Var (Exp ()) (Exp ())
  deriving (Eq, Ord-- , Data, Typeable
           )

instance Show Range where
  show (Range x y z) = printf "%s[%s .. %s]" x (showExp y) (showExp z)

newtype Loc = Loc { deref :: Var }
  deriving (Eq, Ord)

instance Show Loc where
  show = deref

newtype Partition = Partition { ranges :: [Range] }
  deriving (Eq, Ord-- , Data, Typeable
           )

unpackPart :: Partition -> [Range]
unpackPart = ranges

instance Show Partition where
  show = showPP . unpackPart
    where
      showPP []       = "∅"
      showPP (r : rs) = foldr (\r' s -> show r' ++ " ⊎ " ++ s) (show r) rs

data Stmt x where
  SAssert :: (XRec x (Exp x)) -> Stmt x
  SCall :: Var -> [(XRec x (Exp x))] -> Stmt x
  SVar :: (XRec x (Binding x)) -> (Maybe (XRec x (Exp x))) -> Stmt x
  (::=:) :: Var -> (XRec x (Exp x)) -> Stmt x
  (:*=:) :: Partition -> (XRec x (Exp x)) -> Stmt x
  SDafny :: String -> Stmt x
  SIf :: GuardExp -> Partition -> (Block x) -> Stmt x
  -- TODO: Refactor 'For' with a record
  --     id      left                right               guard       invarants             separates Body
  SFor :: Var -> (XRec x (Exp x)) -> (XRec x (Exp x)) -> GuardExp -> [(XRec x (Exp x))] -> Maybe Partition -> (Block x) -> Stmt x
  SEmit :: EmitStmt -> Stmt x

deriving instance Show (Stmt ())
deriving instance Show (Stmt Source)
deriving instance Eq (Stmt ())
deriving instance Eq (Stmt Source)

data EmitStmt
  = SIfDafny (Exp ()) (Block ())
  | SBlock (Block ())
  | SForEmit Var (Exp ()) (Exp ()) [Exp ()] (Block ())
  | SVars [Binding ()] (Exp ())
  | (:*:=:) [Var] (Exp ())
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
  | EAppF Var [f]
  | EOp1F Op1 f
  | EOp2F Op2 f f
  | EForallF (Binding ()) (Maybe f) f
  | EDafnyF String
  | EEmitF EmitExp
  | EPartitionF Partition
  | ESpecF Partition QTy [QSpecF f]
  | EReprF Range
  | ELambdaF PhaseBinder Var (Maybe PhaseExp) f
  deriving (Functor, Foldable, Traversable, Show, Generic)

type instance Base (Exp ()) = ExpF
instance Recursive (Exp ())
instance Corecursive (Exp ())


data QSpecF f
  = QSpecF { amp   :: AmpExpF f
           , phase :: PhaseExpF f
           , spec  :: SpecExpF f
           }
  deriving (Functor, Foldable, Traversable)

deriving instance Generic (QSpecF f)
deriving instance Show f => Show (QSpecF f)
deriving instance Eq f => Eq (QSpecF f)
deriving instance Ord f => Ord (QSpecF f)
type QSpec = QSpecF Exp'

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

instance Substitutable a => Substitutable (a :+: b) where
  subst a (Inl r) = inj $ subst a r
  subst _ b       = b
  fVars (Inl r) = fVars r
  fVars _       = []


substMapKeys :: (Ord k, Substitutable k) => AEnv -> Map.Map k v -> Map.Map k v
substMapKeys a = Map.mapKeys (subst a)

fVarMapKeys :: Substitutable k => Map.Map k v -> [Var]
fVarMapKeys = fVars . Map.keys

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
type Toplevel' = Toplevel ()
type QSpec' = QSpecF ()

-- * Annotated Types
type LExp = XRec Source (Exp Source)
type LStmt = XRec Source (Stmt Source)

--------------------------------------------------------------------------------
-- unL :: LExp -> Exp'
-- unL (L _ e) = gmapT unL e
