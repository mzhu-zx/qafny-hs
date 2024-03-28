{-# LANGUAGE
    DataKinds
  , FlexibleInstances
  , GADTs
  , LambdaCase
  , TemplateHaskell
  , TypeApplications
  , TypeOperators
  #-}
module Qafny.Syntax.IR where

import           Control.Lens
import           Data.Bifunctor
import           Data.List
    (intercalate)
import qualified Data.Map.Strict          as Map
import           Data.Sum
import           Qafny.Partial
import           Qafny.Syntax.AST
import           Qafny.Syntax.EmitBinding

import           Data.List.NonEmpty
    (NonEmpty)
--------------------------------------------------------------------------------
-- High-Order Types
--------------------------------------------------------------------------------
-- TODO: Migrate to Locus representation
data LocusT t =
  Locus { loc     :: Loc           -- ^ identifier for the locus
        , part    :: PartitionT t  -- ^ partition
        , qty     :: QTy           -- ^ entanglement type
        , degrees :: [Int]         -- ^ degrees of phase info
        }

type Locus = LocusT []
deriving instance Show Locus
deriving instance Eq Locus

--------------------------------------------------------------------------------
-- Methods
--------------------------------------------------------------------------------
data MethodElem
  = MTyPure Var Ty
  | MTyQuantum Var Exp'
  deriving (Show, Eq, Ord)

data MethodType = MethodType
  -- Parameters for the source method (Type resolution level)
  { mtSrcParams   :: [MethodElem]
  , mtSrcReturns  :: [MethodElem]
  , mtInstantiate :: Map.Map Var Range -> [(Partition, QTy, Maybe Int)]
  , mtReceiver    :: Map.Map Var Range -> [(Partition, QTy, Maybe Int)]
  -- , mtDebugInit :: [(Partition, QTy)]
  }

instance Show MethodType where
  show MethodType {mtSrcParams=ts, mtSrcReturns=ts'} =
    show ts ++ "\n" ++ show ts'


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

--------------------------------------------------------------------------------
-- General
--------------------------------------------------------------------------------
data CtxMode
  = CtxC
  | CtxQ
  deriving Show

type KEnv = Map.Map Var MTy

data TEnv = TEnv
  { _kEnv :: KEnv
  , _ctx  :: CtxMode
  , _qnum :: Exp' -- assume each Q type variable is associated with a qubit num which is C type exp
  }

type RangeOrLoc = Range :+: Loc
type EmitState = Map.Map RangeOrLoc EmitData

data TState = TState
  { _sSt    :: Map.Map Loc (Partition, (QTy, [Int])) -- partition type state
  , _xSt    :: Map.Map Var [(Range, Loc)]            -- range reference state
  , _emitSt :: EmitState
  }

instance Substitutable TState where
  subst a (TState{ _sSt = s, _xSt = x, _emitSt = es }) =
    TState { _sSt = first (subst a) <$> s
           , _xSt = (first (subst a) <$>) <$> x
           , _emitSt = Map.mapKeys (subst a) es
           }
  fVars (TState{ _sSt = s, _xSt = x, _emitSt = es }) =
    concatMap (fVars . fst) s
    ++ fVarMapKeys es
    ++ concatMap (concatMap $ fVars . fst) (Map.elems x)

instance Reducible TState where
  reduce (TState{ _sSt = s, _xSt = x, _emitSt = es }) =
    TState { _sSt = first reduce <$> s
           , _xSt = (first reduce <$>) <$> x
           , _emitSt = Map.mapKeys reduce es
           }

$(makeLenses ''TState)
$(makeLenses ''TEnv)

instance Show TState where
  show st = "\n  Partition Reference State:\n    " ++
            (intercalate "\n    " . map show . Map.toList) (st ^. xSt) ++
            "\n  Partition State:\n    " ++
            (intercalate "\n    " .
             map show . ((\(x, (y,z)) -> (x, y, z)) <$>) . Map.toList)
            (st ^. sSt) ++
            "\n  Renaming State:\n    " ++
            (intercalate "\n    " . map show . Map.toList) (st ^. emitSt)

instance Show TEnv where
  show st = "  Kind Environment" ++
            (intercalate "\n    " . map show . Map.toList) (st ^. kEnv)

initTEnv :: TEnv
initTEnv = TEnv { _kEnv = mempty, _ctx = CtxQ, _qnum = ENum 0 }

initTState :: TState
initTState = TState
  { _sSt = mempty
  , _xSt = mempty
  , _emitSt = mempty
  }

data SplitScheme = SplitScheme
  { schEdAffected   :: (Range, EmitData, EmitData)
    -- ^ Both locus and range `EmitData` for the affected range
  , schEdSplit      :: (Range, EmitData)
    -- ^ The range `EmitData` for the split range. The affected one shares the
    -- same locus as the split one.
  , schEdRemainders :: NonEmpty (Range, EmitData, EmitData)
    -- ^ Both locus and range `EmitData` for each (singleton) remainders
  }
  deriving Show

data CastScheme = CastScheme
  { schVsOldEmit :: [(Var, Ty)]
  , schVsNewEmit :: [(Var, Ty)]
  , schQtOld     :: QTy
  , schQtNew     :: QTy
  , schRsCast    :: [Range] -- | casted ranges
  }
  deriving Show

data MergeScheme
  = MJoin JoinStrategy  -- ^ Join a 'Range' into an existing 'Range'
  | MMove
  | MEqual EqualStrategy -- ^ Join two copies of data of the same range
  deriving Show

data EqualStrategy = EqualStrategy
  { esRange :: Range     -- ^ range
  , esQTy   :: QTy       -- ^ QTy of the corresponding range
  , esVMain :: (Var, Ty) -- ^ the var to stay
  , esVAux  :: (Var, Ty) -- ^ the var to be absorbed
  }
  deriving Show

data JoinStrategy = JoinStrategy
  { jsRMain    :: Range
  , jsQtMain   :: QTy
  , jsRResult  :: Range
  , jsRMerged  :: Range
  , jsQtMerged :: QTy
  }
  deriving Show

