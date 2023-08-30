{-# LANGUAGE
    LambdaCase
  , TemplateHaskell
  #-}
module Qafny.Env where

import           Control.Lens
import           Data.List       (intercalate)
import qualified Data.Map.Strict as Map
import           Qafny.Syntax.AST
import           Text.Printf     (printf)

--------------------------------------------------------------------------------
-- High-Order Types
--------------------------------------------------------------------------------
newtype STuple = STuple { unSTup :: (Loc, Partition, QTy) } -- STuple { unS :: (Loc, Partition, QTy) }

instance Show STuple where
  show (STuple (loc, s, qt)) =
    printf " <%s :: %s ↦ %s>" (show loc) (show qt) (show s)

--------------------------------------------------------------------------------
-- General
--------------------------------------------------------------------------------
data CtxMode
  = CtxC
  | CtxQ
  deriving Show

type KEnv = Map.Map Var Ty

data TEnv = TEnv
  { _kEnv :: KEnv
  , _ctx  :: CtxMode
  , _qnum :: Exp' -- assume each Q type variable is associated with a qubit num which is C type exp
  }


data TState = TState
  { _sSt    :: Map.Map Loc (Partition, QTy) -- partition type state
  , _xSt    :: Map.Map Var [(Range, Loc)] -- range reference state
  , _emitSt :: Map.Map RBinding Var
  }

$(makeLenses ''TState)
$(makeLenses ''TEnv)

-- instance Substitutable TState where
--   subst aenv ts@TState{_sSt=sSt', _xSt=xSt'} =
--     ts { _sSt=subst aenv <$> sSt'
--        , _xSt=subst aenv <$> xSt'
--        }
--   fVars TState{_sSt=sSt', _xSt=xSt'} =
--     concatMap fVars sSt' ++ concatMap fVars xSt'

instance Show TState where
  show st = "\n  Partition Reference State:\n    " ++
            (intercalate "\n    " . map show . Map.toList) (st ^. xSt) ++
            "\n  Partition State:\n    " ++
            (intercalate "\n    " . map show . ((\(x, (y,z)) -> STuple (x, y, z)) <$>) . Map.toList) (st ^. sSt) ++
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
  { schROrigin     :: Range   -- | the original range
  , schRTo         :: Range   -- | the range splitted _to_
  , schRsRem       :: [Range] -- | the remainder range
  , schQty         :: QTy     -- | entanglement types
  , schSMain       :: STuple  -- | the partition that was splitted _from_
  --  , schSAux    :: STuple  -- | the partition that was splitted _to_
  , schVEmitOrigin :: Var     -- | the emit variable of the original range
  , schVsEmitAll   :: [Var]   -- | the emit variables of new ranges
  }
  deriving Show

data CastScheme = CastScheme
  { schVsOldEmit :: [Var]
  , schTOldEmit  :: Ty
  , schVsNewEmit :: [Var]
  , schTNewEmit  :: Ty
  , schQtOld     :: QTy
  , schQtNew     :: QTy
  , schRsCast    :: [Range] -- | casted ranges
  }
  deriving Show

data MergeScheme
  = MJoin JoinStrategy  -- ^ Join a 'Range' into an existing 'Range' 
  | MMove 
  
data JoinStrategy = JoinStrategy
  { jsRMain :: Range
  , jsQtMain :: QTy 
  , jsRResult :: Range 
  , jsRMerged :: Range
  , jsQtMerged :: QTy
  }

