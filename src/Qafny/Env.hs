{-# LANGUAGE
    LambdaCase
  , TemplateHaskell
  #-}
module Qafny.Env where

import           Control.Lens
import           Control.Lens.TH
import           Control.Monad.Except
import           Control.Monad.RWS
import           Data.Bifunctor
import           Data.List            (intercalate)
import qualified Data.Map.Strict      as Map
import           GHC.Stack
import           Qafny.AST
import           Text.Printf          (printf)

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
  , _qnum :: Exp -- assume each Q type variable is associated with a qubit num which is C type exp
  }


data TState = TState
  { _sSt    :: Map.Map Loc (Partition, QTy) -- partition type state
  , _xSt    :: Map.Map Var [(Range, Loc)] -- range reference state
  , _emitSt :: Map.Map Binding Var
  }

$(makeLenses ''TState)
$(makeLenses ''TEnv)

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
  { schROrigin :: Range -- the original range
  , schRTo     :: Range -- the range splitted _to_
  , schRsRem   :: [Range] -- the remainder range
  , schQty     :: QTy     -- entanglement types
  , schSMain   :: STuple  -- the partition that was splitted _from_
  , schSAux    :: STuple  -- the partition that was splitted _to_
  }
  deriving Show
