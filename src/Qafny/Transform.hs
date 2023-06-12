{-# LANGUAGE LambdaCase, TemplateHaskell #-}
module Qafny.Transform where

import           Control.Lens
import           Control.Lens.TH
import           Control.Monad.Except
import           Control.Monad.RWS
import           Data.Bifunctor
import           Data.List            (intercalate)
import qualified Data.Map.Strict      as Map
import           GHC.Stack
import           Qafny.AST

--------------------------------------------------------------------------------
-- High-Order Types
--------------------------------------------------------------------------------
type STuple = (Loc, Session, QTy) -- STuple { unS :: (Loc, Session, QTy) }

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
  { _sSt  :: Map.Map Loc (Session, QTy) -- session type state
  , _xSt  :: Map.Map Var Loc            -- range reference state
  , _emitSt :: Map.Map Binding Var
  }

$(makeLenses ''TState)
$(makeLenses ''TEnv)

instance Show TState where
  show st = "\n  Session Reference State:\n    " ++
            (intercalate "\n    " . map show . Map.toList) (st ^. xSt) ++
            "\n  Session State:\n    " ++
            (intercalate "\n    " . map show . Map.toList) (st ^. sSt) ++
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
  , _emitSt = mempty}

