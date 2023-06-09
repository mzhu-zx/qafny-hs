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
type Zipper m a r = (a -> a -> m r) -> m [r]

type STuple = (Loc, Session, QTy) -- STuple { unS :: (Loc, Session, QTy) }

--------------------------------------------------------------------------------
-- General
--------------------------------------------------------------------------------
type Transform a = ExceptT String (RWS TEnv [(String, Ty)] TState) a

data CtxMode
  = CtxC
  | CtxQ
  deriving Show

data TEnv = TEnv
  { _kEnv :: Map.Map Var Ty
  , _ctx  :: CtxMode
  , _qnum :: Exp -- assume each Q type variable is associated with a qubit num which is C type exp
  }


data TState = TState
  { _sSt  :: Map.Map Loc (Session, QTy) -- session type state
  , _xSt  :: Map.Map Var Loc            -- range reference state
  , _kSt  :: Map.Map Var Ty             -- kind state
  , _emitSt :: Map.Map Binding Var
  }

$(makeLenses ''TState)
$(makeLenses ''TEnv)

instance Show TState where
  show st = "  Kind State:\n    " ++
            (intercalate "\n    " . map show . Map.toList) (st ^. kSt) ++
            "\n  Session Reference State:\n    " ++
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
  , _kSt = mempty
  , _emitSt = mempty}

--------------------------------------------------------------------------------
-- Combinator
--------------------------------------------------------------------------------

only1 :: (HasCallStack, Show a) => Transform [a] -> Transform a
only1 = (=<<) $
  \case
    [x] -> return x
    e -> error $ "[only1]: " ++ show e ++ "is not a singleton"

--------------------------------------------------------------------------------
-- Wrapper
--------------------------------------------------------------------------------
type Production a = (Either String a, TState, [(String, Ty)])

runTransform :: Transform a -> Production a
runTransform = fuseError . (\x -> runRWS x initTEnv initTState) . runExceptT
  where
    -- fuseError :: (Either String a, TState, [String]) -> (Either String a, TState, [String])
    fuseError (eit, st, writ) =
      (first (++ "\ESC[0m\nCodegen terminted with an error!\n" ++ show st) eit, st, writ)
