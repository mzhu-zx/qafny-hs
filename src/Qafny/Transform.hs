{-# LANGUAGE TemplateHaskell #-}
module Qafny.Transform where

import           Qafny.AST
import           Control.Monad.RWS
import           Control.Monad.Except
import           Control.Lens.TH
import           Control.Lens
import           Data.Bifunctor
import qualified Data.Map.Strict as Map 
import Data.List (intercalate)



--------------------------------------------------------------------------------
-- General 
--------------------------------------------------------------------------------
type Transform a = ExceptT String (RWS TEnv () TState) a

data CtxMode
  = CtxC
  | CtxQ
  deriving Show

data TEnv = TEnv
  { _kEnv :: Map.Map Var Ty
  , _ctx  :: CtxMode
  }

data TState = TState
  { _sSt :: Map.Map Session QTy       -- session type state
  , _xSt :: Map.Map Var Session       -- session reference state
  , _kSt :: Map.Map Var Ty            -- kind state
  , _symSt :: [Int]                   -- gensm state
  -- renaming state (maintained by `gensym`), indexed by metaVar and emittedType  
  , _rbSt :: Map.Map (Var, Ty) Var
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
            (intercalate "\n    " . map show . Map.toList) (st ^. rbSt) ++
            "\n  Number of Fresh Symbols: " ++ show (head (st ^. symSt) - 1)

instance Show TEnv where
  show st = "  Kind Environment" ++
            (intercalate "\n    " . map show . Map.toList) (st ^. kEnv)

initTEnv :: TEnv
initTEnv = TEnv { _kEnv = mempty, _ctx = CtxQ }  

initTState :: TState
initTState = TState
  { _sSt = mempty
  , _xSt = mempty
  , _kSt = mempty
  , _symSt = [1..]
  , _rbSt = mempty}  

-- | Generate a fresh symbol and add into the renaming buffer
gensym :: Var -> Ty -> Transform Var
gensym s t = do
  sym <-
    uses symSt $
      (\x -> s ++ "__" ++ typeTag t ++ "_emited_" ++ x) . show . head
  symSt %= tail
  rbSt %= (at (s, t) ?~ sym)
  return sym


-- | Generate a symbol at meta level without performing renaming
gensymMeta :: Var -> Transform Var
gensymMeta v =
  do sym <- uses symSt $ ((v ++ "__") ++ ) . show . head
     symSt %= tail
     return sym

gensymSessionMeta :: Session -> Transform Session
gensymSessionMeta (Session rs) =
  mapM inner rs <&> Session
  where
    inner (Ran r e1 e2) = gensymMeta r <&> flip (`Ran` e1) e2

-- | Generate multiple symbols based on the type
gensymTys :: [Ty] -> Var -> Transform [Var]
gensymTys ty s = mapM (gensym s) ty 

findSym :: Var -> Ty -> Transform Var
findSym v t =
  do
    me <- use (rbSt . at (v, t))
    err return me
 where
  err =
    maybe
      ( throwError $
          "the symbol `"
            ++ show v
            ++ "` of emitted type `"
            ++ show t
            ++ "` cannot be found in the renaming state."
      )

--------------------------------------------------------------------------------
-- Error Reporting
--------------------------------------------------------------------------------
unknownVariableError :: Var -> Transform a
unknownVariableError s =
  throwError $ "Variable `" ++ s ++ "` is not in the scope"

unknownSessionError :: Session -> Transform a
unknownSessionError s =
  throwError $ "Session `" ++ show s ++ "` is not in the scope"

handleWith :: Transform a -> Transform (Maybe a) -> Transform a
handleWith err = (>>= maybe err return)

--------------------------------------------------------------------------------
-- Wrapper
--------------------------------------------------------------------------------
runTransform :: Transform a -> (Either String a, TState, ())
runTransform = fuseError . (\x -> runRWS x initTEnv initTState) . runExceptT
  where
    fuseError :: (Either String a, TState, ()) -> (Either String a, TState, ())
    fuseError comp =
      _1 %~ first (++ "\ESC[0m\nCodegen terminted with an error!\n" ++ show st) $ comp
      where st = comp ^. _2
