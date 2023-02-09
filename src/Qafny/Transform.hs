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

data TEnv = TEnv
  { _kEnv :: Map.Map Var Ty
  }

data TState = TState
  { _sSt :: Map.Map Session QTy,
    _kSt :: Map.Map Var Ty,
    _symSt :: [Int], -- renaming state
    _rbSt :: Map.Map Var Var  -- renaming state
  }

$(makeLenses ''TState)
$(makeLenses ''TEnv)

instance Show TState where
  show st = "  Kind State:\n    " ++
            (intercalate "\n    " . map show . Map.toList) (st ^. kSt) ++
            "\n  Session State:\n    " ++
            (intercalate "\n    " . map show . Map.toList) (st ^. sSt) ++ 
            "\n  Renaming State:\n    " ++
            (intercalate "\n    " . map show . Map.toList) (st ^. rbSt)

instance Show TEnv where
  show st = "  Kind Environment" ++
            (intercalate "\n    " . map show . Map.toList) (st ^. kEnv)

initTEnv :: TEnv
initTEnv = TEnv { _kEnv = mempty }  

initTState :: TState
initTState = TState
  { _sSt = mempty
  , _kSt = mempty
  , _symSt = [1..]
  , _rbSt = mempty}  

-- | Generate a fresh symbol and add into the renaming buffer
gensym :: Var -> Transform Var
gensym s = do sym <- uses symSt $ (\x -> s ++ "_emited_" ++ x) . show . head
              symSt %= tail
              rbSt %= Map.insert s sym
              return sym

-- | Generate multiple symbols based on the type
gensymTys :: [Ty] -> Var -> Transform [Var]
gensymTys ty s = mapM (\t -> gensym (s ++ typeTag t)) ty 

--------------------------------------------------------------------------------
-- Error Reporting
--------------------------------------------------------------------------------
unknownVariableError :: String -> Transform a
unknownVariableError s =
  throwError $ "Variable `" ++ s ++ "` is not in the environemnt"

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
