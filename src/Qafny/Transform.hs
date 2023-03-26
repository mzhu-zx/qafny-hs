{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE LambdaCase #-}
module Qafny.Transform where

import           Qafny.AST
import           Control.Monad.RWS
import           Control.Monad.Except
import           Control.Lens.TH
import           Control.Lens
import           Data.Bifunctor
import qualified Data.Map.Strict as Map 
import           Data.List (intercalate)
import           GHC.Stack

--------------------------------------------------------------------------------
-- High-Order Types
--------------------------------------------------------------------------------
type Zipper a r = (a -> a -> Transform r) -> Transform [r]


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
  { _sSt :: Map.Map Session QTy       -- session type state
  , _xSt :: Map.Map Var Session       -- range reference state
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
initTEnv = TEnv { _kEnv = mempty, _ctx = CtxQ, _qnum = ENum 0 }  

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
  tell [(sym, t)]
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
    inner (Range r e1 e2) = gensymMeta r <&> flip (`Range` e1) e2

-- | Generate multiple symbols based on the type
gensymTys :: [Ty] -> Var -> Transform [Var]
gensymTys ty s = mapM (gensym s) ty 

-- | Find a symbol based on its emitted type
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
-- Combinator
--------------------------------------------------------------------------------

only1 :: (HasCallStack, Show a) => Transform [a] -> Transform a
only1 = (=<<) $
  \case
    [x] -> return x
    e -> error $ "[only1]: " ++ show e ++ "is not a singleton"


--------------------------------------------------------------------------------
-- Error Reporting
--------------------------------------------------------------------------------

unknownXError :: (HasCallStack, Show b) => String -> b -> Transform a
unknownXError meta s =
  throwError $ prettyCallStack callStack ++ "\n" ++  meta ++ " `" ++ show s ++ "` is not in the scope"

unknownVariableError :: HasCallStack => Var -> Transform a
unknownVariableError = unknownXError "Variable"

unknownSessionError :: HasCallStack => Session -> Transform a
unknownSessionError = unknownXError "Session"

unknownRangeError :: HasCallStack => Range -> Transform a
unknownRangeError = unknownXError "Range"

handleWith :: Transform a -> Transform (Maybe a) -> Transform a
handleWith err = (>>= maybe err return)

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
