{-# LANGUAGE
    ScopedTypeVariables
  , TupleSections
  , TypeApplications
  , TypeOperators
  #-}
module Qafny.Utils.Utils where

--
import           Control.Effect.Error
    (Error, catchError, throwError)
import           Control.Effect.Lens
import           Control.Effect.Reader
import           Control.Effect.State
import           Control.Effect.Trace
import           Control.Lens
    (at, (?~), (^.))
import           Control.Monad
    (forM, join, unless)

import           Data.Bifunctor
import           Data.Sum
import           Text.Printf
    (PrintfType, printf)

--
import           Effect.Gensym
    (Gensym, gensym)

--
import           Control.Applicative
    (Applicative (liftA2))
import           Qafny.Error
    (QError (UnknownVariableError))
import           Qafny.Syntax.AST
import           Qafny.Syntax.Emit
    (showEmitI)
import           Qafny.Syntax.IR
import           Qafny.Variable
    (Variable (variable))


--------------------------------------------------------------------------------
-- * 3-Tuples
uncurry3 ::  (a -> b -> c -> d) -> (a, b, c) -> d
uncurry3 f (a, b, c) = f a b c

fst2 :: (a, b, c) -> (a, b)
fst2 (a, b, c) = (a, b)

internalError :: a
internalError = error "Internal Error!"

trd :: (a, b, c) -> c
trd (_, _, c) = c
--------------------------------------------------------------------------------

onlyOne
  :: ( Has (Error String) sig m
     , Show a
     )
  => (String -> m a) -> [a] -> m a
onlyOne throw v =
  case v of
    [v'] -> return v'
    _    -> throw $ printf "Expecting only one element, but given: %s!" (show v)


throwError''
  :: ( Has (Error String) sig m )
  => String -> m a
throwError'' = throwError @String

-- | Catch the error in the Maybe and rethrow it as an Error
rethrowMaybe
  :: ( Has (Error String) sig m )
  => m (Maybe a)
  -> String
  -> m a
rethrowMaybe mayFail err =
  mayFail >>= maybe (throwError'' err) return


gensymLoc
  :: ( Has (Gensym String) sig m )
  => String -> m Loc
gensymLoc = (Loc <$>) . gensym . variable . Loc

--------------------------------------------------------------------------------
-- * Gensym Utils
--
-- $doc
-- The following functions operate on a 'Range' and a 'QTy', form a `Binding` to
-- be normalized to a variable name, perform modification and query to the emit
-- symbol state and the __Gensym EmitBinding__ effect.
-- $doc
--------------------------------------------------------------------------------

-- gensymBase
--   :: ( Has (Gensym EmitBinding) sig m )
--   => Range -> Int -> m Var
-- gensymBase r i = gensym $ rbindingOfRange r (inj i)

-- rbindingOfRangeQTy :: Range -> QTy -> EmitBinding
-- rbindingOfRangeQTy r qty = RBinding (reduce r, inj qty)

-- rbindingOfRangePTyRepr :: Range -> PhaseTy -> Maybe EmitBinding
-- rbindingOfRangePTyRepr r pty =
--   pty <&> RBinding . (reduce r, ) . snd



--------------------------------------------------------------------------------
exp2AExp
  :: (Has (Error String) sig m)
  => Exp' -> m AExp
exp2AExp (EVar v) = return $ AVar v
exp2AExp (ENum n) = return $ ANat n
exp2AExp e = throwError @String $
  printf "%s cannot be projected to an AExp." (show e)

dumpSt
  :: ( Has (State TState) sig m
     , Has Trace sig m
     )
  => String -> m ()
dumpSt str = do
  s <- get @TState
  trace $ printf "[info] The state after (%s) is:\n%s" str (show s)

dumpSSt
  :: ( Has (State TState) sig m
     , Has Trace sig m
     )
  => String -> m ()
dumpSSt str = do
  s <- use sSt
  trace $ printf "[info] Dumped sSt (%s):%s" str (show s)

--------------------------------------------------------------------------------
-- * Method Types

-- | Retrive the type of the given formal variable from the environment
getMethodType
  :: ( Has (Error String) sig m
     , Has (Reader TEnv) sig m
     )
  => Var -> m MethodType
getMethodType v = do
  tyM :: Maybe MTy  <- asks (^. kEnv . at v)
  case tyM of
    Just mty ->
      case unMTy mty of
        Inl ty -> throwError'' $ printf "%s is not a method but a %s" v (showEmitI 0 ty)
        Inr mty -> pure mty
    _             -> asks (^. kEnv) >>= throwError'' . show . UnknownVariableError v

haveSameLength
  :: ( Has (Error String) sig m
     , Show a
     , Show b
     )
  => [a] -> [b] -> m ()
haveSameLength vsEmit eValues =
  unless (length vsEmit == length eValues) $
    throwError @String $ printf
      "the number of elements doesn't agree with each other: %s %s"
      (show vsEmit) (show eValues)

--------------------------------------------------------------------------------
-- | Catch error and add information to it
errTrace :: (Has (Error String) sig m) => String -> m a ->  m a
errTrace info m =
  catchError m (\e -> throwError (e ++ "\n↑ " ++ info))


-- * Pure functions 

both :: Bifunctor f => (a -> b) -> f a a -> f b b
both = join bimap

bothM :: Applicative m => (a -> m b) -> (a, a) -> m (b, b)
bothM f (a, b) = liftA2 (,) (f a) (f b)

hasNoDup :: Eq a => [a] -> Bool
hasNoDup [] = True
hasNoDup (x:xs) = foldr go True xs
  where
    go x' ans = x == x' && ans
