{-# LANGUAGE
    ScopedTypeVariables
  , TupleSections
  , TypeApplications
  , TypeOperators
  #-}
module Qafny.Utils where

--
import           Control.Effect.Error  (Error, throwError)
import           Control.Effect.Lens
import           Control.Effect.Reader
import           Control.Effect.State
import           Control.Effect.Trace
import           Control.Lens          (at, (?~), (^.))
import           Control.Monad         (forM)

import           Data.Bifunctor        (bimap, second)
import           Data.Functor          ((<&>))
import qualified Data.Map.Strict       as Map
import qualified Data.Set              as Set
import           Data.Sum
import           Text.Printf           (printf)

--
import           Effect.Gensym         (Gensym, gensym)

--
import           Data.Maybe            (catMaybes, mapMaybe)
import           Qafny.Env             (TEnv, TState, emitSt, kEnv, sSt)
import           Qafny.Error           (QError (UnknownVariableError))
import           Qafny.Partial         (Reducible (reduce))
import           Qafny.Syntax.AST
import           Qafny.Syntax.Emit     (showEmitI)
import           Qafny.TypeUtils       (typingPhaseEmit, typingQEmit)
import           Qafny.Variable        (Variable (variable))


--------------------------------------------------------------------------------
-- * 3-Tuples
uncurry3 ::  (a -> b -> c -> d) -> (a, b, c) -> d
uncurry3 f (a, b, c) = f a b c

fst2 :: (a, b, c) -> (a, b)
fst2 (a, b, c) = (a, b)

--------------------------------------------------------------------------------

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
rbindingOfRange :: Range -> QTy :+: PhaseTy :+: Ty -> EmitBinding
rbindingOfRange r b = RBinding (reduce r, b)


gensymBase
  :: ( Has (Gensym EmitBinding) sig m )
  => Range -> m Var
gensymBase r = gensym $ rbindingOfRange r (inj TNat)

-- rbindingOfRangeQTy :: Range -> QTy -> EmitBinding
-- rbindingOfRangeQTy r qty = RBinding (reduce r, inj qty)

-- rbindingOfRangePTyRepr :: Range -> PhaseTy -> Maybe EmitBinding
-- rbindingOfRangePTyRepr r pty =
--   pty <&> RBinding . (reduce r, ) . snd
-- | Generate a varaible from a 'Range' and its 'QTy' and add the corresponding
-- 'Binding' into 'emitSt'
gensymEmitRangeQTy
  :: ( Has (Gensym EmitBinding) sig m
     , Has (State TState) sig m
     )
  => Range -> QTy-> m Var
gensymEmitRangeQTy r qty = gensymEmitRB (rbindingOfRange r (inj qty))

-- | Generate a new variable for phase representation and returns a new PhaseTy
-- that refers to the new variable.
gensymEmitRangePTyRepr
  :: ( Has (Gensym EmitBinding) sig m
     , Has (State TState) sig m
     )
  => Range -> PhaseTy-> m (Maybe Var, PhaseTy)
gensymEmitRangePTyRepr _ PT0 = pure (Nothing, PT0)
gensymEmitRangePTyRepr r t@(PTN i pRef) = do
  vRepr <- gensymEmitRB (rbindingOfRange r (inj t))
  return (Just vRepr, PTN i pRef{ prRepr=vRepr })


gensymEmitRangePTy
  :: ( Has (Gensym EmitBinding) sig m
     , Has (State TState) sig m
     )
  => Range -> PhaseTy-> m (Maybe (Var, Var))
gensymEmitRangePTy r =
  undefined


gensymEmitRB
  :: ( Has (Gensym EmitBinding) sig m
     , Has (State TState) sig m
     )
  => EmitBinding -> m Var
gensymEmitRB rb = do
  name <- gensym rb
  emitSt %= (at rb ?~ name)
  return name

-- | Similar to 'gensymEmitRangeQTy' but gensym without adding it the 'emitSt'
gensymRangeQTy
  :: ( Has (Gensym EmitBinding) sig m
     )
  => Range -> QTy -> m Var
gensymRangeQTy r qty =
  gensym $ rbindingOfRange r (inj qty)

gensymEmitPartitionQTy
  :: ( Has (Gensym EmitBinding) sig m
     , Has (State TState) sig m
     )
  => Partition -> QTy -> m [Var]
gensymEmitPartitionQTy p qty =
  forM (unpackPart p) (`gensymEmitRangeQTy` qty)

liftPartition :: Monad m => (Range -> m b) -> Partition -> m [b]
liftPartition f p = forM (unpackPart p) f

findEmitRangeQTy
  :: ( Has (State TState) sig m
     , Has (Error String) sig m
     )
  => Range -> QTy -> m Var
findEmitRangeQTy r qty = do
  let rb = rbindingOfRange r (inj qty)
  st <- use emitSt
  rethrowMaybe
    (return (st ^. at rb)) $
    printf "the binding `%s` cannot be found in the renaming state.\n%s"
      (show rb)
      (show st)

findEmitBindingsFromPartition
  :: ( Has (State TState) sig m
     , Has (Error String) sig m
     )
  => Partition -> QTy -> m [Binding']
findEmitBindingsFromPartition part q =
  forM (unpackPart part) $ (uncurry Binding . (, typingQEmit q) <$>) . (`findEmitRangeQTy` q)


findEmitVarsFromPartition
  :: ( Has (State TState) sig m
     , Has (Error String) sig m
     )
  => Partition -> QTy -> m [Var]
findEmitVarsFromPartition part q =
  forM (unpackPart part) $ (`findEmitRangeQTy` q)



modifyEmitRangeQTy
  :: ( Has (State TState) sig m )
  => Range -> QTy -> Var -> m ()
modifyEmitRangeQTy r qty name = do
  let rb = rbindingOfRange r (inj qty)
  emitSt %= (at rb ?~ name)


removeEmitPartitionQTys
  :: ( Has (State TState) sig m)
  => Partition -> QTy -> m ()
removeEmitPartitionQTys p qty = do
  removeEmitRangeQTys ((, qty) <$> unpackPart p)

removeEmitRangeQTys
  :: ( Has (State TState) sig m)
  => [(Range, QTy)] -> m ()
removeEmitRangeQTys rqts = do
  let bs = uncurry rbindingOfRange <$> (rqts <&> second inj)
  emitSt %= (`Map.withoutKeys` Set.fromList bs)

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

--------------------------------------------------------------------------------
-- * EmitBinding Related

projEmitBindingRangeQTy :: EmitBinding -> Maybe (Range, QTy)
projEmitBindingRangeQTy (RBinding (r, Inl (Inl qty))) = Just (r, qty)
projEmitBindingRangeQTy _                             = Nothing

collectRQTyBindings ::[(EmitBinding, Var)] -> [((Range, QTy), Var)]
collectRQTyBindings = mapMaybe (\(e, v) -> projEmitBindingRangeQTy e <&> (, v))
