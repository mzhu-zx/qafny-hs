{-# LANGUAGE
    ScopedTypeVariables
  , TypeApplications
  , TupleSections
  #-}
module Qafny.Utils where

--
import           Control.Carrier.State.Church (State)
import           Control.Effect.Error         (Error, throwError)
import           Control.Effect.Lens
import           Control.Effect.Reader
import           Control.Effect.State
import           Control.Lens                 (at, (?~), (^.))

--
import           Effect.Gensym                (Gensym, gensym)

--
import           Control.Effect.Trace
import           Control.Monad                (forM)
import           Data.Functor                 ((<&>))
import qualified Data.Map.Strict              as Map
import qualified Data.Set                     as Set
import           Data.Sum
import           Qafny.Env                    (TEnv, TState, emitSt, kEnv, sSt)
import           Qafny.Error                  (QError (UnknownVariableError))
import           Qafny.Partial                (Reducible (reduce))
import           Qafny.Syntax.AST
import           Qafny.Syntax.Emit            (showEmitI)
import           Qafny.TypeUtils              (typingQEmit)
import           Qafny.Variable               (Variable (variable))
import           Text.Printf                  (printf)

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
-- symbol state and the __Gensym RBinding__ effect.
-- $doc
--------------------------------------------------------------------------------
rbindingOfRangeQTy :: Range -> QTy -> RBinding
rbindingOfRangeQTy r qty = RBinding (reduce r, typingQEmit qty)


-- | Generate a varaible from a 'Range' and its 'QTy' and add the corresponding
-- 'Binding' into 'emitSt'
gensymEmitRangeQTy
  :: ( Has (Gensym RBinding) sig m
     , Has (State TState) sig m
     )
  => Range -> QTy-> m Var
gensymEmitRangeQTy r qty = gensymEmitRB (rbindingOfRangeQTy r qty)

gensymEmitRB
  :: ( Has (Gensym RBinding) sig m
     , Has (State TState) sig m
     )
  => RBinding -> m Var
gensymEmitRB rb = do
  name <- gensym rb
  emitSt %= (at rb ?~ name)
  return name

-- | Similar to 'gensymEmitRangeQTy' but gensym without adding it the 'emitSt'
gensymRangeQTy
  :: ( Has (Gensym RBinding) sig m
     )
  => Range -> QTy -> m Var
gensymRangeQTy r qty =
  gensym $ rbindingOfRangeQTy r qty

gensymEmitPartitionQTy 
  :: ( Has (Gensym RBinding) sig m
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
  let rb = rbindingOfRangeQTy r qty
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
  let rb = rbindingOfRangeQTy r qty
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
  let bs = uncurry rbindingOfRangeQTy <$> rqts
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
