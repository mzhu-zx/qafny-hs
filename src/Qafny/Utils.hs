{-# LANGUAGE
    TypeApplications
  #-}
module Qafny.Utils where

--
import           Control.Carrier.State.Church (State)
import           Control.Effect.Error         (Error, Has, throwError)
import           Control.Effect.Lens
import           Control.Lens                 (at, (?~), (^.))

--
import           Effect.Gensym                (Gensym, gensym)

--
import qualified Data.Map.Strict              as Map
import qualified Data.Set                     as Set
import           Qafny.AST
import           Qafny.Env                    (TState, emitSt)
import           Qafny.TypeUtils              (typingQEmit)
import           Qafny.Variable               (Variable (variable))
import           Text.Printf                  (printf)


-- catchMaybe
--   :: Has (Error e) sig m
--   => m (Maybe a)
--   -> m a
--   -> m a
-- catchMaybe mayFail fail' =
--   mayFail >>= maybe fail' return

throwError'
  :: ( Has (Error String) sig m )
  => String -> m a
throwError' = throwError @String

-- | Catch the error in the Maybe and rethrow it as an Error
rethrowMaybe
  :: ( Has (Error String) sig m )
  => m (Maybe a)
  -> String
  -> m a
rethrowMaybe mayFail err =
  mayFail >>= maybe (throwError' err) return


gensymLoc
  :: ( Has (Gensym String) sig m )
  => String -> m Loc
gensymLoc = (Loc <$>) . gensym . variable . Loc

-- | Generate a new symbol for emit variable and add it to emitSt
-- gensymEmit
--   :: ( Has (Gensym RBinding) sig m
--      , Has (State TState) sig m
--      )
--   => Binding -> m String
-- gensymEmit b = do
--   name <- gensym b
--   emitSt %= (at b ?~ name)
--   return name



-- TODO: Binding can cause aliasing, Var is not sufficient, I need to define
-- `RBinding = (Range, Ty)` to avoid aliasing!
-- | Lookup for emitted symbols in emitSt
-- findEmitSym
--   :: ( Has (State TState) sig m
--      , Has (Error String) sig m
--      )
--   => Binding -> m String
-- findEmitSym b = do
--   st <- use emitSt
--   rethrowMaybe
--     (return (st ^. at b)) $
--     printf "the binding `%s` cannot be found in the renaming state.\n%s"
--       (show b)
--       (show st)

-- -- | Remove bindings from emitSt
-- removeEmitBindings
--   :: ( Has (State TState) sig m)
--   => [Binding] -> m ()
-- removeEmitBindings bs = do
--   emitSt %= (`Map.withoutKeys` Set.fromList bs)

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
rbindingOfRangeQTy r qty = RBinding (r, typingQEmit qty)

-- | Generate a varaible from a 'Range' and its 'QTy' and add the corresponding
-- 'Binding' into 'emitSt'   
gensymEmitRangeQTy
  :: ( Has (Gensym RBinding) sig m
     , Has (State TState) sig m
     )
  => Range -> QTy-> m Var
gensymEmitRangeQTy r qty = do
  let rb = rbindingOfRangeQTy r qty
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

findEmitRangeQTy
  :: ( Has (State TState) sig m
     , Has (Error String) sig m
     )
  => Range -> QTy -> m String
findEmitRangeQTy r qty = do
  let rb = rbindingOfRangeQTy r qty
  st <- use emitSt
  rethrowMaybe
    (return (st ^. at rb)) $
    printf "the binding `%s` cannot be found in the renaming state.\n%s"
      (show rb)
      (show st)

  -- findEmitSym $ rbindingOfRangeQTy r qty

removeEmitRangeQTys
  :: ( Has (State TState) sig m)
  => [(Range, QTy)] -> m ()
removeEmitRangeQTys rqts = do
  let bs = uncurry rbindingOfRangeQTy <$> rqts
  emitSt %= (`Map.withoutKeys` Set.fromList bs)

--------------------------------------------------------------------------------

exp2AExp
  :: (Has (Error String) sig m)
  => Exp -> m AExp
exp2AExp (EVar v) = return $ AVar v
exp2AExp (ENum n) = return $ ANat n
exp2AExp e = throwError @String $
  printf "%s cannot be projected to an AExp." (show e)

