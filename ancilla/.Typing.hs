{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE TupleSections #-}

module Qafny.Typing where

import           Qafny.AST
import           Qafny.Env
import           Control.Lens
import           Control.Monad.RWS
import           Control.Monad.Except
import qualified Data.Map.Strict as Map 
import qualified Data.Set as Set 
import qualified Data.List as List

--------------------------------------------------------------------------------
-- | Helpers 
--------------------------------------------------------------------------------
-- Compute types of methods from the toplevel
collectMethodTypes :: AST -> [(Var, Ty)]
collectMethodTypes a = [ (idt, TMethod (bdTypes ins) (bdTypes outs))
                       | QMethod idt ins outs _ _ _ <- a]

collectMethodTypesM :: AST -> Map.Map Var Ty
collectMethodTypesM = Map.fromList . collectMethodTypes

appkEnvWithBds :: Bindings -> TEnv -> TEnv
appkEnvWithBds bds = kEnv %~ appBds
  where appBds = Map.union $ Map.fromList [(v, t) | Binding v t <- bds]

bdTypes :: Bindings -> [Ty]
bdTypes b = [t | Binding _ t <- b]

sub :: Ty -> Ty -> Bool
sub = (==)

checkSubtype :: Ty -> Ty -> Env ()
checkSubtype t1 t2 =
  unless (sub t1 t2) $
  throwError $
  "Type mismatch: `" ++ show t1 ++ "` is not a subtype of `" ++ show t2 ++ "`"

-- TODO: make `sub` a typeclass?
subQ :: QTy -> QTy -> Bool
subQ _    TCH  = True
subQ THad THad = True
subQ TNor TNor = True
subQ _     _   = False
  
checkSubtype2 :: (Ty, Ty, Ty) -> Ty -> Ty -> Env Ty
checkSubtype2 (top1, top2, tret) t1 t2 =
  do checkSubtype top1 t1
     checkSubtype top2 t2
     return tret

checkSubtypeQ :: QTy -> QTy -> Env ()
checkSubtypeQ t1 t2 =
  unless (subQ t1 t2) $
  throwError $
  "Type mismatch: `" ++ show t1 ++ "` is not a subtype of `" ++ show t2 ++ "`"

--------------------------------------------------------------------------------
-- | Typing 
--------------------------------------------------------------------------------
class Typing a t where
  typing :: a -> Env t

-- | resolve the typing of a coarse partition
instance Typing Partition QTy where
  typing se@(Partition s) = resolvePartition se >>= getPartitionType

instance Typing Exp Ty where
  typing (ENum _)  = return TNat
  typing (EVar x)  =
    handleWith (unknownVariableError x) $ use (kSt . at x)
  typing (EOp2 op2 e1 e2) =
    do top <- typing op2
       t1 <- typing e1
       t2 <- typing e2
       checkSubtype2 top t1 t2 
  typing e = throwError $ "Typing for "  ++ show e ++ " is unimplemented!"

instance Typing Op2 (Ty, Ty, Ty) where
  typing OAnd = return (TBool, TBool, TBool)
  typing OOr = return (TBool, TBool, TBool)
  -- We might need to solve the issue of nat vs int 0
  typing OAdd = return (TNat, TNat, TNat) 
  typing OMod = return (TNat, TNat, TNat) 
  typing OMul = return (TNat, TNat, TNat)
  typing ONor = return (TNat, TNat, TQ TNor)
  typing OLt  = return (TNat, TNat, TBool)
  typing OLe  = return (TNat, TNat, TBool)


instance Typing QTy [Ty] where
  typing TNor = return [TSeq TNat]
  typing THad = return [TSeq TNat]
  typing TCH  = return [TSeq TNat]


-- | Gather partitions used in the guard
typingGuard :: Exp -> Env (Partition, QTy)
typingGuard (EPartition s') = 
  do 
    s <- resolvePartition s'
    handleWith (unknownPartitionError s) (uses (sSt . at s) ((s, ) <$>))
typingGuard e = throwError $ "Unsupported guard: " ++ show e

-- | Find the type of the emitted term
typingEmit :: Partition -> Env [Ty]
typingEmit s = (typing s :: Env QTy) >>= typing

-- | Find the emitted symbol by the range name and quantum type
-- TODO: this should probably be refactored to return a list of symbols
findSymByRangeQTy :: Range -> QTy -> Env Var
findSymByRangeQTy (Range v _ _) qt = only1 (typing qt) >>= findSym v

-- | Dealloc an orphan variable
deallocOrphan :: Var -> Ty -> Env ()
deallocOrphan vMeta tyEmit =
  rbSt %= (`Map.withoutKeys` Set.singleton (vMeta, tyEmit))
    

-- | Change the type of a partition and returns something
-- retyping doesn't emit a new partition symbol 
retypePartition :: Partition -> QTy -> Env ([Var], Ty, [Var], Ty)
retypePartition s qtNow =
  do
    qtPrev <- typing s
    when (qtNow == qtPrev) $
      throwError $
        "Partition `" ++ show s ++ "` is of type `" ++ show qtNow ++ "`. No retyping can be done."
    let vMetas = varFromPartition s
    tOldEmit <- only1 $ typing qtPrev
    vOldEmits <- mapM (`findSym` tOldEmit) vMetas
    -- update states
    -- update with new ones
    sSt %= (at s ?~ qtNow)
    -- update the kind state for each (probably not necessary)
    foldM_ (\_ v -> kSt %= (at v ?~ TQ qtNow)) () vMetas
    rbSt %= (`Map.withoutKeys` (Set.fromList $ map (,tOldEmit) vMetas))
    tNewEmit <- only1 $ typing qtNow
    vNewEmits <- mapM (`gensym` tNewEmit) vMetas
    return (vOldEmits, tOldEmit, vNewEmits, tOldEmit)

retypePartition1 :: Partition -> QTy -> Env (Var, Ty, Var, Ty)
retypePartition1 s qtNow =
  do
    qtPrev <- typing s
    when (qtNow == qtPrev) $
      throwError $
        "Partition `" ++ show s ++ "` is of type `" ++ show qtNow ++ "`. No retyping can be done."
    vMeta <- only1 $ return $ varFromPartition s
    tOldEmit <- only1 $ typing qtPrev
    vOldEmit <- vMeta `findSym` tOldEmit
    -- update states
    -- update with new ones
    sSt %= (at s ?~ qtNow)
    -- update the kind state for each (probably not necessary)
    kSt %= (at vMeta ?~ TQ qtNow)
    rbSt %= (`Map.withoutKeys` Set.singleton (vMeta ,tOldEmit))
    tNewEmit <- only1 $ typing qtNow
    vNewEmit <- vMeta `gensym` tNewEmit
    return (vOldEmit, tOldEmit, vNewEmit, tOldEmit)

-- | Merge two partitions and update the typing state
mergePartitionType :: Partition -> Partition -> Env ()
mergePartitionType sMain@(Partition rsMain) sAux@(Partition rsAux) =
  do
    qtMain <- handleWith (unknownPartitionError sMain) $ use (sSt . at sMain)
    qtAux <- handleWith (unknownPartitionError sAux) $ use (sSt . at sAux)
    unless (qtMain == qtAux && qtAux == TCH) $
      throwError $
        "Partition `"
          ++ show sMain
          ++ "` and partition `"
          ++ show sAux
          ++ "` are of type `"
          ++ show qtMain
          ++ "` and `"
          ++ show qtAux
          ++ "`, which are not CH."
    -- start merge
    let newPartition = Partition $ rsMain ++ rsAux
    let vMetasMain = varFromPartition sMain 
    let vMetasAux =  varFromPartition sAux
    let refNewMain = Map.fromList $ (, newPartition) <$> vMetasMain 
    let refNewAux  = Map.fromList $ (, newPartition) <$> vMetasAux 
    -- update range reference 
    xSt %= ((refNewMain `Map.union` refNewAux) `Map.union`)
    -- update partition type state
    sSt %= (`Map.withoutKeys` Set.fromList [sMain, sAux])
    sSt %= (at newPartition ?~ TCH)
    -- surprisingly, I don't need to change the rest
    -- TODO: what should I return to avoid computation?
    return ()


-- | Resolve partition: compute the super partition of one partition
resolvePartition :: Partition -> Env Partition
resolvePartition se@(Partition rs) =
    do
      sesRange <-
        (`mapM` rs)
          ( \r@(Range name _ _) ->
              handleWith (unknownRangeError r) $ use (xSt . at name)
          )
      case List.nub sesRange of
        [] -> throwError "Internal Error? An empty partition has no type!"
        [x] -> return x
        ss ->
          throwError $
            "`"
              ++ show se
              ++ "` is not a sub-partition, counterexample: "
              ++ show ss

-- | Resolve partition: compute the super partition of several partitions
resolvePartitions :: [Partition] -> Env Partition
resolvePartitions =
  resolvePartition . Partition . concatMap (\(Partition rs) -> rs)

-- | Compute the quantum type of a partition
getPartitionType :: Partition -> Env QTy
getPartitionType s =
  handleWith
    ( throwError $
        "Internal Error? Partition`"
          ++ show s
          ++ "` is not in the type state"
    )
    $ use (sSt . at s)

-- | Assemble the partition from a partition from the guard and the upper and the
-- lower bound of the loop and emit a check
-- Precondition: Split has been performed at the subtyping stage so that it's
-- guaranteed that only one range can be in the partition
-- Reason: (was from `augByGuardType`)
--   `sGuard` is likely to be in `x [i .. i + 1]` form,
--   there should be a around of resolution that resolves to the partition
--   `x[l .. h]` and do the emission at that place 
loopPartition :: Partition -> Exp -> Exp -> Env (Partition, Exp)
loopPartition (Partition [Range r sl sh]) l h =
  return
    ( Partition [Range r l h]
    , EEmit (EOpChained l [(OLe, sl), (OLt, sh), (OLe, h)])
    )
loopPartition s _ _ =
  throwError $
    "Partition `"
      ++ show s
      ++ "` contains more than 1 range, this should be resolved at the typing stage"
