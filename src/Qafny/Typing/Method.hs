module Qafny.Typing.Method where

-- Effects
import           Control.Carrier.Reader
    (runReader)
import           Control.Effect.NonDet
import           Qafny.Effect

-- Qafny
import           Qafny.Interval
import           Qafny.Partial
    (Reducible (reduce))
import           Qafny.Syntax.AST
import           Qafny.Syntax.Emit
    (showEmitI, showEmit0, byLineT, byComma)
import           Qafny.Syntax.EmitBinding
import           Qafny.Syntax.IR
import           Qafny.Utils.Utils
    (errTrace, trd)

import           Qafny.Utils.EmitBinding

-- Utils
import           Control.Carrier.State.Lazy
    (execState, runState)
import           Control.Monad
    (forM, forM_, unless, zipWithM, when)
import           Data.Functor.Identity
import qualified Data.Map.Strict            as Map
import           Data.Maybe
    (catMaybes)
import           Data.Sum
import           Qafny.Typing.Error
    (hdlSCError)
import           Qafny.Typing.Partial
import           Qafny.Typing.Predicates
import           Qafny.Typing.Typing
    (checkTypeEq, extendMetaState'Degree, resolvePartition, splitThenCastScheme,
    typingExp, typingPartitionQTy)
import           Text.Printf
    (printf)
import Data.Foldable (Foldable(toList))


throwError'
  :: ( Has (Error String) sig m )
  => String -> m a
throwError' = throwError @String . ("[Typing/Method] " ++)

--------------------------------------------------------------------------------
-- * Method Typing
--------------------------------------------------------------------------------
-- Generate a method type signature through pre-&post- conditions and the
-- origianl signature following the calling convention.
--
analyzeMethodType
  :: Has (Error String) sig m
  => QMethod () -> m (Var, MethodType)
analyzeMethodType (QMethod v bds rts rqs ens _) = do
  sigRqs <- sigsFromClauses rqs
  sigEns <- sigsFromClauses ens
  let srcParams   = collectRange <$> bds
      srcReturns  = collectRange <$> rts
      instantiate = embedSubst (catMaybes sigRqs)
      receiver    = embedSubst (catMaybes sigEns)
  return (v, MethodType { mtSrcParams=srcParams
                        , mtSrcReturns=srcReturns
                        , mtInstantiate = instantiate
                        , mtReceiver = receiver
                        })
  where
    sigsFromClauses cs = wfSignatureFromPredicate `mapM` cs
    embedSubst sigs r = runIdentity . runReader r $ mapM go sigs

    collectRange :: Binding () -> MethodElem
    collectRange (Binding vq (TQReg a)) = MTyQuantum vq (aexpToExp a)
    collectRange (Binding varg t)       = MTyPure varg t

    go (s, qt, dgr) = (,qt, dgr) <$> instPart s

    -- instantiate a Type expression with a given mapping from variable to Range
    instPart
      :: (Has (Reader (Map.Map Var Range)) sig' m')
      => Partition -> m' Partition
    instPart (Partition rs) = Partition <$> mapM instRange rs

    instRange
      :: ( Has (Reader (Map.Map Var Range)) sig' m' )
      => Range -> m' Range
    instRange rr@(Range x l r) = do
      -- Q: What to do with the right
      rMaybe <- asks (Map.!? x)
      pure $ case rMaybe of
        Just (Range x' l' r') ->
          reduce $ Range x' (reduce (l + l')) (reduce (r + l'))
        Nothing               -> rr

-- | Given an argument, check it against the parameter in the method signature.
-- Note this function doesn't check the entanglement type information.
kindCheckEachParameter
  :: ( Has (Error String) sig m'
     , Has (State (Map.Map Var Range)) sig m'
     , Has (Reader IEnv) sig m'
     , Has (Reader TEnv) sig m'
     )
  => Exp' -> MethodElem -> m' (Maybe Exp')
-- for simple types, check it immediately
kindCheckEachParameter earg (MTyPure v ty) = do
  tyArg <- typingExp earg
  checkTypeEq tyArg ty
  pure (Just earg)
-- for quantum types, collect the qreg correspondence instead
kindCheckEachParameter earg (MTyQuantum v cardinality) = do
  qRange@(Range x el er) <-
    case earg of
      EVar varg -> pure $ Range varg 0 cardinality
      ERange r  -> pure r
      _         -> nonQArgument earg
  -- check if the cardinality is fine
  let eCard :: Exp' = er - el
  -- test if the cadinality is known to be the same as the qreg's size
  eq <- (allI .:) <$> liftIEnv2 (≡)
  unless (eq 0 (er - el - cardinality)) $
    throwError' $ cardinalityMismatch eCard cardinality
  modify (Map.insert v qRange)
  pure Nothing
  where
    nonQArgument arg = throwError' $
      printf "%s is not a valid qreg parameter" (showEmitI 0 arg)
    cardinalityMismatch cardGiven cardReq = fail $
      printf "the cardinality of the qreg passed %s doesn't match the required: %s"
      (showEmitI 0 cardGiven) (showEmitI 0 cardReq)


-- | Partition arguments into quantum and regular ones and produce
--
--   - a map between variable and range represents quantum variable to the
--     actual range used to instantiate
--   - a list of arguments for non-quantum parameters
-- 
-- The function only kind check arguments against the parameters as well as
-- potential range overlappings among those arguments at the call site.
--
normalizeArguments
  :: ( Has (Error String) sig m
     , Has (Reader IEnv) sig m
     , Has (Reader TEnv) sig m
     )
  => [Exp'] -> [MethodElem] -> m (Map.Map Var Range, [Exp'])
normalizeArguments es params = do
  (qmap, pureArgs) <- runState Map.empty $
    catMaybes <$> zipWithM kindCheckEachParameter es params
  let rs = Map.elems qmap
  isBot' <- (all (== Just True) .) <$> isBotI
  let hasDuplication = checkRangeDuplication isBot' rs
  when hasDuplication $
    throwError' (errNonLinear rs) 
  return (qmap, pureArgs)
  where
    errNonLinear rs = printf
      "Nonlinear usage of quantum resources in ranges:\n%s"
      (showEmit0 (byLineT rs))

-- | Given an inclusion operator, check if there's a nonlinear usage of ranges.
checkRangeDuplication :: (Range -> Bool) -> [Range] -> Bool
checkRangeDuplication isBot' = go
  where
    go [] = False
    go (x : xs) = any (cmp x) xs || go xs
    cmp r1 r2 = maybe False isBot' (r1 ⊓ r2) 


-- | Take in a list of arguments, check against the method signature and resolve
-- arguments to be emitted w.r.t. the calling convention.
-- 
-- This function check not only kind information as well as entanglement types.
--
-- Return a map from QVars to ranges passed, arguments to be emitted, and passed
-- Loci in the caller's context.
resolveMethodApplicationArgs
  ::  ( Has (Gensym String) sig m
      , Has (Gensym Emitter) sig m
      , Has (Error String) sig m
      , Has (Reader TEnv) sig m
      , Has (Reader IEnv) sig m
      , Has (State TState) sig m
      , Has Trace sig m
      )
  => [Exp']
  -> MethodType
  -> m ( Map.Map Var Range -- parameter -> range mapping
       , [Exp']            -- pure args
       , [Exp']            -- quantum args
       , [(Maybe SplitScheme, Maybe CastScheme)])
resolveMethodApplicationArgs es
  MethodType { mtSrcParams=srcParams
             , mtInstantiate=instantiator
             } = errTrace "`resolveMethodApplicationArgs`" $ do
  unless (length es == length srcParams) $
    arityMismatch srcParams
  (qArgMap, pureArgs) <- normalizeArguments es srcParams
  let inst = instantiator qArgMap -- instantiated partition, qty, and degree
  -- perform qtype check for each argument
  (qArgs, schemes) <- resolveInstantiatedQuantumArgs inst
  pure (qArgMap, pureArgs, qArgs, schemes)
  where
    arityMismatch prs = throwError' $
      "The number of arguments given doesn't match the number of parameters expected by the method."
      ++ printf "Given:\n%s\nExpected:\n%s" (show es) (show prs)

-- | Given an list of instantiated entanglement types, perform splits and casts
-- and return a list of extracted representations as well as split and cast
-- schemes requires to do so.
--
-- For any instantiation of the same instantiator, the order is guaranteed to be
-- the same.
resolveInstantiatedQuantumArgs
  :: ( HasResolution sig m
     , GensymMeta sig m
     , GensymEmitterWithState sig m
     )
  => [(Partition, QTy, Maybe Int)]
  -> m ([Exp'], [(Maybe SplitScheme, Maybe CastScheme)])
resolveInstantiatedQuantumArgs insts = do
  locusAndSchemes <- mapM go insts
  let (loci, schemes) = unzip $ regroup <$> locusAndSchemes
  unless (and (zipWith checkPhase loci insts)) $
    errDegreeMismatch loci
  emits <- mapM extractEmitablesFromLocus loci
  return (EVar <$> fsts (concat emits), schemes)
  where
    regroup (a, b, c) = (a, (b, c))

    -- | type cast and type checks 
    go (p@(Partition [r]), q, degreeM)  = do
      -- cast is only feasible for singleton partitions
      st <- resolvePartition p
      hdlSCError $ splitThenCastScheme st q r
    go (p, q, degreeM) =
      -- use `typingPartitionQTy` to make sure the partition is exact!
      (, Nothing, Nothing) <$> typingPartitionQTy p q
  
    -- | phase type checks
    checkPhase Locus{degrees} (_, _, methodDegree) =
      toList methodDegree == degrees

    errDegreeMismatch loci = throwError' $
      printf "Degree mismatch:\n%s\n%s"
      (byComma (degrees <$> loci))
      (byComma (trd <$> insts))

-- | Compute the typing state after returning from a method call.
resolveMethodApplicationRets
  ::  ( Has (Error String) sig m
      , Has (State TState) sig m
      , Has (Gensym Var) sig m
      , Has (Gensym Emitter) sig m
      , Has Trace sig m
      )
  => Map.Map Var Range -> MethodType ->  m [(Var, Ty)]
resolveMethodApplicationRets envArgs
  MethodType { mtSrcReturns=retParams
             , mtReceiver=receiver
             } = do
  trace "* resolveMethodApplicationRets"
  qBindings <- concat <$> forM psRet ((fst <$>) . extendMetaState'Degree)
  --TODO: also outputs pure variables here
  -- Sanity check for now:
  let pureArgs = collectPureBindings retParams
  unless (null pureArgs) unimpl
  return qBindings
  where
    unimpl = throwError' "Unimplemented: method returns a pure value."
    -- partitions after the method call
    psRet = receiver envArgs



-- Collect all pure variables
collectPureBindings :: [MethodElem] -> [Binding']
collectPureBindings params =  [ Binding v t | MTyPure v t <- params ]

-- Compute types of methods from the toplevel
collectMethodTypes
  :: (Has (Error String) sig m)
  => AST  -> m (Map.Map Var MethodType)
collectMethodTypes a = execState @(Map.Map Var MethodType) Map.empty $
  forM_ a go
  where
    go :: ( Has (Error String) sig m'
          , Has (State (Map.Map Var MethodType)) sig m'
          )
       => Toplevel () -> m' ()
    go (Toplevel (Inl q@(QMethod {}))) = do
      let (idMethod, methodTy) = analyzeMethodType q
      existsMaybe <- (Map.!? idMethod) <$> get @(Map.Map Var MethodType)
      case existsMaybe of
        Just _ ->
          throwError' $ printf "Duplicated definitions of the method %s." idMethod
        _ -> modify (Map.insert idMethod methodTy)
    go _ = pure ()