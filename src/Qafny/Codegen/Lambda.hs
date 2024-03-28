{-# LANGUAGE
    NamedFieldPuns
  , TypeApplications
  , TypeFamilies
  #-}

module Qafny.Codegen.Lambda(codegenUnaryLambda, codegenLambdaEntangle) where

import           Control.Algebra
    (Has)
import           Control.Effect.Error
    (Error, throwError)
import           Control.Effect.Reader
    (Reader)
import           Control.Effect.Trace
    (Trace, trace)
import           Control.Exception
    (assert)
import           Control.Monad
    (unless)
import           Effect.Gensym
    (Gensym)
import           Qafny.Codegen.Phase
    (codegenPhaseLambda, codegenPromotion)
import           Qafny.Codegen.SplitCast
    (codegenSplitThenCastEmit)
import           Qafny.Codegen.Utils
    (putOpt)
import           Qafny.Effect
    (GensymEmitterWithStateError)
import           Qafny.Syntax.AST
import           Qafny.Syntax.ASTFactory
import           Qafny.Syntax.IR
import           Qafny.Typing
    (promotionScheme, resolvePartition', splitThenCastScheme)
import           Qafny.Typing.Error
import           Qafny.Utils
    (findEmitBasesByRanges, findEmitBasisByRange, gensymBinding, fsts)


throwError'
  :: ( Has (Error String) sig m )
  => String -> m a
throwError' = throwError @String . ("[Codegen|Lambda] " ++)

--------------------------------------------------------------------------------

-- | Apply the oracle function to the singleton partition on the LHS.
-- The range in the partition may be a sub-range of the resolved one.
-- When the entanglement type permits, a split is inserted.
codegenUnaryLambda
  :: ( Has (Gensym String) sig m
     , GensymEmitterWithStateError sig m
     , Has (Reader IEnv) sig m
     , Has (Reader Bool) sig m
     , Has Trace sig m
     )
  => Range -> Range -> Locus -> QTy -> Lambda -> m [Stmt']
codegenUnaryLambda rLhs rResolved locus qtLambda
  lam@LambdaF{ePhase, bPhase, eBases, bBases} = do
  -- do the type cast and split first
  (stS@Locus{qty=qt}, maySplit, mayCast) <-
    hdlSCError $ splitThenCastScheme locus qtLambda rLhs
  stmts <- codegenSplitThenCastEmit maySplit mayCast

  -- resolve again for consistency, debugging only
  dbgAssertConsistency rLhs stS

  -- handle promotions in phases
  stmtsPhase <- do
    promoteMaybe <- promotionScheme stS bPhase ePhase
    case promoteMaybe of
      Just promote -> codegenPromotion promote
      Nothing      -> codegenPhaseLambda stS bPhase ePhase

  -- after promotion, the locus queried before must be staled
  -- dbgAssertConsistency rLhs stS


  -- | It's important not to use the fully resolved `s` here because the OP
  -- should only be applied to the sub-partition specified in the annotation.
  (vEmit, _) <- findEmitBasisByRange rLhs
  ((stmts ++) . (stmtsPhase ++) <$>) . putOpt $ case qtLambda of
    TEn -> return [ vEmit ::=: callMap lamSansPhase vEmit ]
    TEn01 -> do
      -- for example, we have
      --  - rLhs x[3 .. 6]
      --  - rRsv x[2 .. 8]
      -- then,
      --  - offset = 1
      --  - elFrom0 = offset
      --  - erFrom0 = eLhsUpper-eLhsLower + offset
      --            = 6 - 3 + 1 = 4
      (vInner, _) <- gensymBinding "i" TNat
      return $
        let offset = eLhsLower - eRsvLower
            (elFrom0, erFrom0) = (offset, offset + eLhsUpper-eLhsLower)
            lambda = lambdaSplit vInner elFrom0 erFrom0
        in  [ vEmit ::=: callMap lambda vEmit ]
    TNor -> return $
      let offset = eLhsLower - eRsvLower
          (elFrom0, erFrom0) = (offset, offset + eLhsUpper-eLhsLower)
      in [ vEmit ::=: bodyOnly vEmit elFrom0 erFrom0 lamSansPhase ]
    _    -> throwError' "I have no idea what to do in this case ..."

  where
    (Range _ eLhsLower eLhsUpper, Range _ _ eRsvLower) = (rLhs, rResolved)

    dbgAssertConsistency r stS = do
      (stS', _) <- resolvePartition' (Partition [r])
      assert (stS == stS') $ trace "asesrtion passed!"

    -- a function to be applied to a map that manipulates a sequence of
    -- sequences.
    bodyOnly v el er f = -- v[0..el] + Map(f, v[el..er]) + v[er..]
      (v >:@@: (0 :: Exp', el)) + callMap f (v >:@@: (el, er)) + (v >:@@: (er, mkCard v))

    -- for the EN01 case
    lambdaSplit v el er =
      simpleLambda v $ bodyOnly v el er lamSansPhase

    lamSansPhase = lambdaUnphase lam


-- Codegen lambda that takes multiple inputs.
codegenLambdaEntangle
  :: GensymEmitterWithStateError sig m => [Range] -> Lambda -> m [Stmt']
codegenLambdaEntangle rs (LambdaF{ bBases, eBases }) = do
  vReprs <- fsts <$> findEmitBasesByRanges rs
  unless (lenBbases == lenEbases && length vReprs == lenEbases) $
    throwError errInconsistentLength
  (iVar, _) <- gensymBinding "i" TNat
  return $ codegenApplyLambdaMany iVar vReprs bBases eBases
  where
    lenBbases = length bBases
    lenEbases = length eBases
    errInconsistentLength =
      "The numbers of lambda binders, expressions and ranges don't match with each other."

codegenApplyLambdaMany :: Var -> [Var] -> [Var] -> [Exp'] -> [Stmt']
codegenApplyLambdaMany iVar vReprs vBinders eBodies =
  [ SEmit $ vReprs :*:=: newSeqs ]
  where
    vEnv = aenvWithIndex (EVar iVar) vBinders vReprs
    substWvenv = subst vEnv
    newSeq vRepr eBody = natSeqLike vRepr (substWvenv eBody)
    newSeqs = zipWith newSeq vReprs eBodies

-- Make an `AEnv` that maps each `binder` to the `index` position of `repr`.
aenvWithIndex :: Exp' -> [Var] -> [Var] -> AEnv
aenvWithIndex idx = zipWith go
  where go binder repr = (binder, repr >:@: idx)


-- | Phase Kickback semantics for (Had, En) Locus
-- Given an En-typed locus formed by entangling a Had locus with a En locus and
-- an oracle function of shape
-- @
--   f(x, y) = (x, y + f(x))
-- @
-- where `y` points to the prior Had locus.
--  
-- The function takes the ket variable to the non-Had range and the phase
-- reference to the casted state and generates statements representing phase
-- kickback.
--
-- See [proposal/phaseful-had] for the math.
codegenPhaseKickback :: Var -> PhaseRef -> Int -> [Stmt']
codegenPhaseKickback vKet pRef = go
  where
    go 0 = []
