{-# LANGUAGE
    NamedFieldPuns
  #-}

module Qafny.Codegen.Lambda where
import           Control.Algebra
    (Has)
import           Control.Effect.Error
    (Error, throwError)
import           Control.Monad
    (unless)
import           Effect.Gensym
    (Gensym)
import           Qafny.Syntax.AST
    (AEnv, EmitExp (ECard, EMakeSeq), Exp (EEmit, EVar), Exp', Lambda,
    LambdaF (..), Range, Stmt', Substitutable (subst), Ty (TNat), Var,
    EmitStmt(..), Stmt (SEmit))
import           Qafny.Syntax.ASTFactory
    (eAt)
import           Qafny.Syntax.EmitBinding
    (Emitter (EmAnyBinding))
import           Qafny.Utils
    (GensymWithState, findEmitBasesByRanges, gensymBinding)



codegenLambdaEntangle
  :: ( GensymWithState sig m
     , Has (Error String) sig m
     )
  => [Range] -> Lambda -> m [Stmt']
codegenLambdaEntangle rs (LambdaF{ bBases, eBases }) = do
  vReprs <- findEmitBasesByRanges rs
  unless (lenBbases == lenEbases && length vReprs == lenEbases) $
    throwError errInconsistentLength
  iVar <- gensymBinding "i" TNat
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
    newSeq vRepr eBody = natSeqLike (EVar vRepr) (substWvenv eBody)
    newSeqs = zipWith newSeq vReprs eBodies

-- Make an `AEnv` that maps each `binder` to the `index` position of `repr`.
aenvWithIndex :: Exp' -> [Var] -> [Var] -> AEnv
aenvWithIndex idx = zipWith go
  where go binder repr = (binder, eAt (EVar repr) idx)

natSeqLike :: Exp' -> Exp' -> Exp'
natSeqLike liked = EEmit . EMakeSeq TNat (EEmit (ECard liked))
