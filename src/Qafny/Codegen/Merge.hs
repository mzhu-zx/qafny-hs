{-# LANGUAGE
    TypeFamilies
  #-}

module Qafny.Codegen.Merge(codegenMergeScheme) where

-- Effects
import           Qafny.Effect

-- Handlers

-- Utils

import           Text.Printf
    (printf)

-- Qafny

import           Qafny.Partial
    (Reducible (reduce))
import           Qafny.Syntax.AST
import           Qafny.Syntax.ASTFactory
import           Qafny.Syntax.EmitBinding
import           Qafny.Syntax.IR

import           Data.Sum
    (Injection (inj))
import           Qafny.Utils.EmitBinding


throwError'
  :: ( Has (Error String) sig m )
  => String -> m a
throwError' = throwError @String . ("[Codegen/Merge] " ++)



--------------------------------------------------------------------------------
-- * Merge Semantics
--------------------------------------------------------------------------------
-- | Merge semantics of a Had qubit into one EN emitted state
-- uses the name of the emitted seq as well as the index name
addENHad1 :: Var -> Exp' -> Stmt'
addENHad1 vEmit idx =
  (::=:) vEmit $
    EOp2 OAdd (EVar vEmit) (EEmit $ ECall "Map" [eLamPlusPow2, EVar vEmit])
  where
    vfresh = "x__lambda"
    eLamPlusPow2 =
      simpleLambda vfresh $
        EOp2 OAdd (EVar vfresh) (EEmit (ECall "Pow2" [idx]))


-- | Multiply the Had coutner by 2
doubleHadCounter :: Var -> Stmt'
doubleHadCounter vCounter =
  (::=:) vCounter $ EOp2 OMul (ENum 2) (EVar vCounter)


-- | Generate from the merge scheme statements to perform the merge and the
-- final result variable.
codegenMergeScheme
  :: ( Has (Gensym Emitter) sig m
     , Has (Gensym String) sig m
     , Has (State TState) sig m
     , Has (Error String) sig m
     )
  => [MergeScheme] -> m [(Stmt', Var)]
codegenMergeScheme = mapM $ \scheme -> do
  case scheme of
    MMove -> throwError' "I have no planning in solving it here now."
    MJoin JoinStrategy { jsQtMain=qtMain, jsQtMerged=qtMerged
                       , jsRResult=rResult, jsRMerged=rMerged, jsRMain=rMain
                       } -> do
      (vEmitMerged, _) <- findEmitBasisByRange rMerged
      (vEmitMain, _)   <- findEmitBasisByRange rMain
      deleteEms $ inj <$> [rMerged, rMain]
      case (qtMain, qtMerged) of
        (TEn01, TNor) -> do
          -- append the merged value (ket) into each kets in the main value
          -- TODO: use `genEmStFromLocus` for phase compatibility
          (vEmitResult, _) <- genEmStByRange qtMain rResult >>= visitEmBasis
          vBind <- gensym "lambda_x"
          let stmt = vEmitResult ::=: callMap ef vEmitMain
              ef   = simpleLambda vBind (EVar vBind + EVar vEmitMerged)
          return (stmt, vEmitMain)
        (TEn, THad) -> do
          let (Range _ lBound rBound) = rMain
          let stmtAdd = addENHad1 vEmitMain (reduce (rBound - lBound))
          return (stmtAdd, vEmitMain)
        _             -> throwError' $ printf "No idea about %s to %s conversion."
    MEqual EqualStrategy { esRange = r, esQTy = qt
                         , esVMain = (v1, _), esVAux = (v2, _) } -> do
      -- This is all about "unsplit".
      case qt of
        TNor ->
          -- no "unsplit" should happen here!
          return (qComment "TNor has nothing to be merged!", v1)
        THad ->
          throwError' $ printf "This type (%s) cannot be handled: (%s)" (show qt) (show r)
        _ | qt `elem` [ TEn01, TEn ] ->
          -- TEn01 is emitted as seq<seq<nat>> representing Sum . Tensor,
          -- TEn   is emitted as seq<nat>      representing Sum . Tensor,
          -- It suffices to simply concat them
          pure (merge3 v1 v1 v2, v1)
        _ -> throwError' "This pattern shoule be complete!"
  where
    merge3 vS vRF vRT = vS ::=: (EVar vRF + EVar vRT)
