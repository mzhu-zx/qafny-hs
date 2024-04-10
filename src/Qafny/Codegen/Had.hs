module Qafny.Codegen.Had where

import           Control.Arrow
    (Arrow (second))
import           Qafny.Effect
import           Qafny.Syntax.AST
import           Qafny.Syntax.ASTFactory
import           Qafny.Syntax.Emit
import           Qafny.Syntax.EmitBinding
import           Qafny.Syntax.IR
import           Text.Printf
    (printf)

throwError'
  :: ( Has (Error String) sig m )
  => String -> m a
throwError' = throwError @String . ("[Codegen/Had] " ++)

-- | Generate statements to promote the type of a locus.
codegenNorToHad
  :: ( Has (Error String) sig m)
  => CastScheme -> m [Stmt']
codegenNorToHad
  CastScheme{ schEdsFrom=edsFrom@(lEdFrom, rsEdFrom), schEdsTo=edsTo@(lEdTo, rsEdTo)
            , schQtFrom , schQtTo
            } =
  case rules schQtFrom schQtTo of
    Nothing -> throwError' $ printf
      "%s cannot be casted into %s:\n%s\n%s\n"
      (showEmit0 schQtFrom) (showEmit0 schQtTo)
      (showEmit0 (second byComma edsFrom))
      (showEmit0 (second byComma edsTo))
    Just s  -> return s
  where
    rules :: QTy -> QTy -> Maybe [Stmt']
    -- "nor < *"
    rules TNor THad = do
      -- | Cast Nor to first degree Had
      -- No amplitude is involved
      (PhaseRef vBase vRepr, TSeqNat) <- evPhaseRef lEdTo
      [(vKet, TSeqNat)]               <- (evBasis . snd) `mapM` rsEdFrom
      return $ SEmit <$>
        [[vBase, vRepr] :*:=: ["CastNorHad" >$ vKet]]
    rules _ _ = Nothing
