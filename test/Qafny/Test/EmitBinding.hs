{-# LANGUAGE
    FlexibleInstances
  , PartialTypeSignatures
  #-}

module Qafny.Test.EmitBinding where

import           Control.Carrier.Error.Either
    (runError)
import           Qafny.Analysis.Normalize
    (Normalizable (normalize))
import           Qafny.Runner
    (debugGensymEmitterWithState)
import           Qafny.Syntax.AST
import           Qafny.Syntax.Emit
import           Qafny.Syntax.EmitBinding
    (Emitter)
import           Qafny.Syntax.IR
import           Qafny.Utils.EmitBinding
    (genEmStFromLocus)


ppTerm :: DafnyPrinter a => (Int, [(Emitter, String)], (TState, Either Builder a)) -> IO ()
ppTerm (i, _, (st, ans)) =
  prettyIO $ vsep [pp i, pp st, pp "ans:", incr2 ppAns] <> line
  where
    ppAns = either id pp ans

term1 :: (Int, [(Emitter, String)], (TState, Either Builder _))
term1 = debugGensymEmitterWithState . runError $
  LocusEmitData' <$> genEmStFromLocus l
  where
    l :: Locus
    l = Locus (Loc "a") (normalize (Partition rs)) TEn [0]
    rs = [Range "x" 0 1, Range "y" 0 1]
