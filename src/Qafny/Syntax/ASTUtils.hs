{-# LANGUAGE
    TupleSections
  #-}

module Qafny.Syntax.ASTUtils where

import           Qafny.Syntax.AST


getPhaseRef :: PhaseTy -> PhaseRef
getPhaseRef (PTN _ r) = r
getPhaseRef _         = undefined

getPhaseRefN :: [PhaseTy] -> [(Int, PhaseRef)]
getPhaseRefN ptys = do
  pty <- ptys
  case pty of
    PT0      -> []
    PTN n pr -> return (n, pr)
