module Qafny.Typing.Qft where

import Qafny.Effect
import Qafny.Syntax.AST
import Qafny.Syntax.IR


typingQft
  :: GensymEmitterWithStateError sig m
  => Locus -> m Locus
typingQft loc =
  return loc { qty = TQft }
