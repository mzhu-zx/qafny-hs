module Qafny.Typing.Locus where

import           Control.Lens
    (at, (?~))
import           Qafny.Effect
import           Qafny.Syntax.IR


updateLocusSt
  :: ( Has (State TState) sig m )
  => Locus -> m ()
updateLocusSt s@Locus{loc, part, qty, degrees} =
  sSt %= (at loc ?~ (part, (qty, degrees)))
