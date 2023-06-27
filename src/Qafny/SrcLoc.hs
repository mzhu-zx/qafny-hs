module Qafny.SrcLoc where

data SrcLoc = SrcLoc
  { sLine   :: !Int
  , sColumn :: !Int
  }


-- | Attach 'SrcLoc' information to a functor and tie the knot to form a
-- recursive datatype
data HasSrcLoc f = HasSrcLoc SrcLoc f

type HasSrcLocFix f = HasSrcLoc (f HasSrcLoc)

unstrip :: HasSrcLoc f -> f
unstrip (HasSrcLoc _ f) = f
