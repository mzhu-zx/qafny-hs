module Qafny.SrcLoc where

data SrcLoc = SrcLoc
  { sLine   :: !Int
  , sColumn :: !Int
  }


-- | Attach 'SrcLoc' information to a functor and tie the knot to form a
-- recursive datatype
data HasSrcLoc m = HasSrcLoc SrcLoc (m (HasSrcLoc m))
