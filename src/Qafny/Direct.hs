module Qafny.Direct where

{- Experiment: Type-directed Compilation
   - Pass 1. Typing: traverse the AST and produce type derivation at each step
   - Pass 2. Compilation: traverse the derivation to produce codegen
   - Fuse: traverse and produce derivation in postorder and call the compiler on
     each step  
-}

import           Qafny.AST
import           Qafny.Transform

data Derivation f
  = DIf f f f
  -- deriving Functor

class Infer a where
  infer :: a -> Transform (Derivation [a])

-- inferCompile :: Infer a => (Derivation -> Transform [a]) -> Transform [a]
-- inferCompile a f = infer a >>=  f

-- instance Infer Stmt where
  
