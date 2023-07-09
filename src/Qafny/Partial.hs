{-# LANGUAGE
    FlexibleInstances
  , GeneralizedNewtypeDeriving
  , TupleSections
  #-}

module Qafny.Partial where
import           Data.Bool        (bool)
import qualified Data.Map.Strict  as Map
import           Data.Maybe       (isJust, isNothing)
import           Qafny.AST
import           Qafny.ASTFactory

--------------------------------------------------------------------------------
-- $doc
-- 'Qafny.Partial' module implements the partial evaluation strategy of
-- expressions, (linear) arithmetic expressions and ranges in particular.
--
-- The goal is to reduce an expression with uninterpreted variables /as much as/
-- possible.
--
-- $doc
--------------------------------------------------------------------------------

-- | Result of performing partial evaluation
type PResult = (Map.Map Var Int, Int)

class PEval a where
  evalP :: a -> PResult
  reflectP :: PResult -> a

instance PEval Exp where
  evalP (ENum i) = (Map.empty, i)
  evalP (EVar v) = (Map.singleton v 1, 0)
  evalP (EOp2 op e1 e2) =
    let (m1, v1) = evalP e1
        (m2, v2) = evalP e2
    in case op of
      OAdd -> (evalResidue (+) m1 m2, v1 + v2)
      OSub -> (evalResidue (+) m1 (Map.map (0 -) m2), v1 - v2)
      _    -> undefined

  reflectP (m, i) =
    Map.foldrWithKey go (ENum i) m
    where
      go v cnt =
        let fs = if cnt >= 0
                 then replicate cnt (EOp2 OAdd `flip` EVar v)
                 else replicate (negate cnt) (EOp2 OSub `flip` EVar v)
        in foldr (.) id fs

class Reducible a where
  reduce :: a -> a

instance Reducible a => Reducible [a] where
  reduce = fmap reduce

instance Reducible Exp where
  reduce = reflectP . evalP

instance Reducible Range where
  reduce (Range x l r) = Range x (reduce l) (reduce r)

instance Reducible Partition where
  reduce = Partition . reduce . unpackPart

-- | Union two residual maps with the given operator and remove zero-coefficient
-- variables
evalResidue
  :: (Int -> Int -> Int)
  -> Map.Map Var Int
  -> Map.Map Var Int
  -> Map.Map Var Int
evalResidue f s1 s2 = Map.filter (/= 0) $ Map.unionWith f s1 s2

staticValue :: PResult -> Maybe Int
staticValue (s, i) = bool Nothing (Just i) $ Map.null s

evalPStatic :: PEval a => a -> Maybe Int
evalPStatic = staticValue . evalP

hasResidue :: PEval a => a -> Bool
hasResidue = isJust . staticValue . evalP


--------------------------------------------------------------------------------
-- * Misc Evaluation
--------------------------------------------------------------------------------
-- newtype PExp = PExp { unPExp :: Exp }

sizeOfRangeP :: Range -> Maybe Int
sizeOfRangeP (Range _ el er) = evalPStatic (er `eSub` el)
