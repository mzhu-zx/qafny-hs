{-# LANGUAGE
    FlexibleInstances
  , TypeOperators
  #-}

module Qafny.Syntax.EmitBinding where


import           Control.Applicative
    (Alternative (..))
import qualified Data.Map.Strict       as Map
import           Data.Sum
import           Qafny.Syntax.AST
import           Qafny.Syntax.ASTUtils
    (getPhaseRefMaybe)
-- * EmitBinding related functions

-- | 'EmitData' stores emit variables (a.k.a. data variables) that's supposed to
-- be mapped to either a 'Loc' or a 'Range'
--
data EmitData = EmitData
  { evPhaseTy    :: Maybe PhaseTy -- ^ the variables for the phase
  , evBasis      :: Maybe String   -- ^ the varible for its basis
  , evAmp        :: Maybe String   -- ^ the variable for its amplitude
  , evBasisTy    :: Maybe Ty
  , evPhaseSeqTy :: Maybe Ty
  }
  deriving (Eq, Ord, Show)

mtEmitData :: EmitData
mtEmitData = EmitData { evPhaseTy = Nothing
                      , evBasis = Nothing
                      , evAmp   = Nothing
                      , evBasisTy = Nothing
                      , evPhaseSeqTy = Nothing
                      }

evPhase :: EmitData -> Maybe PhaseRef
evPhase ed = getPhaseRefMaybe =<< evPhaseTy ed

-- Merge two EmitData pairwise and prefer the 'Just'-fields or the latter one if
-- both are fields 'Just'
instance Semigroup EmitData where
  ed1 <> ed2 = EmitData
    { evPhaseTy    = evPhaseTy ed2    <|> evPhaseTy ed1
    , evBasis      = evBasis ed2      <|> evBasis ed1
    , evAmp        = evAmp ed2        <|> evAmp ed1
    , evPhaseSeqTy = evPhaseSeqTy ed2 <|> evPhaseSeqTy ed1
    , evBasisTy    = evBasisTy ed2    <|> evBasisTy ed1
    }


-- | EmitBinding : "the query result"
newtype EmitBinding
  = EmitBinding { unEB :: (Range :+: Loc, EmitData) }
  deriving (Eq, Ord)

instance Substitutable EmitBinding where
  subst a (EmitBinding (Inl r, t)) = EmitBinding (inj (subst a r), t)
  subst a b                        = b

  fVars (EmitBinding (Inl r, _)) = fVars r
  fVars _                        = []

instance Substitutable (Map.Map (Range :+: Loc) EmitData) where
  subst = substMapKeys
  fVars = fVarMapKeys

instance Show EmitBinding where
  show (EmitBinding t) = show t


-- | Emitter : the thing used to perform Gensym
data Emitter
  = EmBaseSeq Range QTy              -- ^ Base  seq per range
  | EmPhaseSeq (Range :+: Loc) Int   -- ^ Phase Seq per range/loc with degree
  | EmPhaseBase (Range :+: Loc)      -- ^ Phase Base per range/loc with degree
  -- TODO: I may need to add a Phase Index here
  | EmAmplitude                      -- ^ Amplitude?
  | EmAnyBinding Var Ty              -- ^ Anything like a binding
  deriving (Show)
