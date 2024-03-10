{-# LANGUAGE
    FlexibleContexts
  , FlexibleInstances
  , LambdaCase
  , MultiParamTypeClasses
  , MultiWayIf
  , ScopedTypeVariables
  , TupleSections
  , TypeApplications
  , TypeFamilies
  #-}
{-# LANGUAGE NamedFieldPuns #-}


module Qafny.Typing.Phase where

-- | Phase-related Typing

-- Effects
import           Control.Effect.Catch
import           Control.Effect.Error
    (Error, throwError)
import           Control.Effect.Lens
import           Control.Effect.State
    (State)
import           Effect.Gensym
    (Gensym)

-- Qafny
import           Qafny.Syntax.IR
import           Qafny.Syntax.AST
import           Qafny.Syntax.EmitBinding
import           Qafny.TypeUtils
import           Qafny.Utils

-- Utils
import           Control.Effect.Trace
import           Control.Lens
    (at, (%~), (?~), (^.))
import           Control.Monad
    (forM, when)
import           Data.List
    (nub, singleton)
import           Data.Sum
    (Injection (inj))
import           Qafny.Syntax.ASTUtils
    (getPhaseRef, phaseRefToTy)
import           Qafny.Syntax.Emit
    (showEmitI)
import           Text.Printf
    (printf)
import Data.Maybe (catMaybes, mapMaybe)

throwError'
  :: ( Has (Error String) sig m )
  => String -> m a
throwError' = throwError @String . ("[Phase Typing] " ++)

-------------------------------------------------------------------------------
-- | Promotion Scheme
--------------------------------------------------------------------------------
data PromotionScheme = PromotionScheme
  { psPrefs     :: [PhaseRef]
  , psDgrPrev   :: Int
  , psDgrCurr   :: Int
  , psPromotion :: Promotion
  }

data Promotion
  = Promote'0'1 (Exp', Exp') [Range] QTy

-- | Promote phases to another level
-- - The degree of the binder should agree with the degree of the tuple
-- - The degree of the spec can be different from the one of the binder: this is
--   where the promotion kicks in
--
promotionScheme
  :: ( Has (Gensym Emitter) sig m
     , Has (State TState) sig m
     , Has (Error String) sig m
     , Has Trace sig m
     )
  => STuple -> PhaseBinder -> PhaseExp -> m (Maybe PromotionScheme)
promotionScheme st@(STuple (loc, Partition rs, (qt, dgrsSt))) pb pe = do
  -- FIXME: for now, the simple dirty way is to restrict `dgrsSt` to have only
  -- one consistent degree. So the promotionScheme can act on the entire
  -- partition, which I think is a good idea for now.  Unless one specified a
  -- weird phase in the precondition, there's no statement available for you to
  -- construct a partition with multiple different degrees.

  -- intro degrees
  dgrSt <- onlyOne throwError' $ nub dgrsSt
  let dgrBind = analyzePhaseSpecDegree pb
      dgrSpec = analyzePhaseSpecDegree pe

  -- check if binder's and specexp's degrees match
  when (dgrSt /= dgrBind) $ throwError' (errDgrMismatch dgrSt dgrBind)

  -- check what promotion can be done here
  case (dgrBind, dgrSpec) of
    (dBind, dSpec) | dBind == dSpec -> return Nothing
    (0, 1)                          -> promote'0'1 pe
    (1, 2)                          -> promote'1'2
    (dBind, dSpec) | dBind > dSpec  -> errDemotion dBind dSpec
    (dBind, dSpec)                  -> errUnimplementedPrompt dBind dSpec
  where
    -- Promote 0 to 1
    promote'0'1
      :: ( Has (Gensym Emitter) sig m'
         , Has (State TState) sig m'
         , Has (Error String) sig m'
         , Has Trace sig m'
         )
      => PhaseExp -> m' (Maybe PromotionScheme)
    promote'0'1 (PhaseOmega i n) = do
      let fstSt = modifyPty (1 <$) st
      ptys <- allocAndUpdatePhaseType fstSt
      dumpSt "After promotion"
      let prefs = getPhaseRef <$> ptys
      return . Just $ PromotionScheme
        { psPrefs = prefs
        , psDgrPrev = 0
        , psDgrCurr = 1
        , psPromotion = Promote'0'1 (i, n) rs qt
        }
    promote'0'1 _ = internalError


    -- Promote 1 to 2
    errDgrMismatch dSt dbinder =
      printf "Degree %d doesn't match the degree of the binder %s : %d"
      dSt (showEmitI 4 dbinder) dbinder
    promote'1'2 = undefined
    errDemotion i j = throwError' $
      printf "Demote %d to %d is not allowed." i j
    errUnimplementedPrompt i j =  throwError' $
      printf "Promoting %d to %d is undefined." i j


--------------------------------------------------------------------------------
-- * Phase Typing
--------------------------------------------------------------------------------

-- | Analyze the degree of a phase expression
analyzePhaseSpecDegree :: PhaseExpF f -> Int
analyzePhaseSpecDegree PhaseZ          = 0
analyzePhaseSpecDegree PhaseWildCard   = 0
analyzePhaseSpecDegree PhaseOmega{}    = 1
analyzePhaseSpecDegree PhaseSumOmega{} = 2


-- dispatchPhaseSpec :: (forall k . PhaseExpF' f k -> g) -> PhaseExpF f -> g
-- dispatchPhaseSpec f = construct
--   where
--     construct PhaseZ = f (PhaseZ')
--     construct PhaseWildCard = f (PhaseWildCard')
--     construct (PhaseOmega a b) = f (PhaseOmega' a b)
--     construct (PhaseSumOmega r a b) = f (PhaseSumOmega' r a b)



-- | Generate variables and phase types based on a phase specification.
-- generatephasetype
--   :: ( Has (Gensym Emitter) sig m
--      )
--   => Int -> m PhaseTy
-- generatePhaseType 0 = return PT0
-- generatePhaseType n = do
--   vEmitBase <- gensym (LBinding ("base", inj n))
--   vEmitRepr <- gensym (LBinding ("repr", inj (typingPhaseEmitReprN 1)))
--   return (PTN n $ PhaseRef { prBase = vEmitBase, prRepr = vEmitRepr })

-- | Generate a new phase type based on the STuple.
--
-- allocPhaseType
--   :: ( Has (Gensym Emitter) sig m
--      , Has (State TState) sig m
--      , Has (Error String) sig m
--      )
--   => STuple -> m [PhaseTy]
-- allocPhaseType (STuple (loc, Partition rs, (qt, dgrs))) =
--   if isEN qt
--     then
--     do dgr <- onlyOne throwError' dgrs
--        ed  <- genEDStUpdatePhase dgr  (inj loc)
--        return [evPhaseTy dgr ed]
--     else do checkListCorr dgrs rs
--             sequence [ evPhaseTy dgr <$> genEDStUpdatePhase dgr (inj r)
--                      | (r, dgr) <- zip rs dgrs
--                      ]


updateTState
  :: ( Has (State TState) sig m )
  => STuple -> m ()
updateTState s@(STuple (loc, p, (qt, dgrs))) =
  sSt %= (at loc ?~ (p, (qt, dgrs)))


allocAndUpdatePhaseType
  :: ( Has (Gensym Emitter) sig m
     , Has (State TState) sig m
     , Has (Error String) sig m
     )
  => STuple -> m [PhaseTy]
allocAndUpdatePhaseType s@(STuple(loc, Partition{ranges}, (qt, dgrs))) = do
  updateTState s
  mapMaybe evPhaseTy <$> genEDStUpdatePhaseFromSTuple loc ranges qt dgrs
  

-- | Query in the emit state the phase types of the given STuple
queryPhaseType
  :: ( Has (State TState) sig m
     , Has (Error String) sig m
     )
  => STuple -> m [PhaseTy]
queryPhaseType (STuple (loc, Partition rs, (qt, dgrs))) =
  if isEN qt
    then do dgr <- onlyOne throwError' dgrs
            catMaybes . singleton . evPhaseTy <$> findED (inj loc)
    else do checkListCorr rs dgrs
            catMaybes <$> sequence [ evPhaseTy <$> findED (inj r)
                                   | (r, dgr) <- zip rs dgrs
                                   ]
