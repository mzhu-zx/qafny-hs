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

module Qafny.Typing.Phase where

-- | Phase-related Typing

-- Effects
import           Control.Effect.Catch
import           Control.Effect.Error     (Error, throwError)
import           Control.Effect.Lens
import           Control.Effect.State     (State)
import           Effect.Gensym            (Gensym)

-- Qafny
import           Qafny.Env
import           Qafny.Syntax.AST
import           Qafny.Syntax.EmitBinding
import           Qafny.TypeUtils
import           Qafny.Utils

-- Utils
import           Control.Effect.Trace
import           Control.Lens             (at, (%~), (?~), (^.))
import           Control.Monad            (forM)
import           Qafny.Syntax.ASTUtils    (getPhaseRef)
import           Text.Printf              (printf)

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
promotionScheme
  :: ( Has (Gensym EmitBinding) sig m
     , Has (State TState) sig m
     , Has (Error String) sig m
     , Has Trace sig m
     )
  => STuple -> PhaseBinder -> PhaseExp -> m (Maybe PromotionScheme)
promotionScheme st@(STuple (loc, Partition rs, (qt, dgrsSt))) pb pe = do
  let dgrBind = analyzePhaseSpecDegree pb
      dgrSpec = analyzePhaseSpecDegree pe
  case (dgrBind, dgrSpec) of
    (db, ds) | db == ds -> return Nothing
    (0, 1)              -> promote'0'1 pe
    (1, 2)              -> promote'1'2
    (db, ds) | db > ds  -> errDemotion db ds
    (db, ds)            -> errUnimplementedPrompt db ds
  where
    -- Promote 0 to 1
    promote'0'1
      :: ( Has (Gensym EmitBinding) sig m'
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
--   :: ( Has (Gensym EmitBinding) sig m
--      )
--   => Int -> m PhaseTy
-- generatePhaseType 0 = return PT0
-- generatePhaseType n = do
--   vEmitBase <- gensym (LBinding ("base", inj n))
--   vEmitRepr <- gensym (LBinding ("repr", inj (typingPhaseEmitReprN 1)))
--   return (PTN n $ PhaseRef { prBase = vEmitBase, prRepr = vEmitRepr })

-- | Generate a new phase type based on the STuple.
--
allocPhaseType
  :: ( Has (Gensym EmitBinding) sig m
     , Has (State TState) sig m
     , Has (Error String) sig m
     )
  => STuple -> m [PhaseTy]
allocPhaseType (STuple (loc, Partition rs, (qt, dgrs))) =
  if | isEN qt -> do
         dgr <- onlyOne throwError' dgrs
         pty <- gensymEmitLocDegree loc dgr
         return [pty]
     | otherwise -> do
         checkListCorr dgrs rs
         forM (zip rs dgrs) (uncurry gensymEmitRangeDegree)

updateTState
  :: ( Has (State TState) sig m )
  => STuple -> m ()
updateTState s@(STuple (loc, p, (qt, dgrs))) =
  sSt %= (at loc ?~ (p, (qt, dgrs)))


allocAndUpdatePhaseType
  :: ( Has (Gensym EmitBinding) sig m
     , Has (State TState) sig m
     , Has (Error String) sig m
     )
  => STuple -> m [PhaseTy]
allocAndUpdatePhaseType s = do
  updateTState s
  allocPhaseType s

-- generatePhaseTypeThen
--   :: ( Has (Gensym EmitBinding) sig m
--      , Has (State TState) sig m
--      , Has (Error String) sig m
--      )
--   => (PhaseTy -> m g) -- do when it's EN
--   -> ([PhaseTy] -> m g) -- do when it isn't
--   -> STuple
--   -> m ([PhaseTy], g)
-- generatePhaseTypeThen fLoc fOthers (STuple (loc, Partition rs, (qt, dgrs))) =
--   if | isEN qt -> do
--          dgr <- onlyOne throwError' dgrs
--          pty <- gensymEmitLocDegree loc dgr
--          ([pty],) <$> fLoc pty
--      | otherwise -> do
--          checkListCorr dgrs rs
--          ptys <- forM (zip rs dgrs) (uncurry gensymEmitRangeDegree)
--          (ptys,) <$> fOthers ptys


-- | Query in the emit state the phase types of the given STuple
queryPhaseType
  :: ( Has (State TState) sig m
     , Has (Error String) sig m
     )
  => STuple -> m [PhaseTy]
queryPhaseType (STuple (loc, Partition rs, (qt, dgrs))) =
  if | isEN qt -> do
         dgr <- onlyOne throwError' dgrs
         (: []) <$> findEmitLocDegree loc dgr
     | otherwise -> do
         checkListCorr rs dgrs
         forM (zip rs dgrs) $ uncurry findEmitRangeDegree
