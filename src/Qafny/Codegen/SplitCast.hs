{-# LANGUAGE
    TypeFamilies
  #-}

module Qafny.Codegen.SplitCast where


import           Control.Monad
    (liftM2)
import qualified Data.List.NonEmpty       as NE
import           Qafny.Effect
import           Qafny.Partial
import           Qafny.Syntax.AST
import           Qafny.Syntax.ASTFactory
import           Qafny.Syntax.EmitBinding
import           Qafny.Syntax.IR
import           Qafny.Typing
    (castScheme, resolvePartition, retypePartition)
import           Qafny.Utils.EmitBinding
import           Qafny.Utils.Utils
    (both)
import           Text.Printf
    (printf)
import Data.Maybe (maybeToList)



throwError'
  :: ( Has (Error String) sig m )
  => String -> m a
throwError' = throwError @String . ("[Codgen|SplitCast] " ++)

--------------------------------------------------------------------------------
-- * Split Semantics
--------------------------------------------------------------------------------
codegenSplitEmitMaybe :: Maybe SplitScheme -> [Stmt']
codegenSplitEmitMaybe = maybe [] codegenSplitEmit

-- | Generate emit variables and split operations from a given split scheme.
codegenSplitEmit :: SplitScheme -> [Stmt']
codegenSplitEmit
  SplitScheme { schEdAffected=(rAffected@(Range _ elAff erAff)
                              ,edAffL, edAffR )
              , schEdSplit=(rSplit ,edSplitR)
              , schEdRemainders
              } =
  concatMap stmtsSplitRem $ NE.toList schEdRemainders ++ [(rSplit, edAffL, edSplitR)]
  where
    stmtsSplitRem (Range _ elRem erRem, edRemL, edRemR) =
      let off  = elRem - elAff
          size = erRem - elRem
      in codegenSplitEd edRemL edAffL off size ++
         codegenSplitEd edRemR edAffR   off size


codegenSplitEd :: EmitData -> EmitData -> Exp' -> Exp' -> [Stmt']
codegenSplitEd ed1 ed2 offset size =
  liftC splitSimple base
  ++ liftC splitSimple amp
  ++ concat (liftC splitPhase refs)
  where
    liftC f a = maybeToList $ uncurry (liftM2 f) a
    bothFst f = both ((fst <$>) . f)
    base  = bothFst evBasis (ed1, ed2)
    amp   = bothFst evAmp (ed1, ed2)
    refs  = bothFst evPhaseRef (ed1, ed2)

    splitPhase :: PhaseRef -> PhaseRef -> [Stmt']
    splitPhase pr1 pr2 =
      [ splitSimple (prRepr pr1) (prRepr pr2)
      , prBase pr1 ::=: EVar (prRepr pr2)
      ]

    splitSimple :: Var -> Var -> Stmt'
    splitSimple v1 v2 =
      v1 ::=: v2 >:@@: (offset, offset + size)


--------------------------------------------------------------------------------
-- * Split & Cast Semantics
--------------------------------------------------------------------------------
codegenSplitThenCastEmit
  :: ( Has (Error String) sig m
     , Has Trace sig m
     )
  => Maybe SplitScheme
  -> Maybe CastScheme
  -> m [Stmt']
codegenSplitThenCastEmit sS sC = do
  trace "* codegenSplitThenCastEmit"
  (codegenSplitEmitMaybe sS ++) <$> codegenCastEmitMaybe sC


--------------------------------------------------------------------------------
-- * Cast Semantics
--------------------------------------------------------------------------------
-- | Mutate the typing state and generate the expressions to cast
codegenCast
  :: GensymEmitterWithStateError sig m
  => Locus -> QTy -> m [Stmt']
codegenCast locus qtyInto = do
  (locus', mayScheme) <- castScheme locus qtyInto
  codegenCastEmitMaybe mayScheme

codegenCastEmitMaybe
  :: ( Has (Error String) sig m)
  => Maybe CastScheme -> m [Stmt']
codegenCastEmitMaybe =
  maybe (return []) codegenCastEmit


codegenCastEmit
  :: ( Has (Error String) sig m)
  => CastScheme -> m [Stmt']
codegenCastEmit
  CastScheme{ schVsOldEmit=vsOldEmits
            , schVsNewEmit=vsNewEmit
            , schQtNew=qtNew
            , schQtOld=qtOld
            , schRsCast=rsCast
            } = do
  op <- mkOp qtOld qtNew
  return . concat $
      [ [ qComment $ "Cast " ++ show qtOld ++ " ==> " ++ show qtNew
        , (::=:) vNew $ EEmit (op rCast  `ECall` [EEmit $ EDafnyVar vOld])
        ]
      | ((vOld, tyOld), (vNew, tyNew), rCast) <- zip3 vsOldEmits vsNewEmit rsCast ]
  where
    -- | Consume /from/ and /to/ types and return a function that consumes a
    -- range and emit a specialized cast operator based on the property of the
    -- range passed in
    mkOp TNor TEn   = return $ const "CastNorEN"
    mkOp TNor TEn01 = return $ const "CastNorEN01"
    mkOp TNor THad  = return $ const "CastNorHad"
    mkOp THad TEn01 = return $ \r -> case sizeOfRangeP r of
      Just 1 -> "CastHadEN01'1"
      _      -> "CastHadEN01"
    mkOp _    _     = throwError err
    err :: String = printf "Unsupport cast from %s to %s." (show qtOld) (show qtNew)

-- | Convert quantum type of `s` to `newTy` and emit a cast statement with a
-- provided `op`
castWithOp
  :: GensymEmitterWithStateError sig m
  => String -> Locus -> QTy -> m (Locus, [Stmt'])
castWithOp op s newTy = do
  (newLocus, maySchemeC) <- castScheme s newTy
  (newLocus, ) <$> case maySchemeC of
       Nothing      -> return []
       Just schemeC -> go schemeC
  where
    go CastScheme{ schVsOldEmit=vsOldEmits, schVsNewEmit=vsNewEmit} = do
      let partitionTy = (qty s, degrees s)
      -- assemble the emitted terms
      return . concat $
        [ [ qComment $ "Cast " ++ show partitionTy ++ " ==> " ++ show newTy
          , (::=:) vNew $ EEmit (op `ECall` [EEmit $ EDafnyVar vOld])
          ]
        | ((vOld, _), (vNew, _)) <- zip vsOldEmits vsNewEmit ]


-- | Cast the given partition to EN type!
castPartitionEN
  :: GensymEmitterWithStateError sig m
  => Locus -> m [Stmt']
castPartitionEN = (snd <$>) . castPartitionEN'

-- | Cast the given partition to EN type!
castPartitionEN'
  :: GensymEmitterWithStateError sig m
  => Locus -> m (Locus, [Stmt'])
castPartitionEN' st@Locus{loc=locS, part=s, qty=qtS} = do
  case qtS of
    TNor -> castWithOp "CastNorEN" st TEn
    THad -> castWithOp "CastHadEN" st TEn
    TEn -> throwError' $
      printf "Partition `%s` is already of EN type." (show st)
    TEn01 -> throwError' $
      printf "Casting %s to TEn is expensive therefore not advised!" (show qtS)
    TQft -> throwError' $
      printf "It is impossible to cast into Qft type."

-- | Duplicate the data, i.e. sequences to be emitted, by generating statements
-- that duplicates the data as well as the correspondence between the range
-- bindings, emitted variables from the fresh copy and the original emitted
-- varaibles.
--
-- However, this does not add the generated symbols to the typing environment or
-- modifying the existing bindings!
--
dupState
  :: ( GensymEmitterWithStateError sig m
     , Has (Reader IEnv) sig m
     , Has Trace sig m
     )
  => Partition -> m ([Stmt'], [((Var, Ty), (Var, Ty))])
dupState s' = do
  Locus{loc=locS, part=s, qty=qtS, degrees=ptys} <- resolvePartition s'
  let rs = ranges s
  -- generate a set of fresh emit variables as the stashed partition
  -- do not manipulate the `emitSt` here
  vsEmitFresh <- genEmByRange qtS `mapM` rs >>= visitEmsBasis
  -- the only place where state is used!
  vsEmitPrev  <- findEmitBasesByRanges rs
  let comm = qComment "Duplicate"
  let stmts = [ (::=:) vEmitFresh (EVar vEmitPrev)
              | ((vEmitFresh, _), (vEmitPrev, _)) <- zip vsEmitFresh vsEmitPrev ]
  return (comm : stmts, zip vsEmitPrev vsEmitFresh)

-- | Assemble a partition collected from the guard with bounds and emit a
-- verification time assertions that checks the partition is indeed within the
-- bound.
--
-- Precondition: Split has been performed at the subtyping stage so that it's
-- guaranteed that only one range can be in the partition
--
makeLoopRange
  :: Has (Error String) sig m
  => Partition -> Exp' -> Exp' -> m (Range, Exp')
makeLoopRange (Partition [Range r sl sh]) l h =
  return
    ( Range r l h
    , EEmit (EOpChained l [(OLe, sl), (OLt, sh), (OLe, h)])
    )
makeLoopRange s _ _ =
  throwError $
    "Partition `"
      ++ show s
      ++ "` contains more than 1 range, this should be resolved at the typing stage"



