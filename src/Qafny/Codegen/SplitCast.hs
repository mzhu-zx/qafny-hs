{-# LANGUAGE
    TypeFamilies
  #-}

module Qafny.Codegen.SplitCast where

import           Control.Algebra
import           Control.Effect.Error
    (Error, throwError)
import           Control.Effect.Reader
import           Control.Effect.Trace
import           Qafny.Partial
import           Qafny.Syntax.AST
import           Qafny.Syntax.ASTFactory
    (qComment)
import           Qafny.Syntax.IR
import           Qafny.Typing
    (resolvePartition, retypePartition)
import           Qafny.Utils.EmitBinding
import           Text.Printf
    (printf)


throwError'
  :: ( Has (Error String) sig m )
  => String -> m a
throwError' = throwError @String . ("[Codgen|SplitCast] " ++)

--------------------------------------------------------------------------------
-- * Split Semantics
--------------------------------------------------------------------------------
codegenSplitEmitMaybe
  :: ( Has (Error String) sig m
     )
  => Maybe SplitScheme
  -> m [Stmt']
codegenSplitEmitMaybe = maybe (return []) codegenSplitEmit

-- | Generate emit variables and split operations from a given split scheme.
-- FIXME: implement split for phases as well
codegenSplitEmit
  :: ( Has (Error String) sig m
     )
  => SplitScheme
  -> m [Stmt']
codegenSplitEmit
  ss@SplitScheme { schQty=qty
                 , schROrigin=rOrigin@(Range x left _)
                 , schRTo=rTo
                 , schRsRem=rsRem
                 , schVEmitOrigin=vEmitOrigin
                 , schVsEmitAll=vEmitAll
                 } =
  -- trace ("codegenSplitEmit: " ++ show ss) >>
  case qty of
    t | t `elem` [ TNor, THad, TEN01 ] -> do
      let offset e = reduce $ EOp2 OSub e left
      let stmtsSplit =
            [ [ (vEmitNew ::=:) $
                EEmit (ESlice (EVar vEmitOrigin) (offset el) (offset er))
              , infoWeirdAssertionNeeded
              , SAssert (EOp2 OEq
                          (EEmit (ESlice (EVar vEmitOrigin) (offset el) (offset er)))
                          (EEmit (ESlice (EVar vEmitNew) 0 (reduce (er - el)))))
              ]
            | (vEmitNew, Range _ el er) <- zip (schVsEmitAll ss) (rTo : rsRem) ]
      return . concat $ stmtsSplit
    _    ->
      throwError @String $ printf "Splitting a %s partition is unsupported." (show qty)
  where
    infoWeirdAssertionNeeded =
      qComment "I have no idea why this assertion about equality is necessary...."

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
  (++) <$> codegenSplitEmitMaybe sS <*> codegenCastEmitMaybe sC


--------------------------------------------------------------------------------
-- * Cast Semantics
--------------------------------------------------------------------------------
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
      | (vOld, vNew, rCast) <- zip3 vsOldEmits vsNewEmit rsCast ]
  where
    -- | Consume /from/ and /to/ types and return a function that consumes a
    -- range and emit a specialized cast operator based on the property of the
    -- range passed in
    mkOp TNor TEN   = return $ const "CastNorEN"
    mkOp TNor TEN01 = return $ const "CastNorEN01"
    mkOp TNor THad  = return $ const "CastNorHad"
    mkOp THad TEN01 = return $ \r -> case sizeOfRangeP r of
      Just 1 -> "CastHadEN01'1"
      _      -> "CastHadEN01"
    mkOp _    _     = throwError err
    err :: String = printf "Unsupport cast from %s to %s." (show qtOld) (show qtNew)

-- | Convert quantum type of `s` to `newTy` and emit a cast statement with a
-- provided `op`
castWithOp
  :: ( Has (Error String) sig m
     , GensymWithState sig m
     )
  => String -> Locus -> QTy -> m [Stmt']
castWithOp op s newTy =
  do
    schemeC <- retypePartition s newTy
    let CastScheme{ schVsOldEmit=vsOldEmits , schVsNewEmit=vsNewEmit} = schemeC
    let partitionTy = (qty s, degrees s)
    -- assemble the emitted terms
    return . concat $
      [ [ qComment $ "Cast " ++ show partitionTy ++ " ==> " ++ show newTy
        , (::=:) vNew $ EEmit (op `ECall` [EEmit $ EDafnyVar vOld])
        ]
      | (vOld, vNew) <- zip vsOldEmits vsNewEmit ]


-- | Cast the given partition to EN type!
castPartitionEN
  :: ( Has (Error String) sig m
     , GensymWithState sig m
     )
  => Locus -> m [Stmt']
castPartitionEN st@Locus{loc=locS, part=s, qty=qtS} = do
  case qtS of
    TNor -> castWithOp "CastNorEN" st TEN
    THad -> castWithOp "CastHadEN" st TEN
    TEN -> throwError' $
      printf "Partition `%s` is already of EN type." (show st)
    TEN01 -> throwError' $
      printf "Casting %s to TEN is expensive therefore not advised!" (show qtS)

-- | Duplicate the data, i.e. sequences to be emitted, by generating statements
-- that duplicates the data as well as the correspondence between the range
-- bindings, emitted variables from the fresh copy and the original emitted
-- varaibles.
--
-- However, this does not add the generated symbols to the typing environment or
-- modifying the existing bindings!
--
dupState
  :: ( Has (Error String) sig m
     , GensymWithState sig m
     , Has (Reader IEnv) sig m
     , Has Trace sig m
     )
  => Partition -> m ([Stmt'], [(Var, Var)])
dupState s' = do
  Locus{loc=locS, part=s, qty=qtS, degrees=ptys} <- resolvePartition s'
  let rs = ranges s
  -- generate a set of fresh emit variables as the stashed partition
  -- do not manipulate the `emitSt` here
  vsEmitFresh <- genEDByRangeSansPhase qtS `mapM` rs >>= visitEDsBasis
  -- the only place where state is used!
  vsEmitPrev  <- findEmitBasesByRanges rs
  let comm = qComment "Duplicate"
  let stmts = [ (::=:) vEmitFresh (EVar vEmitPrev)
              | (vEmitFresh, vEmitPrev) <- zip vsEmitFresh vsEmitPrev ]
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

