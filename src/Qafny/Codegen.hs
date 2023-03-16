{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TupleSections #-}

module Qafny.Codegen where

import           Qafny.AST
import           Qafny.Transform
import           Qafny.Typing

import           Control.Monad.RWS
import           Control.Monad.Except
import           Control.Lens
import qualified Data.Map.Strict as Map 
import           Control.Applicative (Applicative(liftA2))
import           Data.Maybe (listToMaybe)

--------------------------------------------------------------------------------
-- | Codegen 
--------------------------------------------------------------------------------

class Codegen a where
  -- | Augmentation: perform typecheck over `a` and rewrite `a` into `[a]`
  aug :: a -> Transform [a]

instance Codegen AST where
  -- TODO: make `../../external` configable
  aug ast = do
    let k = Map.fromList (collectMethodTypes ast)
    let prelude =
          [ QDafny "include \"../../external/QPreludeUntyped.dfy\""
          , QDafny "include \"../../external/libraries/src/Collections/Sequences/Seq.dfy\""
          , QDafny "include \"../../external/libraries/src/NonlinearArithmetic/Power2.dfy\""
          , QDafny ""
          , QDafny "// target Dafny version: 3.12.0"
          , QDafny "abstract module QafnyDefault {"
          , QDafny "import opened QPreludeUntyped"
          , QDafny "import opened Seq"
          , QDafny "import opened Power2"
          , QDafny ""
          ]
    let postscript =
          [ QDafny "}" ]
    main <- local (kEnv %~ Map.union k) $ mapM aug ast
    return $ prelude : main ++ [postscript]

instance Codegen Toplevel where
  aug q@(QMethod v bds rts rqs ens block) = do
    tEnv <- asks $ appkEnvWithBds bds
    -- sync kState with kEnv because when handling Stmts, environment becomes
    -- a state!
    kSt .= tEnv ^. kEnv
    (block', eVts) <- listen $ only1 $ local (const tEnv) $ aug block
    let stmtsDeclare = map (\(s, t) -> SVar (Binding s t) Nothing) eVts
    let totalBlock =
          [SDafny "// Forward Declaration"]
            ++ stmtsDeclare
            ++ [ SDafny ""
               , SDafny "// Method Definition"
               ]
            ++ inBlock block'
    return [QMethod v bds rts rqs ens (Block totalBlock)]
  aug q@(QDafny _) = return [q]

instance Codegen Block where
  aug (Block stmts) = do
    kSt' <- use kSt -- push a kindSt
    stmts' <- mapM aug stmts
    kSt .= kSt' -- restore when exiting the block
    return [Block $ concat stmts'] -- return the result of the block

instance Codegen Stmt where
  aug s@(SVar (Binding v t) eM) = do
    -- TODO: make a special case to allow `SVar` emission for uncured terms
    kSt %= (at v ?~ t)
    doE eM
    where
      doE :: Maybe Exp -> Transform [Stmt]
      doE Nothing = return [s]
      doE (Just e) =
        do
          te <- typing e
          checkSubtype t te -- check if `t` agrees with the type of `e`
          vets <- aug (v, e, t)
          return $ map mkSVar vets
        where
          mkSVar :: (Var, Exp, Ty) -> Stmt
          mkSVar (vEmitted, e', tEmitted) = SAssign vEmitted e'
  aug (SApply s EHad) = do
    qt <- typing s
    opCast <- opCastHad qt
    coercionWithOp opCast qt THad s
    where
      opCastHad :: QTy -> Transform String
      opCastHad TNor = return "CastNorHad"
      opCastHad t = throwError $ "type `" ++ show t ++ "` cannot be casted to Had type"
  aug (SApply s@(Session ranges) e@(EEmit (ELambda {}))) = do
    qt <- typing s
    checkSubtypeQ TCH qt
    emitVs <- mapM (`findSymByRangeQTy` qt) ranges
    return $ mkMapCall `map` emitVs
    where
      mkMapCall v = v `SAssign` EEmit (ECall "Map" [e, EVar v])
  aug (SIf e seps b) = do
    (s, t) <- typingGuard e
    sIf <- withGuardType s t
    return [SEmit $ SBlock (Block sIf)]
    where
      withGuardType _ TNor = throwError "Nor type for gurad?"
      withGuardType sGuard THad = do
        -- Requirement: all sessions in the body should be in the same session
        freeSession <- resolveSessions . leftSessions . inBlock $ b
        prelude <- preludeIf freeSession
        stmtsBody <- aug b
        vCard <- getStashedEmitVar prelude
        mergeGuardStmt <- mergeGuard vCard freeSession sGuard
        mergeBody <- mergeIf prelude <&> concat
        let dupStmts = (^. _3) prelude
        return $ dupStmts ++ concatMap inBlock stmtsBody ++ mergeBody ++ mergeGuardStmt
      withGuardType _ TCH =
        throwError "Do the split mechanism here, map will not be generic enough"
      -- Convert those session to CH type if not and generate split statement
      -- for every session
      preludeIf :: Session -> Transform (Ty, Session, [Stmt], BiRangeZipper a)
      preludeIf s = do
        (castStmts, tyEmit) <- coercionSessionCH s
        (stashed, dupStmts, zipper) <- dupSession tyEmit s
        return (tyEmit, stashed, castStmts ++ dupStmts, zipper)
      -- Generate merge statement for every session
      mergeIf :: (Ty, Session, [Stmt], BiRangeZipper [Stmt]) -> Transform [[Stmt]]
      mergeIf (tyEmit, _, _, zipper) = zipper $ mergeRange2 tyEmit
      -- Merge the guard into the session
      -- Question: should the guard be visible to the body? I don't think so.
      -- If that should be visible, then the cast should happen beforehand.
      -- The semantics of multiple sessions in one body is unclear so far
      mergeGuard :: Var -> Session -> Session -> Transform [Stmt]
      mergeGuard vCard bodySession s = do
        -- grab an arbitrary range from the session
        let stateCard = EEmit . ECard . EVar $ vCard
        -- in Had type, `retypeSession1` should not fail, unless there's some
        -- other design choices: the more you want, the more messy the entire
        -- system will be
        (vOldEmit, _, vNewEmit, tNewEmit) <- retypeSession1 s TCH
        mergeSessionType bodySession s
        -- TODO: in phase calculus, the sign of phases will depend on
        -- `vNewEmit
        tNew <-
          handleWith
            (throwError $ "`" ++ show tNewEmit ++ "` is not a sequence type")
            ( return $ case tNewEmit of
                TSeq ty -> Just ty
                _ -> Nothing
            )
        return
          [ SDafny "// Body Session + Guard Session"
          , vNewEmit
              `SAssign` EOp2
                OAdd
                (EEmit $ EMakeSeq tNew stateCard $ constExp (ENum 0))
                (EEmit $ EMakeSeq tNew stateCard $ constExp (ENum 1))
          ]
      getStashedEmitVar :: (Ty, Session, [Stmt], BiRangeZipper a) -> Transform Var
      getStashedEmitVar (_, s@(Session rs), _, _) =
        case listToMaybe rs of
          Nothing -> throwError "Empty Session?"
          Just r -> findSymByRangeQTy r TCH
  aug (SFor idx boundl boundr eguard invs seps body) = do
    (s, t) <- typingGuard eguard
    sFor <- augByGuardType t s
    return [SEmit $ SBlock (Block sFor)]
    where
      augByGuardType TNor _ =
        throwError "This is an easy case: apply on states with 1"
      augByGuardType THad sGrd = do
        (sGrdTtl, eGrdRng) <- loopSession sGrd boundl boundr
        -- collect the sessions in the body and cast them to CH first
        freeSession <- resolveSessions . leftSessions . inBlock $ body
        (castStmts, tyEmit) <- coercionSessionCH freeSession
        -- create a fresh CH metavariable for the guard session1
        -- interestingly, the dup semantics works here!
        tyGuardEmit <- only1 $ typing THad
        (sGrdFrsh, sGrdDupStmts, zGrd) <- dupSession tyGuardEmit sGrdTtl
        -- cast `sGrd` to CH type at meta-level
        (_, _, vGrdNowEmits, tGrdNowEmits) <- retypeSession sGrd TCH
        vGrdNowEmit <- only1 $ return vGrdNowEmits
        let sGrdResetStmt = SAssign vGrdNowEmit (EEmit EMtSeq)
        -- now, both `freeSession` and the new guard sessions has been
        -- prepared
        -- Start building the new body:
        -- 1. split semantics again over freeSessions
        (sStashedBdy, dupSBdy, zipperBody) <- dupSession tyEmit freeSession
        -- 2. compile the body
        loopBody <- aug body
        -- 3. compile the merge of both body and the guard
        mergeBodyStmts <- zipperBody $ mergeRange2 tyEmit
        let mergeGuardStmt = addCHHad1 vGrdNowEmit idx
        -- 4. put them together
        let prelude = castStmts ++ sGrdDupStmts ++ [sGrdResetStmt]
        let innerFor =
              SEmit $
                SForEmit idx boundl boundr [] $
                  Block
                    ( dupSBdy
                        ++ (SEmit . SBlock <$> loopBody)
                        ++ concat mergeBodyStmts
                        ++ [mergeGuardStmt]
                    )
        return $ prelude ++ [innerFor]
      augByGuardType TCH _ =
        throwError "This is a tricky, perhaps only makes sense in GHZ-like bitvector?"
  aug s = return [s]

type BiRangeZipper a = Zipper Range a

{- | Duplicate session, generate duplication statements and a zipper
 the zipper returned zips over the newly generated ranges and the old ones

 FIXME: do I really need to emit new symbols?
 return: (stashed, dupStmts, zipper)
-}
dupSession :: Ty -> Session -> Transform (Session, [Stmt], BiRangeZipper a)
dupSession tEmit s =
  do
    stashed@(Session newRs) <- gensymSessionMeta s
    let Session oldRs = s
    stmts <- zipWithM mkDecls newRs oldRs
    return (stashed, stmts, \f -> zipWithM f oldRs newRs)
  where
    mkDecls (Range newR _ _) (Range oldR _ _) =
      liftA2
        (\vOldEmit vNewEmit -> SAssign vNewEmit (EVar vOldEmit))
        (findSym oldR tEmit)
        (gensym newR tEmit)

instance Codegen (Var, Exp, Ty) where
  -- Specialized instance for variable declaration
  -- note: the type checking of `Exp` is caller's responsibility
  -- probably I need some nice types to enforce this
  aug (v, e@(EOp2 ONor e1 e2), t@(TQ TNor)) = do
    let es =
          [ EEmit $ EMakeSeq TNat e1 $ constExp e2 -- basis
          ] -- todo: phases
    ts <- aug t
    -- check arities to make sure I didn't mess up
    unless (length ts == length es) $
      throwError $
        "augmented type and expressions are of differnt length"
          ++ "\n  Types: "
          ++ show ts
          ++ "\n  Expression: "
    vs <- gensymTys ts v
    -- update state mappings
    let vRange = Range v (ENum 0) e1
        vSession = session1 vRange
    xSt %= (at v ?~ vSession)
    sSt %= (at vSession ?~ TNor)
    kSt %= (at v ?~ TQ TNor)
    -- done
    return $ zip3 vs es ts
  aug (v, e@(EOp2 ONor e1 e2), _) =
    throwError "Internal: Attempt to create a Nor session that's not of nor type"
  aug ve = return [ve]

instance Codegen Exp where
  -- instance for conventional expression
  -- note: the type checking of `Exp` is caller's responsibility
  -- probably I need some nice type to enforce this
  aug e = return [e]

instance Codegen Ty where
  aug (TQ t) = typing t -- TODO complete the phase type here
  aug e = return [e]

--------------------------------------------------------------------------------
-- | Helpers 
--------------------------------------------------------------------------------

-- | Given a well-typed full session (s :: τ1), emit the statement and cast it
-- to CH type
-- 
-- FIXME: Emitted variable declaration should appear outside the block,
-- there could be some problem in the current implementation
-- Solution: write used emission variables in the writer and forward the
-- declaration

coercionCH :: QTy -> Session -> Transform [Stmt]
coercionCH TCH = const $ return []
coercionCH TNor = coercionWithOp "CastNorCH10" TNor TCH
coercionCH THad = coercionWithOp "CastHadCH10" TNor TCH


coercionSessionCH :: Session -> Transform ([Stmt], Ty)
coercionSessionCH s =
  do
    ty <- getSessionType s
    coerStmts <- coercionCH ty s
    tyEmit <- only1 $ typingEmit s
    return (coerStmts, tyEmit)


-- | For a given well-typed session, cast its type with the given op and return
-- the statements for the cast
-- TODO: with phase calculus [coercionWithOp] will need to take a list of `Op`s
coercionWithOp :: String -> QTy -> QTy -> Session -> Transform [Stmt]
coercionWithOp castOp sessionTy newTy s =
  do
    (vOldEmits, tOldEmit, vNewEmits, tNewEmit) <- retypeSession s newTy
    -- assemble the emitted terms
    return $
      concat
        [ [ SDafny $ "// Cast " ++ show sessionTy ++ " ==> " ++ show newTy
          , SAssign vNew $ EEmit (castOp `ECall` [EEmit $ EDafnyVar vOld])
          ]
        | (vOld, vNew) <- zip vOldEmits vNewEmits
        ]

-- | Generate the merge statement of one paired range
mergeRange2 :: Ty -> Range -> Range -> Transform [Stmt]
mergeRange2 tyEmit rMain@(Range vMain _ _) rStash@(Range vStash _ _) =
  do
    stmts <-
      liftA2
        ( \vMainEmit vStashEmit ->
            [SAssign vMainEmit (EOp2 OAdd (EVar vMainEmit) (EVar vStashEmit))]
        )
        (findSym vMain tyEmit)
        (findSym vStash tyEmit)
    -- recycle stashed variables
    deallocOrphan vStash tyEmit
    return stmts

-- | Merge semantics of a Had qubit into one CH emitted state
-- uses the name of the emitted seq as well as the index name

addCHHad1 :: Var -> Var -> Stmt
addCHHad1 vEmit idx =
  SAssign vEmit $
    EOp2 OAdd (EVar vEmit) (EEmit $ ECall "Map" [eLamPlusPow2, EVar vEmit])
  where
    vfresh = "x__lambda"
    eLamPlusPow2 =
      EEmit $
        ELambda vfresh $
          EOp2 OAdd (EVar vfresh) (EEmit (ECall "Pow2" [EVar idx]))


--------------------------------------------------------------------------------
-- | Wrapper 
--------------------------------------------------------------------------------
codegen :: AST -> Production AST
codegen = (_1 %~ fmap concat) . runTransform . aug
