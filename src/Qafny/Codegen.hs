{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TupleSections #-}

module Qafny.Codegen where

import           Qafny.AST
import           Qafny.Transform
import           Qafny.Typing

import           Control.Monad.RWS
import           Control.Monad.Except
import           Control.Lens
import qualified Data.Map.Strict as Map 
import qualified Data.Set as Set 
import           Control.Applicative (Applicative(liftA2))

--------------------------------------------------------------------------------
-- | Codegen 
--------------------------------------------------------------------------------

class Codegen a where
  -- | Augmentation: perform typecheck over `a` and rewrite `a` into `[a]`
  aug :: a -> Transform [a]

instance Codegen AST where
  aug ast = do
    let k = Map.fromList (collectMethodTypes ast)
    let prelude =
          [ QDafny "include \"../../external/QPreludeUntyped.dfy\""
          , QDafny "// target Dafny version: 3.12.0"
          , QDafny "abstract module QafnyDefault {"
          , QDafny "import opened QPreludeUntyped"
          , QDafny ""
          ]
    let postscript =
          [ QDafny "}" ]
    main <- local (kEnv %~ Map.union k) $ mapM aug ast
    return $ prelude : main ++ [postscript]

instance Codegen Toplevel where
  aug q@(QMethod v bds rts rqs ens block) =
    do
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
  aug (Block stmts) =
    do
      kSt' <- use kSt -- push a kindSt
      stmts' <- mapM aug stmts
      kSt .= kSt' -- restore when exiting the block
      return [Block $ concat stmts'] -- return the result of the block

instance Codegen Stmt where
  aug s@(SVar (Binding v t) eM) =
    do
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
          mkSVar (v', e', t') = SVar (Binding v t') $ Just e'
  aug (SApply s EHad) = 
    do qt <- typing s
       opCast <- opCastHad qt
       coercionWithOp opCast qt THad s
    where
      opCastHad :: QTy -> Transform String
      opCastHad TNor = return "CastNorHad"
      opCastHad t = throwError $ "type `" ++ show t ++ "` cannot be casted to Had type"
  -- aug (SApply s e@(ECl _ _)) =
  --   do qt <- typing s
  --      checkSubtypeQ TCH qt
  --      throwError "I need to finish the cast part first"
  aug (SIf e seps b) =
    do
      (s, t) <- typingGuard e
      sDup <- withGuardType t
      -- I need to first gather all sessions that are going to be mutated here.
      return [SEmit $ SBlock (Block sDup)]
    where
      withGuardType TNor = throwError "Nor type for gurad?"
      withGuardType THad =
        do
          let freeSession = leftSessions . inBlock $ b
          prelude <- mapM preludeIf freeSession
          -- TODO: implement separate checker here:
          -- only `separated` sessions can be on the LHS of `aug`
          -- I could add a checker on the Reader.
          -- another point is that you should not allocate any new qubits in
          -- if. therefore, some freshness checker needs to be implemented at
          -- the method call to ensure that
          stmtsBody <- aug b
          mergeBody <- mapM mergeIf prelude <&> concat
          let dupStmts = concatMap (^. _3) prelude
          return $ dupStmts ++ concatMap inBlock stmtsBody ++ concat mergeBody
      withGuardType TCH =
        throwError "Do the split mechanism here, map will not be generic enough"
      -- Convert those session to CH type if not and generate split statement
      -- for every session
      preludeIf :: Session -> Transform (Ty, Session, [Stmt], BiRangeZipper a)
      preludeIf s =
        do
          ty <- typing s
          coerStmts <- coercionCH ty s
          tyEmit <- only1 $ typingEmit s
          (stashed, dupStmts, zipper) <- dupSession tyEmit s
          return (tyEmit, stashed, coerStmts ++ dupStmts, zipper)
      -- Generate merge statement for every session
      mergeIf :: (Ty, Session, [Stmt], BiRangeZipper [Stmt]) -> Transform [[Stmt]]
      mergeIf (tyEmit, _, _, zipper) = zipper $ mergeRange2 tyEmit
      -- Generate the merge statement of one paired range
      mergeRange2 :: Ty -> Range -> Range -> Transform [Stmt]
      mergeRange2 tyEmit rMain@(Range vMain _ _) rStash@(Range vStash _ _) =
        liftA2
          ( \vMainEmit vStashEmit ->
              [SAssign vMainEmit (EOp2 OAdd (EVar vMainEmit) (EVar vStashEmit))]
          )
          (findSym vMain tyEmit)
          (findSym vStash tyEmit)
  aug s = return [s]

type BiRangeZipper a = (Range -> Range -> Transform a) -> Transform [a]

-- | Generate declarations to duplicate session data
-- TODO: do I really need to generate new emitted symbols?
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
  -- probably I need some nice type to enforce this
  aug (v, e@(EOp2 ONor e1 e2), t@(TQ TNor)) = do
    let es =
          [ EEmit $ EMakeSeq TNat e1 (ELambda wild e2) -- basis
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
only1 :: Show a => Transform [a] -> Transform a
only1 = (=<<) $
  \case
    [x] -> return x
    e -> throwError $ "[only1]: " ++ show e ++ "is not a singleton"


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

-- | For a given well-typed session, cast its type with the given op and return
-- the statements for the cast
-- TODO: with phase calculus [coercionWithOp] will need to take a list of `Op`s
coercionWithOp :: String -> QTy -> QTy -> Session -> Transform [Stmt]
coercionWithOp castOp sessionTy newTy s =
  do
    tNewEmit <- only1 $ typing newTy
    let vMetas = varFromSession s
    -- get the previous types
    tOldEmit <- only1 $ typing sessionTy
    vOldEmits <- mapM (`findSym` tNewEmit) vMetas
    -- update with new ones
    sSt %= (at s ?~ newTy) --  todo: allow splits/change states when typing
    -- update the kind state for each (probably not necessary)
    foldM_ (\_ v -> kSt %= (at v ?~ TQ newTy)) () vMetas
    -- remove all old symbols and generate new symbols
    rbSt %= (`Map.withoutKeys` (Set.fromList $ map (,tOldEmit) vMetas))
    vNewEmits <- mapM (`gensym` tNewEmit) vMetas
    -- assemble the emitted terms
    return $
      concat
        [ [ SDafny $ "// Cast " ++ show sessionTy ++ " ==> " ++ show newTy
          , SAssign vNew $ EEmit (castOp `ECall` [EEmit $ EDafnyVar vOld])
          ]
        | (vOld, vNew) <- zip vOldEmits vNewEmits
        ]

--------------------------------------------------------------------------------
-- | Wrapper 
--------------------------------------------------------------------------------
codegen :: AST -> Production AST
codegen = (_1 %~ fmap concat) . runTransform . aug
