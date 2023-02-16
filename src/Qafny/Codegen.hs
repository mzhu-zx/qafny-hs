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
          , -- , QDafny "import opened QPreludeUntyped"
            QDafny ""
          ]
    main <- local (kEnv %~ Map.union k) $ mapM aug ast
    return $ prelude : main

instance Codegen Toplevel where
  aug q@(QMethod v bds rts rqs ens block) =
    do
      tEnv <- asks $ appkEnvWithBds bds
      -- sync kState with kEnv because when handling Stmts, environment becomes
      -- a state!
      kSt .= tEnv ^. kEnv
      block' <- only1 $ local (const tEnv) $ aug block
      return [QMethod v bds rts rqs ens block']
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
      mkSVar (v', e', t') = SVar (Binding v' t') (Just e')
  aug (SApply s EHad) =
    -- todo: `tNewEmit` and `tOldEmit` new assumes only one, need a mapping when
    -- extending phase calculus
    do
      let newTy = THad
      qt <- typing s
      castOp <- opCastHad qt
      tNewEmit <- only1 $ typing newTy
      let vMetas = varFromSession s
      -- get the previous types
      tOldEmit <- only1 $ typing qt
      vOldEmits <- mapM (`findSym` tNewEmit) vMetas
      -- update with new ones
      sSt %= (at s ?~ newTy) --  todo: allow splits/change states when typing
      -- update the kind state for each (probably not necessary)
      foldM_ (\_ v -> kSt %= (at v ?~ TQ newTy)) () vMetas
      -- remove all old symbols and generate new symbols
      rbSt %= (`Map.withoutKeys` (Set.fromList $ map (,tOldEmit) vMetas))
      vNewEmits <- mapM (`gensym` tNewEmit) vMetas
      -- assemble the emitted terms
      return
        [ SVar (Binding vNew tNewEmit) $
          Just $
            EEmit (castOp `ECall` [EEmit $ EDafnyVar vOld])
        | (vOld, vNew) <- zip vOldEmits vNewEmits
        ]
   where
    opCastHad :: QTy -> Transform String
    opCastHad TNor = return "CastNorHad"
    opCastHad t = throwError $ "type `" ++ show t ++ "` cannot be casted to Had type"
  aug s = return [s]



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
    let vRange = Ran v (ENum 0) e1
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

--------------------------------------------------------------------------------
-- | Wrapper 
--------------------------------------------------------------------------------
codegen :: AST -> (Either String AST, TState, ())
codegen = (_1 %~ fmap concat) . runTransform . aug
