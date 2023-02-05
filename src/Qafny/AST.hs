{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Qafny.AST where

import           Data.Text.Lazy(Text)
import qualified Data.Text.Lazy.Builder as TB
import           Control.Monad.Reader
-- import           GHC.List(foldl')

data Ty = TNat
        | TInt
        | TBool
        | TSeq Ty
        | TQ QTy
        | TMethod Var [Ty] [Ty] -- parameter and return types
        deriving (Show, Eq)

data QTy = TNor
         | THad
         | TCH
         deriving (Show, Eq)

type Var = String

data Binding = Binding Var Ty
             deriving (Show, Eq)

type Bindings = [Binding]

data Op2 = OAnd
         | OOr
         deriving (Show, Eq)

data Op1 = ONot
         deriving (Show, Eq)

data Exp = ENum Int
         | EId Var
         | EBool Bool
         | EOp1 Op1 Exp
         | EOp2 Op2 Exp Exp
         | EForall Binding (Maybe Exp) Exp
         | EDafny String
         deriving (Show, Eq)

type Returns = [Binding]

data Conds = Requires Exp
           | Ensures Exp

type Requires = [Exp]
type Ensures = [Exp]

newtype Block = Block [Stmt]
  deriving (Show, Eq)

data Toplevel = QMethod Var Bindings Returns Requires Ensures Block
              | QDafny String
              deriving (Show, Eq)
              -- | QFunction Var Bindings Ty

data Stmt = SAssert Exp
          | SCall Exp [Exp] -- invoking method
          | SVar Binding (Maybe Exp)
          | SAssign Var Exp
          | SDafny String
          | SIf Exp Block
          | SApply Var Exp -- invoke quantum op
          deriving (Show, Eq)

type AST = [Toplevel]

newtype Builder_ f = Builder { doBuild :: Reader Int f}
  deriving (Functor, Applicative, Monad, (MonadReader Int))

type Builder = Builder_ TB.Builder

instance Semigroup Builder where
  (<>) = liftM2 (<>)

instance Monoid Builder where
  mempty = pure mempty

line :: Builder
line = return $ TB.singleton '\n'

space :: Builder
space = return $ TB.singleton ' '


class DafnyPrinter a where
  build :: a -> Builder

byComma :: DafnyPrinter a => [a] -> Builder
byComma [] = mempty
byComma (x:xs) = foldl (\ys y -> ys  <> build ", " <> build y) (build x) xs

withParens :: Builder -> Builder
withParens s = build '(' <> s <> build ')'

withBraces :: Builder -> Builder
withBraces s = build "{\n" <> s <> build "}\n"

byCat :: DafnyPrinter a => [a] -> Builder
byCat = foldr ((<>) . build) mempty

withIncr2 :: Builder -> Builder
withIncr2 = local (+ 2)

getIndent :: Builder_ String
getIndent = do n <- ask
               return $ replicate n ' '

instance DafnyPrinter Char where
  build = return . TB.singleton
  
instance DafnyPrinter String where
  build = return . TB.fromString

instance DafnyPrinter AST where
  build = foldr (\x xs -> build x <> line <> xs) line

instance DafnyPrinter Ty where
  build TNat = build "nat"
  build (TQ t) = build t
  build e = build "// undefined: " <> build (show e) <> build ";\n"
  
instance DafnyPrinter QTy where
  build TNor = build "nor"
  build THad = build "had"
  build TCH = build "ch"

instance DafnyPrinter Binding where
  build (Binding x t) = build x <> build " : " <> build t

instance DafnyPrinter Toplevel where
  build (QDafny s) = build s 
  build (QMethod idt bds rets reqs ens block) =
    build "method" <> space <>
    build idt <> space <>
    withParens (byComma bds) <>
    buildRets rets <> line <>
    buildRequires reqs <> 
    buildEnsures ens <>
    build block
    where buildRets [] = mempty
          buildRets r  = build " returns " <>
                         withParens (byComma r)

instance DafnyPrinter Stmt where
  build s = do i <- getIndent
               build i <> buildStmt s <> build ";\n"
    where
      buildStmt (SVar bd (Just e)) = build "var " <> build bd <> build " := " <> build e
      buildStmt (SVar bd _) = build "var " <> build bd
      buildStmt (SAssert e) = build "assert " <> build e
      buildStmt (SApply x e) = build x <> build " *= " <> build e
      buildStmt (SCall e es) = build e <> withParens (byComma es) 
      buildStmt e = build "// undefined: " <> build (show e)

instance DafnyPrinter Exp where
  build (ENum n) = build $ show n
  build (EId s) = build s
  build e = build "// undefined: " <> build (show e)
  

instance DafnyPrinter Block where
  build (Block b) = withBraces (withIncr2 (byCat b))


buildRequires :: Requires -> Builder
buildRequires = buildConds "requires"

buildEnsures :: Ensures -> Builder
buildEnsures = buildConds "ensures"

buildConds :: String -> Requires -> Builder
buildConds s = foldr (\x xs -> build s <> build x <> build '\n' <> xs) mempty


texify :: DafnyPrinter a => a -> Text
texify = TB.toLazyText .  flip runReader 0 . doBuild . build
