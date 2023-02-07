{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Qafny.AST where

import           Data.Text.Lazy(Text)
import qualified Data.Text.Lazy.Builder as TB
import           Control.Monad.Reader


data Ty = TNat
        | TInt
        | TBool
        | TSeq Ty
        | TQ QTy
        | TMethod [Ty] [Ty] -- parameter and return types
        deriving (Show, Eq, Ord)

data QTy = TNor
         | THad
         | TCH
         deriving (Show, Eq, Ord)

type Var = String

data Binding = Binding Var Ty
             deriving (Show, Eq, Ord)

type Bindings = [Binding]

data Op2 = OAnd
         | OOr
         | OAdd
         | OMul
         | OMod
         | ONor
         deriving (Show, Eq, Ord)

data Op1 = ONot
         deriving (Show, Eq, Ord)

data Exp = ENum Int
         | EVar Var
         | EHad
         | EQFT
         | ERQFT
         | EMea Var
         | EBool Bool
         | EApp Var Exp
         | EOp1 Op1 Exp
         | EOp2 Op2 Exp Exp
         | EForall Binding (Maybe Exp) Exp
         | EDafny String
         deriving (Show, Eq, Ord)

type Returns = [Binding]

data Conds = Requires Exp
           | Ensures Exp

type Requires = [Exp]
type Ensures = [Exp]

newtype Block = Block { inBlock :: [Stmt] }
  deriving (Show, Eq)

data Toplevel = QMethod Var Bindings Returns Requires Ensures Block
              | QDafny String
              deriving (Show, Eq)

data Range = Ran Var Exp Exp 
        deriving (Show, Eq, Ord)

newtype Session = Session [Range]
  deriving (Show, Eq, Ord)

data Stmt = SAssert Exp
          | SCall Exp [Exp]
          | SVar Binding (Maybe Exp)
          | SAssign Var Exp
          | SApply Session Exp
          | SDafny String
          | SIf Exp Block
          deriving (Show, Eq)

type AST = [Toplevel]


-------------------- Builder --------------------

newtype Builder_ a = Builder { doBuild :: Reader Int a }
  deriving (Functor, Applicative, Monad, (MonadReader Int))
type Builder = Builder_ TB.Builder

instance Semigroup Builder where
  (<>) = liftM2 (<>)

instance Monoid Builder where
  mempty = return mempty

line :: Builder
line = return $ TB.singleton '\n'

space :: Builder
space = return $ TB.singleton ' '

withIncr2 :: Builder -> Builder
withIncr2 = local (+ 2)

getIndent :: Builder_ String
getIndent = do n <- ask
               return $ replicate n ' '

withParen :: Builder -> Builder
withParen b = build '(' <> b <> build ')'

withBrace :: Builder -> Builder
withBrace b = build "{\n" <> b <> build "}\n"

byComma :: DafnyPrinter a => [a] -> Builder
byComma [] = mempty
byComma (x:xs) = foldl (\ys y -> ys  <> build ", " <> build y) (build x) xs

byLine :: DafnyPrinter a => [a] -> Builder
byLine = foldr (\y ys -> build y <> build "\n" <> ys) mempty


class DafnyPrinter a where
  build :: a -> Builder

instance DafnyPrinter Char where
  build = return . TB.singleton
  
instance DafnyPrinter String where
  build = return . TB.fromString

instance DafnyPrinter AST where
  build = byLine

instance DafnyPrinter Ty where
  build TNat = build "nat"
  build (TQ q) = build q
  build _    = undefined 

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
    withParen (byComma bds) <> 
    buildRets rets <> line <>
    buildConds "requires" reqs <> 
    buildConds "ens" reqs <>
    build block
    where buildRets [] = mempty
          buildRets r  = build " returns " <> withParen (byComma bds)

instance DafnyPrinter Block where
  build = withBrace . withIncr2 . byLine . inBlock

instance DafnyPrinter Stmt where
  build s = do i <- getIndent
               build i <> buildStmt s <> build ';'
    where buildStmt :: Stmt -> Builder
          buildStmt (SVar bd Nothing) = build "var " <> build bd
          buildStmt (SVar bd (Just e)) = build "var " <> build bd <>
                                         build " := " <> build e
          buildStmt (SAssign v e) = build v <> build " := " <> build e
          buildStmt e = build "// undefined builder for Stmt : " <> build (show e)

instance DafnyPrinter Exp where
  build (ENum n) = build $ show n
  build (EVar v) = build v
  build _ = undefined

buildConds :: String -> [Exp] -> Builder
buildConds s = foldr (\x xs -> build s <> build x <> build '\n' <> xs) (build "")

texify :: DafnyPrinter a => a -> Text
texify = TB.toLazyText . flip runReader 0 . doBuild . build
