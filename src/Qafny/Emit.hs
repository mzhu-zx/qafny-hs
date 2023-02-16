{-# language FlexibleContexts, FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Qafny.Emit where

import           Qafny.AST

import           Data.Text.Lazy(Text)
import qualified Data.Text.Lazy.Builder as TB
import           Control.Monad.Reader

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
  build TNat     = build "nat"
  build TInt     = build "int"
  build TBool    = build "bool"
  build (TQ q)   = build q
  build (TSeq t) = build "seq<" <> build t <> build ">"
  build _        = undefined

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
          buildStmt (SCall e es) = build e <> withParen (byComma es)
          buildStmt e = build "// undefined builder for Stmt : " <> build (show e)

instance DafnyPrinter Exp where
  build (ENum n) = build $ show n
  build (EVar v) = build v
  build (EEmit e) = build e
  build _ = undefined

instance DafnyPrinter EmitExp where
  build (ELambda v e) = build v <> build " => " <> build e
  build (EMakeSeq ty e ee) =
    build "seq<" <> build ty <> build ">" <>
    withParen (build e <> build ", " <> build ee)
  build (EDafnyVar s) = build s
  build (ECall e es) = build e <> withParen (byComma es)

buildConds :: String -> [Exp] -> Builder
buildConds s = foldr (\x xs -> build s <> build x <> build '\n' <> xs) (build "")

texify :: DafnyPrinter a => a -> Text
texify = TB.toLazyText . flip runReader 0 . doBuild . build
