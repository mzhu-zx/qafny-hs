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

getIndent :: Builder
getIndent = do n <- ask
               build $ replicate n ' '

withParen :: Builder -> Builder
withParen b = build '(' <> b <> build ')'

withBrace :: Builder -> Builder
withBrace b = getIndent <> build "{\n" <> b <> getIndent <> build "}\n"

byComma :: DafnyPrinter a => [a] -> Builder
byComma [] = mempty
byComma (x:xs) = foldl (\ys y -> ys  <> build ", " <> build y) (build x) xs

byLine :: DafnyPrinter a => [a] -> Builder
byLine = foldr (\y ys -> build y <> build "\n" <> ys) mempty

infixr 6 <!>

class DafnyPrinter a where
  build :: a -> Builder
  (<!>) :: a -> Builder -> Builder
  a <!> b = build a <> b

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
  build (TSeq t) = "seq<" <!> t <!> build ">"
  build _        = undefined

instance DafnyPrinter QTy where
  build TNor = build "nor"
  build THad = build "had"
  build TCH  = build "ch"

instance DafnyPrinter Binding where
  build (Binding x t) = x <!>  " : " <!> build t

instance DafnyPrinter Toplevel where
  build (QDafny s) = build s 
  build (QMethod idt bds rets reqs ens block) =
    "method " <!> idt <!> " " <!>
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
  build (SEmit (SBlock b)) = build b
  build s = getIndent <> buildStmt s <> build ';'
    where buildStmt :: Stmt -> Builder
          buildStmt (SVar bd Nothing) = build "var " <> build bd
          buildStmt (SVar bd (Just e)) = build "var " <> build bd <>
                                         build " := " <> build e
          buildStmt (SAssign v e) = build v <> build " := " <> build e
          buildStmt (SCall e es) = build e <> withParen (byComma es)
          buildStmt (SEmit s') = buildEmit s'
          buildStmt e = build "// undefined builder for Stmt : " <> build (show e)
          buildEmit :: EmitStmt -> Builder
          buildEmit (SIfDafny e b) = "if " <!> withParen (build e) <> build b
          buildEmit (SBlock b) = build b

instance DafnyPrinter Exp where
  build (ENum n) = build $ show n
  build (EVar v) = build v
  build (EEmit e) = build e
  build (EOp2 op e1 e2) = buildOp2 op (build e1) (build e2)
    where
      buildOp2 :: Op2 -> Builder -> Builder -> Builder
      buildOp2 OAnd = flip (<>) . (" && " <!>)
      buildOp2 OOr  = flip (<>) . (" || " <!>)
      buildOp2 OAdd = flip (<>) . (" + " <!>)
      buildOp2 OMul = flip (<>) . (" * " <!>)
      buildOp2 OMod = flip (<>) . (" % " <!>)
      buildOp2 _    = const . const $ build "Nor should not be in emitted form"
      -- FIXEM: why without `build` it still works?
  build e = "//" <!> show e <!> build " should not be in emitted form!"

instance DafnyPrinter EmitExp where
  build (ELambda v e) = build v <> build " => " <> build e
  build (EMakeSeq ty e ee) =
    "seq<" <!> ty <!> ">" <!> withParen (e <!> ", " <!> build ee)
  build (EDafnyVar s) = build s
  build (ECall e es) = e <!> withParen (byComma es)

buildConds :: String -> [Exp] -> Builder
buildConds s = foldr (\x xs -> s <!> x <!> '\n' <!> xs) (build "")

texify :: DafnyPrinter a => a -> Text
texify = TB.toLazyText . flip runReader 0 . doBuild . build
