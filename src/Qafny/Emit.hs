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

(<!>) :: (DafnyPrinter a, DafnyPrinter b) => a -> b -> Builder
a <!> b = build a <> build b

instance DafnyPrinter Builder where
  build = id

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
  build (TSeq t) = "seq<" <!> t <!> ">"
  build _        = undefined

instance DafnyPrinter QTy where
  build TNor = build "nor"
  build THad = build "had"
  build TCH  = build "ch"

instance DafnyPrinter Binding where
  build (Binding x t) = x <!>  " : " <!> t

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
  build (SEmit f@(SForEmit idf initf bound invs b)) =
    getIndent <> buildFor
    where
      buildFor =
        "for " <!> idf <!> " := " <!> initf <!> " to " <!> bound
          <!> "\n" <!>
          -- todo: emit invariants
          b
  build (SDafny s') = getIndent <> build s'
  build s = getIndent <> buildStmt s <> build ';'
    where
      buildStmt :: Stmt -> Builder
      buildStmt (SVar bd Nothing) = "var " <!> bd
      buildStmt (SVar bd (Just e)) = "var " <!> bd <!> " := " <!> e
      buildStmt (SAssign v e) = v <!> " := " <!> e
      buildStmt (SCall e es) = e <!> withParen (byComma es)
      buildStmt (SEmit s') = buildEmit s'
      buildStmt e = "// undefined builder for Stmt : " <!> show e
      buildEmit :: EmitStmt -> Builder
      buildEmit (SIfDafny e b) = "if " <!> withParen (build e) <!> b
      buildEmit _ = error "Should have been handled!!"

instance DafnyPrinter Exp where
  build (ENum n) = build $ show n
  build (EVar v) = build v
  build (EEmit e) = build e
  build (EOp2 op e1 e2) = buildOp2 op (build e1) (build e2)
  build e = "//" <!> show e <!> build " should not be in emitted form!"

instance DafnyPrinter EmitExp where
  build (ELambda v e) = v <!> " => " <!> e
  build EMtSeq = build "[]"
  build (EMakeSeq ty e ee) =
    "seq<" <!> ty <!> ">" <!> withParen (e <!> ", " <!> ee)
  build (EDafnyVar s) = build s
  build (EOpChained e eos) =
    e <!> foldr (\(op, e1) bs -> buildOp2 op (build e1) bs) mempty eos
  build (ECard e) = "|" <!> e <!> build "|"
  build (ECall e es) = e <!> withParen (byComma es)


-- | Warning: don't emit parentheses in `buildOp2` because `EOpChained` relies
-- on this function not to be parenthesized
buildOp2 :: Op2 -> Builder -> Builder -> Builder
buildOp2 op = (<!>) . (<!> opSign)
  where
    opSign =
      case op of
        OAnd  -> " && "
        OOr   -> " || "
        OAdd  -> " + "
        OMul  -> " * "
        OMod  -> " % "
        OLt   -> " < "
        OLe   -> " <= "
        _     -> " ???? "

buildConds :: String -> [Exp] -> Builder
buildConds s = foldr (\x xs -> s <!> x <!> '\n' <!> xs) (build "")

texify :: DafnyPrinter a => a -> Text
texify = TB.toLazyText . flip runReader 0 . doBuild . build
