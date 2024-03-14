{-# LANGUAGE
    FlexibleContexts
  , FlexibleInstances
  , GeneralizedNewtypeDeriving
  , NamedFieldPuns
  #-}

module Qafny.Syntax.Emit where

import           Qafny.Syntax.AST

import           Control.Arrow
    (Arrow (first))
import           Control.Monad.Reader
import qualified Data.Map.Strict        as Map
import           Data.Maybe
    (maybeToList)
import           Data.Sum
import           Data.Text.Lazy
    (Text, unpack)
import qualified Data.Text.Lazy.Builder as TB
import           Qafny.Syntax.IR
    (Locus (..), STuple (..))

-------------------- Builder --------------------

newtype Builder_ a = Builder { doBuild :: Reader (Int, Bool) a }
  deriving (Functor, Applicative, Monad, (MonadReader (Int, Bool)))
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
withIncr2 = local (first (+ 2))

indent :: Builder
indent = do (n, _) <- ask
            build $ replicate n ' '


withParen :: DafnyPrinter a => a -> Builder
withParen b = build '(' <> build b <> build ')'

withBracket :: Builder -> Builder
withBracket b = build '[' <> b <> build ']'

withBrace :: Builder -> Builder
withBrace b = indent <> build "{\n" <> b <> indent <> build "}\n"


-- | Build and separate by 'op' but without leading or trailing separator
by :: (DafnyPrinter b, DafnyPrinter a) => b -> [a] -> Builder
by op []     = mempty
by op (x:xs) = foldl (\ys y -> ys <!> op <!> build y) (build x) xs

byComma :: DafnyPrinter a => [a] -> Builder
byComma = by ", "

tupleLike :: DafnyPrinter a => [a] -> Builder
tupleLike []  = mempty
tupleLike [x] = build x
tupleLike xs  = withParen . byComma $ xs

-- | Build and separate by line but with a trailing newline
byLineT :: DafnyPrinter a => [a] -> Builder
byLineT = foldr (\y ys -> y <!> line <!> ys) mempty

-- | Build each element and separate them by a newline without producing any
-- newline in the end but with a leading newline if the list is nonempty
byLineL :: DafnyPrinter a => [a] -> Builder
byLineL a = lineHuh a <> by line a

lineHuh :: Foldable t => t a -> Builder
lineHuh a = if null a then mempty else line

-- FIXME : raise an error if a DEBUG mode term is emitted
debugOnly :: (Show e, DafnyPrinter a) => e -> a -> Builder
debugOnly e d = do
  (_, b) <- ask
  if b then build d else build $ "// (DEBUG)" ++ show e

infixr 6 <!>

class DafnyPrinter a where
  build :: a -> Builder

(<!>) :: (DafnyPrinter a, DafnyPrinter b) => a -> b -> Builder
a <!> b = build a <> build b
{-# INLINE (<!>) #-}

(<+>) :: (DafnyPrinter a, DafnyPrinter b) => a -> b -> Builder
a <+> b = a <!> " " <!> b
{-# INLINE (<+>) #-}


instance DafnyPrinter Builder where
  build = id
  {-# INLINE build #-}

instance DafnyPrinter Int where
  build = return . TB.fromString . show

instance DafnyPrinter Char where
  build = return . TB.singleton

instance DafnyPrinter String where
  build = return . TB.fromString

instance DafnyPrinter AST where
  build = by line

instance DafnyPrinter Ty where
  build TNat               = build "nat"
  build TInt               = build "int"
  build TBool              = build "bool"
  build (TArrow tys ty)    =
    withBracket (byComma tys) <+> "->" <+> ty
  build TMeasured          = build  "measured"
  build (TQReg n)          = "qreg" <+> n
  build (TSeq t)           = "seq<" <!> t <!> ">"
  build t@(TEmit (TAny s)) = debugOnly t $ build s

instance DafnyPrinter MethodType where
  build t@MethodType {mtSrcParams=ts, mtSrcReturns=ts'} = debugOnly t $
    withParen (byComma ts) <+> "->" <+> withParen (byComma ts')

instance DafnyPrinter MethodElem where
  build t = debugOnly t $ buildSub t
    where
      buildSub (MTyPure x ty)   = debugOnly t $ x <+> ":" <+> ty
      buildSub (MTyQuantum x e) = x <!> "[" <!> e <!> "]"

instance DafnyPrinter AExp where
  build (ANat n) = build n
  build (AVar v) = build v

instance DafnyPrinter QTy where
  build TNor  = build "nor"
  build THad  = build "had"
  build TEN   = build "ch"
  build TEN01 = build "ch01"

instance DafnyPrinter (Binding ()) where
  build (Binding x t) = x <+>  ":" <+> t

instance DafnyPrinter QDafny where
  build (QDafny s) = indent <> build s

instance DafnyPrinter (QMethod ()) where
  build (QMethod idt bds rets reqs ens blockHuh) =
    indent <> "method " <!> idt
    <+> withParen (byComma bds) <> buildRets rets
    <!> lineHuh reqEns
    <!> (withIncr2 . by line $ (indent <!>) <$> reqEns)
    -- add a tailing newline if we have conds and blocks
    <!> lineHuh blockHuh
    <!> by line (maybeToList blockHuh)
    where buildRets [] = mempty
          buildRets r  = " returns" <+> withParen (byComma r)
          reqEns = buildConds "requires" reqs ++ buildConds "ensures" ens

instance DafnyPrinter (Block ()) where
  build = withBrace . withIncr2 . byLineT . inBlock

instance DafnyPrinter (Toplevel ()) where
  build t = case unTop t of
    Inl q -> build q
    Inr q -> build q


instance DafnyPrinter (Stmt ()) where
  build (SEmit (SBlock b)) = build b
  build (SEmit f@(SForEmit idf initf bound invs b)) =
    indent <> buildFor
    where
      buildFor =
        "for " <!> idf <!> " := " <!> initf <!> " to " <!> bound
          <!> "\n"
          <!> buildInvs
          <!> b
      buildInvs = withIncr2 . byLineT $
        map (((indent <!> "invariant") <+>) . build) invs

  build (SDafny s') = indent <> build s'

  build s@(SFor idx boundl boundr eG invs seps body) = debugOnly s $
    indent <> "for"
    <+> idx <+> "∈" <+> withBracket (boundl <+> ".." <+> boundr)
    <+> "with" <+> eG <!> line
    <!> body

  -- Statements that end with a SemiColon
  build s = indent <> buildStmt s <> build ';'
    where
      buildStmt :: Stmt' -> Builder
      buildStmt (SVar bd Nothing) = "var " <!> bd
      buildStmt (SVar bd (Just e)) = "var " <!> bd <!> " := " <!> e
      buildStmt (v ::=: e) = v <!> " := " <!> e
      buildStmt (SCall e es) = e <!> withParen (byComma es)
      buildStmt (SEmit s') = buildEmit s'
      buildStmt (SAssert e) = "assert " <!> e
      buildStmt (e1 :*=: e2) = debugOnly s $
        e1 <+> "*=" <+> λHuh e2
      buildStmt e = "// undefined builder for Stmt : " <!> show e

      λHuh e@(ELambda {}) = "λ" <+> e
      λHuh e              = build e

      buildEmit :: EmitStmt -> Builder
      buildEmit (SVars bds e) = "var" <+> byComma bds <+> ":=" <+> e
      buildEmit (vs :*:=: rhs)  = case rhs of
        [] -> mempty
        _  -> byComma vs <+> ":=" <+> byComma (withParen <$> rhs)
      -- buildEmit (SIfDafny e b) = "if " <!> withParen (build e) <!> b
      buildEmit _             = error "Should have been handled!!"

instance DafnyPrinter GuardExp where
  build (GEPartition p _) = build p

instance DafnyPrinter (Exp ()) where
  build (ENum n) = build $ show n
  build (EVar v) = build v
  build (EBool b) = build $ if b then "true" else "false"
  build (EEmit e) = build e
  build (EOp1 ONeg e1) = "-" <+> e1
  build (EOp2 op e1 e2) = buildOp2 op (build e1) (build e2)
  -- parentheses are critical to forall expressions!
  build (EForall x eb e) = withParen $ "forall " <!> x  <!> beb eb <!>  " :: " <!> e
    where beb (Just eb') = " | " <!> eb'
          beb Nothing    = mempty
  build e@EHad = debugOnly e "H"
  build e@(ESpec p qt specs) = debugOnly e $
    "{" <+> p <+> ":" <+> qt  <+> "↦" <+> byComma specs <+> "}"
  build e@(EApp v es) = v <!> withParen (byComma es)
  build e@(EMeasure s) = debugOnly e $
    "measure" <+> s
  build EWildcard = build "_"
  build (ELambda el) = build el
  build e = "//" <!> show e <!> build " should not be in emitted form!"

instance (Show f, DafnyPrinter f) => DafnyPrinter (LambdaF f) where
  build e@(LambdaF{ bPhase, bBases, ePhase, eBases }) =
    case (bPhase, ePhase) of
      (PhaseWildCard, Nothing) ->
        tupleLike bBases <+> "=>" <+> tupleLike eBases
      (_, _) -> debugOnly e $
        bPhase <+> "~" <+> tupleLike bBases <+>
        "=>" <+>
        ePhase <+> "~" <+> tupleLike eBases

instance (DafnyPrinter f, Show f) => DafnyPrinter (SpecExpF f) where
  build s = debugOnly s buildSubterm
    where
      buildSubterm = case s of
        SEWildcard -> build "_"
        SESpecNor v1 e2 -> "⊗" <+> v1 <+> '.' <+> e2
        SESpecEN v1 (Intv e1 e2) e3 ->
          "Σ" <+> v1 <+> "∈" <+> '[' <!> e1 <+> ".." <+> e2 <!> ']' <+> '.' <+>
          withParen (byComma e3)
        SESpecEN01 v1 (Intv e1 e2) v2 (Intv e3 e4) e5 ->
          "Σ" <+> v1 <+> "∈" <+> '[' <!> e1 <+> ".." <+> e2 <!> ']' <+> '.' <+>
          "⊗" <+> v2 <+> "∈" <+> '[' <!> e3 <+> ".." <+> e4 <!> ']' <+> '.' <+>
          withParen (byComma e5)

instance DafnyPrinter f => DafnyPrinter (Maybe f) where
  build Nothing  = build "_"
  build (Just x) = build x

instance (Show f, DafnyPrinter f) => DafnyPrinter (PhaseExpF f) where
  build p = debugOnly p $ case p of
    PhaseZ                -> build "1"
    PhaseWildCard         -> build "_"
    PhaseOmega e1 e2      -> "ω" <!> withParen (byComma [e1, e2])
    PhaseSumOmega i e1 e2 -> "Ω" <+> i <+> "." <+> withParen (byComma [e1, e2])

instance (Show f, DafnyPrinter f) => DafnyPrinter (AmpExpF f) where
  build p = debugOnly p $ case p of
    ADefault     -> build ""
    AISqrt en ed -> "isqrt" <+> withParen (byComma [en, ed])
    ASin e       -> "sin" <!> withParen (build e)
    ACos e       -> "cos" <!> withParen (build e)


instance DafnyPrinter EmitExp where
  build (ESelect e1 e2) = e1 <!> "[" <!> e2 <!> "]"
  build (ESlice e1 e2 e3) = e1 <!> "[" <!> e2 <!> ".." <!> e3 <!> "]"
  build EMtSeq = build "[]"
  build (EMakeSeq ty e ee) =
    "seq<" <!> ty <!> ">" <!> withParen (e <!> ", " <!> ee)
  build (EDafnyVar s) = build s
  build (EOpChained e eos) =
    foldl (\el (op, er) -> buildOp2 op el (build er)) (build e) eos
  build (ECard e) = "|" <!> e <!> build "|"
  build (ECall e es) = e <!> withParen (byComma es)
  build (EMultiLambda vs e) = withParen (byComma vs) <+> "=>" <+> e

instance DafnyPrinter Range where
  build rr@(Range v l r) = debugOnly rr $ build (ESlice (EVar v) l r)

instance DafnyPrinter Partition where
  build pp@(Partition p) = debugOnly pp $ byComma p

instance DafnyPrinter Loc where
  build = build . deref

instance DafnyPrinter STuple where
  build st@(STuple (l, p, (qty, dgrs))) = debugOnly st $
    l <+> "↦" <+> p <+> "::" <+> qty <+> withBracket (byComma dgrs)

instance DafnyPrinter Locus where
  build st@(Locus {loc=l, part=p, qty, degrees=dgrs}) = debugOnly st $
    l <+> "↦" <+> p <+> "::" <+> qty <+> withBracket (byComma dgrs)


instance (Show a, Show b, DafnyPrinter a, DafnyPrinter b) => DafnyPrinter (a, b) where
  build t@(a, b) = debugOnly t $ withParen . byComma $ [build a, build b]

instance (Show a, Show b, Show c,
          DafnyPrinter a, DafnyPrinter b, DafnyPrinter c) =>

         DafnyPrinter (a, b, c) where
  build t@(a, b, c) = debugOnly t $
    withParen . byComma $ [build a, build b, build c]

instance (Show f, DafnyPrinter f) => DafnyPrinter (QSpecF f) where
  build q@QSpecF{amp, phase, spec} = debugOnly q $
    amp <+> phase <+> "~" <+> spec


instance (Show k, Show v, DafnyPrinter k, DafnyPrinter v) => DafnyPrinter (Map.Map k v) where
  build m' = debugOnly m $
    byLineT ((indent <>) . row <$> m)
    where
      m = Map.toList m'
      row (a, b) = a <+> "↦" <+> b

instance DafnyPrinter MTy where
  build (MTy (Inl t)) = build t
  build (MTy (Inr m)) = byComma (mtSrcParams m) <+> "↪" <+> byComma (mtSrcReturns m)


-- | Warning: don't emit parentheses in `buildOp2` because `EOpChained` relies
-- on this function not to be parenthesized
-- TODO: I want to get the precedence right here.
buildOp2 :: Op2 -> Builder -> Builder -> Builder
buildOp2 op b1 b2 =  parenOpt b1 <!> opSign <!> parenOpt b2
  where
    parenOpt :: Builder -> Builder
    parenOpt =
      case op of
        OAnd -> withParen
        OOr  -> withParen
        OMod -> withParen -- mod is a fragile operator
        _    -> id

    opSign :: String
    opSign =
      case op of
        OAnd -> " && "
        OOr  -> " || "
        OAdd -> " + "
        OSub -> " - "
        OMul -> " * "
        OMod -> " % "
        OEq  -> " == "
        OLt  -> " < "
        OLe  -> " <= "
        OGt  -> " > "
        OGe  -> " >= "
        _    -> "\\ unsupprted " ++ show op

buildConds :: String -> [Exp'] -> [Builder]
buildConds s = map ((s <!> " ") <!>)

runBuilder :: DafnyPrinter a => Int -> Bool -> a -> Text
runBuilder i debug = TB.toLazyText . flip runReader (i, debug) . doBuild . build

texify :: DafnyPrinter a => a -> Text
texify = runBuilder 0 False

showEmit :: DafnyPrinter a => a -> String
showEmit = unpack . texify

-- Debug mode
showEmitI :: DafnyPrinter a => Int -> a -> String
showEmitI i = unpack . runBuilder i True

showEmit0 :: DafnyPrinter a => a -> String
showEmit0 = showEmitI 0
