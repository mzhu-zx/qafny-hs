{-# LANGUAGE
    FlexibleContexts
  , FlexibleInstances
  , GeneralizedNewtypeDeriving
  , NamedFieldPuns
  , OverloadedStrings
  #-}

module Qafny.Syntax.Emit where

import           Control.Arrow
    (Arrow (first))
import           Control.Monad.Reader
import qualified Data.Map.Strict        as Map
import           Data.Maybe
    (maybeToList)
import           Data.Sum
import qualified Data.Text              as TS
import           Data.Text.Lazy
    (Text, unpack)
import           Data.Text.Lazy.Builder
    (fromString)
import qualified Data.Text.Lazy.Builder as TB
import qualified Data.Text.Lazy.IO      as TIO
    (putStrLn)
import           Qafny.Syntax.AST
import           Qafny.Syntax.Builder
import           Qafny.Syntax.IR

-------------------- Builder --------------------
default (TB.Builder)

line :: Builder
line = return $ TB.singleton '\n'

space :: Builder
space = return $ TB.singleton ' '

withIncr2 :: Builder -> Builder
withIncr2 = local (first (+ 2))

indent :: Builder
indent = do (n, _) <- ask
            return $ TB.fromText (TS.replicate n " ")


withParen :: DafnyPrinter a => a -> Builder
withParen b = build '(' <> build b <> build ')'

withBracket :: Builder -> Builder
withBracket b = build '[' <> b <> build ']'

withBrace :: Builder -> Builder
withBrace b = indent <> return (t "{\n") <> b <> indent <> return (t"}\n")


-- | Build and separate by 'op' but without leading or trailing separator
by :: (DafnyPrinter b, DafnyPrinter a) => b -> [a] -> Builder
by op []     = mempty
by op (x:xs) = foldl (\ys y -> ys <!> op <!> build y) (build x) xs

byComma :: DafnyPrinter a => [a] -> Builder
byComma = by (t", ")

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
  if b then build d else build $ "// (DEBUG)" <> TB.fromString (show e)

infixr 6 <!>

class DafnyPrinter a where
  build :: a -> Builder

(<!>) :: (DafnyPrinter a, DafnyPrinter b) => a -> b -> Builder
a <!> b = build a <> build b
{-# INLINE (<!>) #-}

(<+>) :: (DafnyPrinter a, DafnyPrinter b) => a -> b -> Builder
a <+> b = a <!> space <!> b
{-# INLINE (<+>) #-}


instance DafnyPrinter Builder where
  build = id
  {-# INLINE build #-}

instance DafnyPrinter TB.Builder where
  build = return

instance DafnyPrinter Int where
  build = build . show

instance DafnyPrinter Char where
  build = return . TB.singleton

instance DafnyPrinter String where
  build = return . fromString

instance DafnyPrinter AST where
  build = by line

instance DafnyPrinter Ty where
  build TNat               = rt"nat"
  build TInt               = rt"int"
  build TBool              = rt"bool"
  build (TArrow tys ty)    =
    withBracket (byComma tys) <+> t"->" <+> ty
  build TMeasured          = rt  "measured"
  build (TQReg n)          = t"qreg" <+> n
  build (TSeq ty)           = t"seq<" <!> ty <!> t">"
  build ty@(TEmit (TAny s)) = debugOnly ty $ TB.fromString s

instance DafnyPrinter MethodType where
  build ty@MethodType {mtSrcParams=ts, mtSrcReturns=ts'} = debugOnly ty $
    withParen (byComma ts) <+> t"->" <+> withParen (byComma ts')

instance DafnyPrinter MethodElem where
  build tt = debugOnly tt $ buildSub tt
    where
      buildSub (MTyPure x ty)   = debugOnly tt $ fromString x <+> t":" <+> ty
      buildSub (MTyQuantum x e) = fromString x <!> t"[" <!> e <!> t"]"

instance DafnyPrinter AExp where
  build (ANat n) = build n
  build (AVar v) = build $ fromString v

instance DafnyPrinter QTy where
  build TNor  = rt"nor"
  build THad  = rt"had"
  build TEn   = rt"en"
  build TEn01 = rt"en01"
  build TQft  = rt"qft"

instance DafnyPrinter (Binding ()) where
  build (Binding x ty) = fromString x <+> t":" <+> ty

instance DafnyPrinter QDafny where
  build (QDafny s) = indent <!> fromString s

instance DafnyPrinter (QMethod ()) where
  build (QMethod idt bds rets reqs ens blockHuh) =
    indent <> t"method " <!> fromString idt
    <+> withParen (byComma bds) <> buildRets rets
    <!> lineHuh reqEns
    <!> (withIncr2 . by line $ (indent <!>) <$> reqEns)
    -- add a tailing newline if we have conds and blocks
    <!> lineHuh blockHuh
    <!> by line (maybeToList blockHuh)
    where buildRets [] = mempty
          buildRets r  = t" returns" <+> withParen (byComma r)
          reqEns = buildConds "requires" reqs <> buildConds "ensures" ens

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
        t"for " <!> fromString idf <!> t" := " <!> initf <!> t" to " <!> bound
          <!> t"\n"
          <!> buildInvs
          <!> b
      buildInvs = withIncr2 . byLineT $
        map (((indent <!> t"invariant") <+>) . build) invs

  build (SDafny s') = indent <!> fromString s'

  build s@(SFor idx boundl boundr eG invs seps body) = debugOnly s $
    indent <> t"for"
    <+> fromString idx <+> t"∈" <+> withBracket (boundl <+> t".." <+> boundr)
    <+> t"with" <+> eG <!> line
    <!> body

  -- Statements that end with a SemiColon
  build s@(SIf eg sep block) = debugOnly s $
    indent <!> t"if" <+> withParen eg <!> line <!>
    indent <!> t"  " <!> t"seperates" <+> sep <!> line <!>
    block

  build s = indent <> buildStmt s <> build ';'
    where
      buildStmt :: Stmt' -> Builder
      buildStmt (SVar bd Nothing) = t"var " <!> bd
      buildStmt (SVar bd (Just e)) = t"var " <!> bd <!> t" := " <!> e
      buildStmt (v ::=: e) = fromString v <!> t" := " <!> e
      buildStmt (SCall v es) = fromString v <!> withParen (byComma es)
      buildStmt (SEmit s') = buildEmit s'
      buildStmt (SAssert e) = t"assert" <!> e
      buildStmt (e1 :*=: e2) = debugOnly s $
        e1 <+> t"*=" <+> λHuh e2
      buildStmt e = t"// undefined builder for Stmt : " <!> fromString (show e)

      λHuh e@(ELambda {}) = t"λ" <+> e
      λHuh e              = build e

      buildEmit :: EmitStmt -> Builder
      buildEmit (SVars bds e) = t"var" <+> byComma bds <+> t":=" <+> e
      buildEmit (vs :*:=: rhs)  = case rhs of
        [] -> mempty
        _  -> byComma (fromString <$> vs) <+> t":=" <+> byComma (withParen <$> rhs)
      -- buildEmit (SIfDafny e b) = "if " <!> withParen (build e) <!> b
      buildEmit _             = error "Should have been handled!!"

instance DafnyPrinter GuardExp where
  build (GEPartition p _) = build p

instance DafnyPrinter (Exp ()) where
  build (ENum n) = build n
  build (EVar v) = build (fromString v)
  build (EBool b) = rt $ if b then "true" else "false"
  build (EEmit e) = build e
  build (EOp1 ONeg e1) = t"-" <+> e1
  build (EOp2 op e1 e2) = buildOp2 op (build e1) (build e2)
  -- parentheses are critical to forall expressions!
  build (EForall x eb e) =
    withParen $ t"forall " <!> x  <!> beb eb <!> t  " :: " <!> e
    where
      beb (Just eb') = t" | " <!> eb'
      beb Nothing    = mempty
  build e@EHad = debugOnly e (t"H")
  build e@(ESpec p qt specs) = debugOnly e $
    t"{" <+> p <+> t":" <+> qt  <+> t"↦" <+> byComma specs <+> t"}"
  build e@(EApp v es) = fromString v <!> withParen (byComma es)
  build e@(EMeasure s) = debugOnly e $
    t"measure" <+> s
  build EWildcard = rt"_"
  build (ELambda el) = build el
  build e = t"//" <!> fromString (show e) <!> t" should not be in emitted form!"

instance (Show f, DafnyPrinter f) => DafnyPrinter (LambdaF f) where
  build e@(LambdaF{ bPhase, bBases, ePhase, eBases }) =
    case (bPhase, ePhase) of
      (PhaseWildCard, PhaseWildCard) ->
        tupleLike (fromString <$> bBases) <+> t"=>" <+> tupleLike eBases
      (_, _) -> debugOnly e $
        bPhase <+>
        t"~" <+> tupleLike (fromString <$> bBases) <+>
        t"=>" <+>
        ePhase <+> t"~" <+> tupleLike eBases

instance DafnyPrinter Intv where
  build e@(Intv e1 e2) = debugOnly e $
    withBracket $ e1 <+> t".." <+> e2

instance (DafnyPrinter f, Show f) => DafnyPrinter (SpecExpF f) where
  build s = debugOnly s buildSubterm
    where
      buildSubterm = case s of
        SEWildcard -> rt"_"
        SESpecNor (SpecNorF v1 e2) -> t"⊗" <+> fromString v1 <+> '.' <+> e2
        SESpecHad (SpecHadF v1 p) -> t"⊗" <+> fromString v1 <+> '.' <+> p
        SESpecEn (SpecEnF v1 intv a p es) ->
          t"Σ" <+> fromString v1 <+> t"∈" <+> intv <+> '.' <+> a <+> p <+>
          withParen (byComma es)
        SESpecEn01 (SpecEn01F v1 intv1 a p v2 intv2 e5) ->
          t"Σ" <+> fromString v1 <+> t"∈" <+> intv1 <+> '.' <+>
          t"⊗" <+> fromString v2 <+> t"∈" <+> intv2 <+> '.' <+>
          a <+> p <+> withParen (byComma e5)

instance DafnyPrinter f => DafnyPrinter (Maybe f) where
  build Nothing  = rt"_"
  build (Just x) = build x

instance (Show f, DafnyPrinter f) => DafnyPrinter (PhaseExpF f) where
  build p = debugOnly p $ case p of
    PhaseZ                -> rt"1"
    PhaseWildCard         -> rt"_"
    PhaseOmega e1 e2      -> t"ω" <!> withParen (byComma [e1, e2])
    PhaseSumOmega i e1 e2 -> t"Ω" <+> i <+> t"." <+> withParen (byComma [e1, e2])

instance (Show f, DafnyPrinter f) => DafnyPrinter (AmpExpF f) where
  build p = debugOnly p $ case p of
    ADefault     -> mempty
    AISqrt en ed -> t"isqrt" <+> withParen (byComma [en, ed])
    ASin e       -> t"sin" <!> withParen (build e)
    ACos e       -> t"cos" <!> withParen (build e)


instance DafnyPrinter EmitExp where
  build (e1 :@: e2) = e1 <!> t"[" <!> e2 <!> t"]"
  build (e1 :@@: (e2, e3)) = e1 <!> t"[" <!> e2 <!> t".." <!> e3 <!> t"]"
  build EMtSeq = rt"[]"
  build (EMakeSeq ty e ee) =
    t"seq<" <!> ty <!> t">" <!> withParen (e <!> t", " <!> ee)
  build (EDafnyVar s) = build (fromString s)
  build (EOpChained e eos) =
    foldl (\el (op, er) -> buildOp2 op el (build er)) (build e) eos
  build (ECard e) = t"|" <!> e <!> t"|"
  build (ECall v es) = fromString v <!> withParen (byComma es)
  build (EMultiLambda vs e) = withParen (byComma (fromString <$> vs)) <+> t"=>" <+> e

instance DafnyPrinter Range where
  build rr@(Range v l r) = debugOnly rr $ build (EVar v :@@: (l, r))

instance DafnyPrinter Partition where
  build pp@(Partition p) = debugOnly pp $ byComma p

instance DafnyPrinter Loc where
  build = build . fromString . deref

instance DafnyPrinter Locus where
  build st@(Locus {loc=l, part=p, qty, degrees=dgrs}) = debugOnly st $
    l <+> t"↦" <+> p <+> t"::" <+> qty <+> withBracket (byComma dgrs)


instance ( Show a, Show b
         , DafnyPrinter a, DafnyPrinter b
         ) => DafnyPrinter (a, b) where
  build t'@(a, b) = debugOnly t' $ withParen . byComma $ [build a, build b]

instance ( Show a, Show b, Show c
         , DafnyPrinter a, DafnyPrinter b, DafnyPrinter c
         ) => DafnyPrinter (a, b, c) where
  build t'@(a, b, c) = debugOnly t' $
    withParen . byComma $ [build a, build b, build c]

-- instance (Show f, DafnyPrinter f) => DafnyPrinter (QSpecF f) where
--   build q@QSpecF{amp, phase, spec} = debugOnly q $
--     amp <+> phase <+> "~" <+> spec


instance ( Show k, Show v
         , DafnyPrinter k, DafnyPrinter v
         ) => DafnyPrinter (Map.Map k v) where
  build m' = debugOnly m $
    byLineT ((indent <>) . row <$> m)
    where
      m = Map.toList m'
      row (a, b) = a <+> t"↦" <+> b

instance DafnyPrinter MTy where
  build (MTy (Inl ty)) = build ty
  build (MTy (Inr m)) =
    byComma (mtSrcParams m) <+> t"↪" <+> byComma (mtSrcReturns m)

-- | Warning: don't emit parentheses in `buildOp2` because `EOpChained` relies
-- on this function not to be parenthesized
-- TODO: I want to get the precedence right here.
buildOp2 :: Op2 -> Builder -> Builder -> Builder
buildOp2 ONor b1 b2 = t"nor" <!> withParen (byComma [b1, b2])
buildOp2 op b1 b2 =  parenOpt b1 <!> opSign <!> parenOpt b2
  where
    parenOpt :: Builder -> Builder
    parenOpt =
      case op of
        OAnd -> withParen
        OOr  -> withParen
        OMod -> withParen -- mod is a fragile operator
        _    -> id

    opSign :: TB.Builder
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
        -- _    -> "\\ unsupprted " <> show op

buildConds :: TB.Builder -> [Exp'] -> [Builder]
buildConds s = map ((s <!> space) <!>)

runBuilder :: DafnyPrinter a => Int -> Bool -> a -> Text
runBuilder i debug = TB.toLazyText . flip runReader (i, debug) . doBuild . build

texify :: DafnyPrinter a => a -> Text
texify = runBuilder 0 False

prettyIO :: DafnyPrinter a => a -> IO ()
prettyIO = TIO.putStrLn . runBuilder 0 True

showEmit :: DafnyPrinter a => a -> String
showEmit = unpack . texify

-- Debug mode
showEmitI :: DafnyPrinter a => Int -> a -> String
showEmitI i = unpack . runBuilder i True

showEmit0 :: DafnyPrinter a => a -> String
showEmit0 = showEmitI 0


-- Regex for OverloadedStrings
-- \(\"[^\"]+?\"\) → t\1
