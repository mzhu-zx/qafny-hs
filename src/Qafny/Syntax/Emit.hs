{-# LANGUAGE
    FlexibleContexts
  , FlexibleInstances
  , GeneralizedNewtypeDeriving
  , NamedFieldPuns
  #-}

module Qafny.Syntax.Emit where

import           Control.Arrow
    (Arrow (first))
import           Control.Monad.Reader
import           Data.Array.IArray
    (Array, array, (!))
import qualified Data.Map.Strict          as Map
import           Data.Maybe
    (maybeToList)
import           Data.Sum
import qualified Data.Text                as TS
import           Data.Text.Lazy
    (Text, unpack)
import           Data.Text.Lazy.Builder
    (fromString)
import qualified Data.Text.Lazy.Builder   as TB
import qualified Data.Text.Lazy.IO        as TIO
    (putStrLn)
import           Qafny.Syntax.AST
import           Qafny.Syntax.EmitBinding
import           Qafny.Syntax.IR

import           Data.Void
    (Void)

import           Prettyprinter
    (line, space, lbracket, rbracket, lbrace, rbrace)
import qualified Prettyprinter            as P

-------------------- Builder --------------------
type Builder = P.Doc Void


-- indentTable :: Array Int TB.Builder
-- indentTable =
--   array (0, 20) [ (x, TB.fromText $ TS.replicate x (TS.singleton ' '))
--                 | x <- [ 0 .. 20 ] ]

incr2 :: DafnyPrinter a => a -> Builder
incr2 = P.indent 2 . pp

vsep :: DafnyPrinter a => [a] -> Builder
vsep = P.vsep . (pp <$>)

encloseSep
  :: (DafnyPrinter delim, DafnyPrinter sep, DafnyPrinter body)
  => delim -> delim -> sep -> [body] -> Builder
encloseSep l r s bs =
  P.encloseSep (pp l) (pp r) (pp s) (pp <$> bs)

-- indent :: Builder
-- indent = do
--   (n, _) <- ask
--   pp $ indentTable ! n

-- withParen :: DafnyPrinter a => a -> Builder
-- withParen b = pp '(' <> pp b <> pp ')'

-- withBracket :: Builder -> Builder
-- withBracket b = pp '[' <> b <> pp ']'

-- withBrace :: Builder -> Builder
-- withBrace b =
--   indent <> pp "{"
--   <> line <!> b <> line
--   <> indent <!> "}"
--   <!> line


-- | Elements separate by 'op' but without leading or trailing separator
by :: (DafnyPrinter b, DafnyPrinter a) => b -> [a] -> Builder
by op []     = mempty
by op (x:xs) = foldl (\ys y -> ys <!> op <!> pp y) (pp x) xs

-- byComma :: DafnyPrinter a => [a] -> Builder
-- byComma = by ", "

tupled :: DafnyPrinter a => [a] -> Builder
tupled = P.tupled . (pp <$>)  

-- -- | Pp and separate by line but with a trailing newline
-- byLineT :: DafnyPrinter a => [a] -> Builder
-- byLineT a = by (line <> indent) a <!> line

-- -- | Pp each element and separate them by a newline without producing any
-- -- newline in the end but with a leading newline if the list is nonempty
-- byLineL :: DafnyPrinter a => [a] -> Builder
-- byLineL a = lineHuh a <> by line a

-- lineHuh :: Foldable t => t a -> Builder
-- lineHuh a = if null a then mempty else line

-- FIXME : raise an error if a DEBUG mode term is emitted
debugOnly' :: DafnyPrinter a => a -> Builder
debugOnly' a = do
  (_, b) <- ask
  if b
    then pp a
    else pp "/* (DEBUG) */"

debugOnly :: (Show e, DafnyPrinter a) => e -> a -> Builder
debugOnly e d = do
  (_, b) <- ask
  if b
    then pp d
    else "// (DEBUG)" <+> show e

infixr 6 <!>

class DafnyPrinter a where
  pp :: a -> Builder

(<!>) :: (DafnyPrinter a, DafnyPrinter b) => a -> b -> Builder
a <!> b = pp a <> pp b
{-# INLINE (<!>) #-}

(<+>) :: (DafnyPrinter a, DafnyPrinter b) => a -> b -> Builder
a <+> b = a <!> space <!> b
{-# INLINE (<+>) #-}


instance DafnyPrinter Builder where
  pp = id
  {-# INLINE pp #-}

instance DafnyPrinter Int where
  pp = P.pretty

instance DafnyPrinter Char where
  pp = P.pretty

instance DafnyPrinter String where
  pp = P.pretty

instance DafnyPrinter AST where
  pp = vsep

instance DafnyPrinter Ty where
  pp TNat               = pp "nat"
  pp TInt               = pp "int"
  pp TBool              = pp "bool"
  pp (TArrow tys ty)    = tupled tys <+> "->" <+> ty
  pp TMeasured          = debugOnly' $ pp "measured"
  pp (TQReg n)          = debugOnly' $ "qreg" <+> n
  pp (TSeq ty)          = "seq<" <!> ty <!> ">"
  pp (TEmit (TAny s))    = pp s

instance DafnyPrinter MethodType where
  pp ty@MethodType {mtSrcParams=ts, mtSrcReturns=ts'} = debugOnly ty $
    tupled ts <+> "->" <+> tupled ts'

instance DafnyPrinter MethodElem where
  pp tt = debugOnly tt $ ppSub tt
    where
      ppSub (MTyPure x ty)   = debugOnly tt $ fromString x <+> ":" <+> ty
      ppSub (MTyQuantum x e) = fromString x <!> "[" <!> e <!> "]"

instance DafnyPrinter AExp where
  pp (ANat n) = pp n
  pp (AVar v) = pp $ fromString v

instance DafnyPrinter QTy where
  pp TNor  = pp "nor"
  pp THad  = pp "had"
  pp TEn   = pp "en"
  pp TEn01 = pp "en01"
  pp TQft  = pp "qf"

instance DafnyPrinter (Binding ()) where
  pp (Binding x ty) = x <+> ":" <+> ty

instance DafnyPrinter QDafny where
  pp (QDafny s) = pp s

instance DafnyPrinter (QMethod ()) where
  pp (QMethod idt bds rets reqs ens blockHuh) =
    "method" <+> idt <+> tupled bds <> ppRets rets
    <!> lineHuh reqEns
    <!> (withIncr2 . by line $ (indent <!>) <$> reqEns)
    -- add a tailing newline if we have conds and blocks
    <!> lineHuh blockHuh
    <!> by line (maybeToList blockHuh)
    where ppRets [] = mempty
          ppRets r  = " returns" <+> withParen (byComma r)
          reqEns = ppConds "requires" reqs <> ppConds "ensures" ens

instance DafnyPrinter (Block ()) where
  pp = withBrace . withIncr2 . (indent <>) . by (line <> indent) . inBlock

instance DafnyPrinter (Toplevel ()) where
  pp ty = case unTop ty of
    Inl q -> pp q
    Inr q -> pp q


instance DafnyPrinter (Stmt ()) where
  pp (SEmit (SBlock b)) = pp b
  pp (SEmit f@(SForEmit idf initf bound invs b)) =
    "for " <!> fromString idf <!> " := " <!> initf <!> " to " <!> bound
      <!> "\n"
      <!> withIncr2 (indent <> byLineT (("invariant" <+>) <$> invs))
      <!> b

  pp (SDafny s') = pp s'

  pp s@(SFor idx boundl boundr eG invs seps body) = debugOnly s $
    "for"
    <+> fromString idx <+> "∈" <+> withBracket (boundl <+> ".." <+> boundr)
    <+> "with" <+> eG <!> line
    <!> withIncr2 (indent <> byLineT (("invariant" <+>) <$> invs))
    <!> body

  -- Statements that end with a SemiColon
  pp s@(SIf eg sep block) = debugOnly s $
    "if" <+> withParen eg <!> line <!>
    indent <!> "seperates" <+> sep <!> line <!>
    block

  pp s = ppStmt s <> pp ';'
    where
      ppStmt :: Stmt' -> Builder
      ppStmt (SVar bd Nothing) = "var " <!> bd
      ppStmt (SVar bd (Just e)) = "var " <!> bd <!> " := " <!> e
      ppStmt (v ::=: e) = fromString v <!> " := " <!> e
      ppStmt (SCall v es) = fromString v <!> withParen (byComma es)
      ppStmt (SEmit s') = ppEmit s'
      ppStmt (SAssert e) = "assert " <!> e
      ppStmt (e1 :*=: e2) = debugOnly s $
        e1 <+> "*=" <+> λHuh e2
      ppStmt e = "// undefined pper for Stmt : " <!> fromString (show e)

      λHuh e@(ELambda {}) = "λ" <+> e
      λHuh e              = pp e

      ppEmit :: EmitStmt -> Builder
      ppEmit (SVars bds e) = "var" <+> byComma bds <+> ":=" <+> e
      ppEmit (vs :*:=: rhs)  = case rhs of
        [] -> mempty
        _  -> byComma (fromString <$> vs) <+> ":=" <+> byComma (withParen <$> rhs)
      -- ppEmit (SIfDafny e b) = "if " <!> withParen (pp e) <!> b
      ppEmit _             = error "Should have been handled!!"

instance DafnyPrinter GuardExp where
  pp (GEPartition p _) = pp p

instance DafnyPrinter (Exp ()) where
  pp (ENum n) = pp n
  pp (EVar v) = pp (fromString v)
  pp (EBool b) = pp $ if b then "true" else "false"
  pp (EEmit e) = pp e
  pp (EOp1 ONeg e1) = "-" <+> e1
  pp (EOp2 op e1 e2) = ppOp2 op (pp e1) (pp e2)
  -- parentheses are critical to forall expressions!
  pp (EForall x eb e) =
    withParen $ "forall " <!> x  <!> beb eb <!> " :: " <!> e
    where
      beb (Just eb') = " | " <!> eb'
      beb Nothing    = mempty
  pp e@EHad = debugOnly e "H"
  pp e@(ESpec p qt specs) = debugOnly e $
    "{" <+> p <+> ":" <+> qt  <+> "↦" <+> byComma specs <+> "}"
  pp e@(EApp v es) = fromString v <!> withParen (byComma es)
  pp e@(EMeasure s) = debugOnly e $
    "measure" <+> s
  pp EWildcard = pp "_"
  pp (ELambda el) = pp el
  pp e = "//" <!> fromString (show e) <!> " should not be in emitted form!"

instance (Show f, DafnyPrinter f) => DafnyPrinter (LambdaF f) where
  pp e@(LambdaF{ bPhase, bBases, ePhase, eBases }) =
    case (bPhase, ePhase) of
      (PhaseWildCard, PhaseWildCard) ->
        tupled (fromString <$> bBases) <+> "=>" <+> tupled eBases
      (_, _) -> debugOnly e $
        bPhase <+>
        "~" <+> tupled (fromString <$> bBases) <+>
        "=>" <+>
        ePhase <+> "~" <+> tupled eBases

instance DafnyPrinter Intv where
  pp e@(Intv e1 e2) = debugOnly e $
    withBracket $ e1 <+> ".." <+> e2

instance (DafnyPrinter f, Show f) => DafnyPrinter (SpecExpF f) where
  pp s = debugOnly s ppSubterm
    where
      ppSubterm = case s of
        SEWildcard -> pp "_"
        SESpecNor (SpecNorF v1 e2) -> "⊗" <+> fromString v1 <+> '.' <+> e2
        SESpecHad (SpecHadF v1 p) -> "⊗" <+> fromString v1 <+> '.' <+> p
        SESpecEn (SpecEnF v1 intv a p es) ->
          "Σ" <+> fromString v1 <+> "∈" <+> intv <+> '.' <+> a <+> p <+>
          withParen (byComma es)
        SESpecEn01 (SpecEn01F v1 intv1 a p v2 intv2 e5) ->
          "Σ" <+> fromString v1 <+> "∈" <+> intv1 <+> '.' <+>
          "⊗" <+> fromString v2 <+> "∈" <+> intv2 <+> '.' <+>
          a <+> p <+> withParen (byComma e5)

instance DafnyPrinter f => DafnyPrinter (Maybe f) where
  pp Nothing  = pp "_"
  pp (Just x) = pp x

instance (Show f, DafnyPrinter f) => DafnyPrinter (PhaseExpF f) where
  pp p = debugOnly p $ case p of
    PhaseZ                -> pp "1"
    PhaseWildCard         -> pp "_"
    PhaseOmega e1 e2      -> "ω" <!> withParen (byComma [e1, e2])
    PhaseSumOmega i e1 e2 -> "Ω" <+> i <+> "." <+> withParen (byComma [e1, e2])

instance (Show f, DafnyPrinter f) => DafnyPrinter (AmpExpF f) where
  pp p = debugOnly p $ case p of
    ADefault     -> mempty
    AISqrt en ed -> "isqpp " <+> withParen (byComma [en, ed])
    ASin e       -> "sin" <!> withParen (pp e)
    ACos e       -> "cos" <!> withParen (pp e)


instance DafnyPrinter EmitExp where
  pp (e1 :@: e2) = e1 <!> "[" <!> e2 <!> "]"
  pp (e1 :@@: (e2, e3)) = e1 <!> "[" <!> e2 <!> ".." <!> e3 <!> "]"
  pp EMtSeq = pp "[]"
  pp (EMakeSeq ty e ee) =
    "seq<" <!> ty <!> ">" <!> withParen (e <!> ", " <!> ee)
  pp (EDafnyVar s) = pp (fromString s)
  pp (EOpChained e eos) =
    foldl (\el (op, er) -> ppOp2 op el (pp er)) (pp e) eos
  pp (ECard e) = "|" <!> e <!> "|"
  pp (ECall v es) = fromString v <!> withParen (byComma es)
  pp (EMultiLambda vs e) = withParen (byComma (fromString <$> vs)) <+> "=>" <+> e
  pp (EAsReal e) =
    withParen (withParen e <+> "as real")

instance DafnyPrinter Range where
  pp rr@(Range v l r) = debugOnly rr $ pp (EVar v :@@: (l, r))

instance DafnyPrinter Partition where
  pp pp@(Partition p) = debugOnly pp $ byComma p

instance DafnyPrinter Loc where
  pp = pp . fromString . deref

instance DafnyPrinter Locus where
  pp st@(Locus {loc=l, part=p, qty, degrees=dgrs}) = debugOnly st $
    l <+> "↦" <+> p <+> "::" <+> qty <+> withBracket (byComma dgrs)


instance DafnyPrinter PhaseRef where
  pp PhaseRef{prBase, prRepr} =
    prRepr <+> "/" <+> prBase

instance DafnyPrinter EmitData where
  pp EmitData{evPhaseRef, evBasis, evAmp} = byComma $
    [ "phase:" <+> evPhaseRef
    , "ket:"   <+> evBasis
    , "amp:"   <+> evAmp
    ]


instance (DafnyPrinter a, DafnyPrinter b) => DafnyPrinter (a, b) where
  pp t'@(a, b) = withParen . byComma $ [pp a, pp b]

instance ( DafnyPrinter a
         , DafnyPrinter b
         , DafnyPrinter c) => DafnyPrinter (a, b, c) where
  pp t'@(a, b, c) =
    withParen . byComma $ [pp a, pp b, pp c]

-- instance (Show f, DafnyPrinter f) => DafnyPrinter (QSpecF f) where
--   pp q@QSpecF{amp, phase, spec} = debugOnly q $
--     amp <+> phase <+> "~" <+> spec


instance ( DafnyPrinter k, DafnyPrinter v
         ) => DafnyPrinter (Map.Map k v) where
  pp m' = debugOnly' $
    byLineT ((indent <>) . row <$> m)
    where
      m = Map.toList m'
      row (a, b) = a <+> "↦" <+> b

instance DafnyPrinter MTy where
  pp (MTy (Inl ty)) = pp ty
  pp (MTy (Inr m)) =
    byComma (mtSrcParams m) <+> "↪" <+> byComma (mtSrcReturns m)

-- | Warning: don't emit parentheses in `ppOp2` because `EOpChained` relies
-- on this function not to be parenthesized
-- TODO: I want to get the precedence right here.
ppOp2 :: Op2 -> Builder -> Builder -> Builder
ppOp2 ONor b1 b2 = "nor" <!> withParen (byComma [b1, b2])
ppOp2 op b1 b2 =  parenOpt b1 <!> opSign <!> parenOpt b2
  where
    parenOpt :: Builder -> Builder
    parenOpt =
      case op of
        OAnd -> withParen
        OOr  -> withParen
        OMod -> withParen -- mod is a fragile operator
        ODiv -> withParen
        _    -> id

    opSign :: TB.Builder
    opSign = fromString $
      case op of
        OAnd -> " && "
        OOr  -> " || "
        OAdd -> " + "
        OSub -> " - "
        OMul -> " * "
        OMod -> " % "
        ODiv -> " / "
        OEq  -> " == "
        OLt  -> " < "
        OLe  -> " <= "
        OGt  -> " > "
        OGe  -> " >= "

ppConds :: DafnyPrinter a => a -> [Exp'] -> [Builder]
ppConds s = map ((s <!> space) <!>)

runBuilder :: DafnyPrinter a => Int -> Bool -> a -> Text
runBuilder i debug = TB.toLazyText . flip runReader (i, debug) . doPp . pp

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

--------------------------------------------------------------------------------
-- Debugging Instances
--------------------------------------------------------------------------------

instance DafnyPrinter [Int] where
  pp = withBracket . byComma

instance DafnyPrinter TState where
  pp TState{_sSt, _xSt, _emitSt} = byLineT $
    [ pp "Partition Reference State:"
    , pp (byLineT <$> _xSt)
    , pp "Partition State:"
    , pp _sSt
    , pp "Renaming State:"
    , pp _emitSt
    ]

instance (DafnyPrinter a, DafnyPrinter b) => DafnyPrinter (a :+: b) where
  pp (Inl a) = pp a
  pp (Inr b) = pp b
