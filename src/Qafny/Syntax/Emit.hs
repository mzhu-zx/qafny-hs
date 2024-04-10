{-# LANGUAGE
    FlexibleContexts
  , FlexibleInstances
  , GeneralizedNewtypeDeriving
  , NamedFieldPuns
  #-}

module Qafny.Syntax.Emit where

import qualified Data.Map.Strict                         as Map
import           Data.Sum

-- Text
import qualified Data.Text                               as TS
import qualified Data.Text.Lazy                          as TL

-- Qafny
import           Qafny.Syntax.AST
import           Qafny.Syntax.EmitBinding
import           Qafny.Syntax.IR
import           Qafny.Syntax.Render

-- PP
import           Prettyprinter
    (lbrace, rbrace, space)
import qualified Prettyprinter                           as P

-------------------- Builder --------------------
type Builder = P.Doc TS.Text

viaShow :: Show e => e -> Builder
viaShow = P.viaShow

line :: Builder
line = P.line

incr2 :: DafnyPrinter a => a -> Builder
incr2 = P.indent 2 . pp

vsep :: DafnyPrinter a => [a] -> Builder
vsep = P.vsep . (pp <$>)

encloseSep
  :: (DafnyPrinter delim, DafnyPrinter sep, DafnyPrinter body)
  => delim -> delim -> sep -> [body] -> Builder
encloseSep l r s bs =
  P.encloseSep (pp l) (pp r) (pp s) (pp <$> bs)

parens :: DafnyPrinter a => a -> Builder
parens = P.parens . pp

brackets :: DafnyPrinter a => a -> Builder
brackets = P.brackets . pp

braces :: DafnyPrinter a => a -> Builder
braces = P.braces . pp

byComma :: DafnyPrinter a => [a] -> Builder
byComma = P.cat . P.punctuate P.comma . (pp <$>)

list :: DafnyPrinter a => [a] -> Builder
list = P.list . (pp <$>)

tupled :: DafnyPrinter a => [a] -> Builder
tupled = P.tupled . (pp <$>)

debugOnly' :: DafnyPrinter a => a -> Builder
debugOnly' a = do
  P.annotate (TS.pack "/* (DEBUG) */") (pp a)

debugOnly :: (Show e, DafnyPrinter a) => e -> a -> Builder
debugOnly e a = do
  P.annotate (TS.pack "/* (DEBUG)" <> TS.pack (show e) <> TS.pack "*/") (pp a)

infixr 6 <!>

class DafnyPrinter a where
  pp :: a -> Builder

(<!>) :: (DafnyPrinter a, DafnyPrinter b) => a -> b -> Builder
a <!> b = pp a <> pp b
{-# INLINE (<!>) #-}

(<+>) :: (DafnyPrinter a, DafnyPrinter b) => a -> b -> Builder
a <+> b = pp a P.<+> pp b
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
  pp TNat             = pp "nat"
  pp TInt             = pp "int"
  pp TBool            = pp "bool"
  pp (TArrow tys ty)  = tupled tys <+> "->" <+> ty
  pp TMeasured        = debugOnly' $ pp "measured"
  pp (TQReg n)        = debugOnly' $ "qreg" <+> n
  pp (TSeq ty)        = "seq<" <!> ty <!> ">"
  pp (TEmit (TAny s)) = pp s

instance DafnyPrinter MethodType where
  pp ty@MethodType {mtSrcParams=ts, mtSrcReturns=ts'} = debugOnly ty $
    tupled ts <+> "->" <+> tupled ts'

instance DafnyPrinter MethodElem where
  pp tt = debugOnly tt $ ppSub tt
    where
      ppSub (MTyPure x ty)   = debugOnly tt $ x <+> ":" <+> ty
      ppSub (MTyQuantum x e) = x <!> "[" <!> e <!> "]"

instance DafnyPrinter AExp where
  pp (ANat n) = pp n
  pp (AVar v) = pp v

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
  pp (QMethod idt bds rets reqs ens blockMaybe) =
    "method" <+> idt <+> tupled bds <+> ppRets rets
    <!> incr2 (vsep reqEns)
    <!> maybe mempty pp blockMaybe
    where
      ppRets [] = mempty
      ppRets x  = tupled x
      reqEns =
        (("requires" <+>) <$> reqs) <>
        (("ensures"  <+>) <$> ens)

instance DafnyPrinter (Block ()) where
  pp (Block b) = vsep
    [ lbrace
    , incr2 (vsep b)
    , rbrace]


instance (DafnyPrinter a, DafnyPrinter b) => DafnyPrinter (a :+: b) where
  pp (Inl a) = pp a
  pp (Inr b) = pp b

instance DafnyPrinter (Toplevel ()) where
  pp = pp . unTop

ppInvs :: [Exp'] -> Builder
ppInvs = vsep . (("invariant" <+>) <$> )

instance DafnyPrinter (Stmt ()) where
  pp (SEmit (SBlock b)) = pp b
  pp (SEmit f@(SForEmit idf initf bound invs b)) =
    "for " <!> idf <!> " := " <!> initf <!> " to " <!> bound <!> line
    <!> ppInvs invs
    <!> b

  pp (SDafny s') = pp s'

  pp s@(SFor idx boundl boundr eG invs seps body) = debugOnly s $
    "for" <+> idx <+> "∈" <+> brackets (boundl <+> ".." <+> boundr)
    <+> "with" <+> eG <!> (line :: Builder)
    <!> ppInvs invs
    <!> body

  -- Statements that end with a SemiColon
  pp s@(SIf eg sep block) = debugOnly s $
    "if" <+> parens eg <!> line
    <!> incr2 ("seperates" <+> sep) <!> line
    <!> block

  pp s = ppStmt s <> pp ';'
    where
      ppStmt :: Stmt' -> Builder
      ppStmt (SVar bd Nothing) = "var " <!> bd
      ppStmt (SVar bd (Just e)) = "var " <!> bd <!> " := " <!> e
      ppStmt (v ::=: e) = v <!> " := " <!> e
      ppStmt (SCall v es) = v <!> tupled es
      ppStmt (SEmit s') = ppEmit s'
      ppStmt (SAssert e) = "assert " <!> e
      ppStmt (e1 :*=: e2) = debugOnly s $
        e1 <+> "*=" <+> λHuh e2
      ppStmt e = "// undefined pper for Stmt : " <!> viaShow e

      λHuh e@(ELambda {}) = "λ" <+> e
      λHuh e              = pp e

      ppEmit :: EmitStmt -> Builder
      ppEmit (SVars bds e) = "var" <+> byComma bds <+> ":=" <+> e
      ppEmit (vs :*:=: rhs)  = case rhs of
        [] -> mempty
        _  -> byComma vs <+> ":=" <+> byComma (parens <$> rhs)
      -- ppEmit (SIfDafny e b) = "if " <!> withParen (pp e) <!> b
      ppEmit _             = error "Should have been handled!!"

instance DafnyPrinter GuardExp where
  pp (GEPartition p _) = pp p

instance DafnyPrinter (Exp ()) where
  pp (ENum n) = pp n
  pp (EVar v) = pp v
  pp (EBool b) = pp $ if b then "true" else "false"
  pp (EEmit e) = pp e
  pp (EOp1 ONeg e1) = "-" <+> e1
  pp (EOp2 op e1 e2) = ppOp2 op (pp e1) (pp e2)
  -- parentheses are critical to forall expressions!
  pp (EForall x eb e) =
    parens $ "forall " <!> x  <!> beb eb <!> " :: " <!> e
    where
      beb (Just eb') = " | " <!> eb'
      beb Nothing    = mempty
  pp e@EHad = debugOnly e "H"
  pp e@(ESpec p qt specs) = debugOnly e $
    "{" <+> p <+> ":" <+> qt  <+> "↦" <+> byComma specs <+> "}"
  pp e@(EApp v es) = v <!> tupled es
  pp e@(EMeasure s) = debugOnly e $
    "measure" <+> s
  pp EWildcard = pp "_"
  pp (ELambda el) = pp el
  pp e = "//" <!> viaShow e <!> " should not be in emitted form!"

instance (Show f, DafnyPrinter f) => DafnyPrinter (LambdaF f) where
  pp e@(LambdaF{ bPhase, bBases, ePhase, eBases }) =
    case (bPhase, ePhase) of
      (PhaseWildCard, PhaseWildCard) ->
        tupled bBases <+> "=>" <+> tupled eBases
      (_, _) -> debugOnly e $
        bPhase <+>
        "~" <+> tupled bBases <+>
        "=>" <+>
        ePhase <+> "~" <+> tupled eBases

instance DafnyPrinter Intv where
  pp e@(Intv e1 e2) = debugOnly e $
    brackets $ e1 <+> ".." <+> e2

instance (DafnyPrinter f, Show f) => DafnyPrinter (SpecExpF f) where
  pp s = debugOnly s ppSubterm
    where
      ppSubterm = case s of
        SEWildcard -> pp "_"
        SESpecNor (SpecNorF v1 e2) -> "⊗" <+> v1 <+> '.' <+> e2
        SESpecHad (SpecHadF v1 p) -> "⊗" <+> v1 <+> '.' <+> p
        SESpecEn (SpecEnF v1 intv a p es) ->
          "Σ" <+> v1 <+> "∈" <+> intv <+> '.' <+> a <+> p <+> tupled es
        SESpecEn01 (SpecEn01F v1 intv1 a p v2 intv2 e5) ->
          "Σ" <+> v1 <+> "∈" <+> intv1 <+> '.' <+>
          "⊗" <+> v2 <+> "∈" <+> intv2 <+> '.' <+>
          a <+> p <+> tupled e5

instance DafnyPrinter f => DafnyPrinter (Maybe f) where
  pp Nothing  = pp "_"
  pp (Just x) = pp x

instance (Show f, DafnyPrinter f) => DafnyPrinter (PhaseExpF f) where
  pp p = debugOnly p $ case p of
    PhaseZ                -> pp "1"
    PhaseWildCard         -> pp "_"
    PhaseOmega e1 e2      -> "ω" <!> tupled [e1, e2]
    PhaseSumOmega i e1 e2 -> "Ω" <+> i <+> "." <+> tupled [e1, e2]

instance (Show f, DafnyPrinter f) => DafnyPrinter (AmpExpF f) where
  pp p = debugOnly p $ case p of
    ADefault     -> mempty
    AISqrt en ed -> "isqpp " <+> tupled [en, ed]
    ASin e       -> "sin" <!> parens e
    ACos e       -> "cos" <!> parens e


instance DafnyPrinter EmitExp where
  pp (e1 :@: e2) = e1 <!> "[" <!> e2 <!> "]"
  pp (e1 :@@: (e2, e3)) = e1 <!> "[" <!> e2 <!> ".." <!> e3 <!> "]"
  pp EMtSeq = pp "[]"
  pp (EMakeSeq ty e ee) =
    "seq<" <!> ty <!> ">" <!> parens (e <!> ", " <!> ee)
  pp (EDafnyVar s) = pp s
  pp (EOpChained e eos) =
    foldl (\el (op, er) -> ppOp2 op el (pp er)) (pp e) eos
  pp (ECard e) = "|" <!> e <!> "|"
  pp (ECall v es) = v <!> tupled es
  pp (EMultiLambda vs e) = tupled vs <+> "=>" <+> e
  pp (EAsReal e) =
    parens (parens e <+> "as real")

instance DafnyPrinter Range where
  pp rr@(Range v l r) = debugOnly rr $ pp (EVar v :@@: (l, r))

instance DafnyPrinter Partition where
  pp par@(Partition p) = debugOnly par $ byComma p

instance DafnyPrinter Loc where
  pp = pp . deref

instance DafnyPrinter Locus where
  pp st@(Locus {loc=l, part=p, qty, degrees=dgrs}) = debugOnly st $
    l <+> "↦" <+> p <+> "::" <+> qty <+> list dgrs

instance DafnyPrinter PhaseRef where
  pp PhaseRef{prBase, prRepr} =
    prRepr <+> "/" <+> prBase

instance DafnyPrinter EmitData where
  pp EmitData{evPhaseRef, evBasis, evAmp} = list
    [ "phase:" <+> evPhaseRef
    , "ket:"   <+> evBasis
    , "amp:"   <+> evAmp
    ]


instance (DafnyPrinter a, DafnyPrinter b) => DafnyPrinter (a, b) where
  pp t'@(a, b) = tupled [pp a, pp b]

instance ( DafnyPrinter a
         , DafnyPrinter b
         , DafnyPrinter c) => DafnyPrinter (a, b, c) where
  pp t'@(a, b, c) =
    tupled $ [pp a, pp b, pp c]

-- instance (Show f, DafnyPrinter f) => DafnyPrinter (QSpecF f) where
--   pp q@QSpecF{amp, phase, spec} = debugOnly q $
--     amp <+> phase <+> "~" <+> spec


instance ( DafnyPrinter k, DafnyPrinter v
         ) => DafnyPrinter (Map.Map k v) where
  pp m' = debugOnly' $
    list (row <$> m)
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
ppOp2 ONor b1 b2 = "nor" <!> tupled [b1, b2]
ppOp2 op b1 b2 =  parenOpt b1 <!> opSign <!> parenOpt b2
  where
    parenOpt :: Builder -> Builder
    parenOpt =
      case op of
        OAnd -> parens
        OOr  -> parens
        OMod -> parens -- mod is a fragile operator
        ODiv -> parens
        _    -> id

    opSign = pp $
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
ppConds s = map ((s <+> (space :: Builder)) <!>)

runBuilder :: DafnyPrinter a => Int -> Bool -> a -> TL.Text
runBuilder i debug =
  renderLazy debug
  . P.layoutPretty P.defaultLayoutOptions
  . P.indent i
  . pp

texify :: DafnyPrinter a => a -> TL.Text
texify = runBuilder 0 False

prettyIO :: DafnyPrinter a => a -> IO ()
prettyIO = putDoc False . pp

-- showEmit :: DafnyPrinter a => a -> String
-- showEmit = TL.unpack . texify

-- -- Debug mode
-- showEmitI :: DafnyPrinter a => Int -> a -> String
-- showEmitI i = TL.unpack . runBuilder i True

-- showEmit0 :: DafnyPrinter a => a -> String
-- showEmit0 = showEmitI 0


-- Regex for OverloadedStrings
-- \(\"[^\"]+?\"\) → t\1

--------------------------------------------------------------------------------
-- Debugging Instances
--------------------------------------------------------------------------------

instance DafnyPrinter [Int] where
  pp = list

instance DafnyPrinter TState where
  pp TState{_sSt, _xSt, _emitSt} = vsep
    [ pp "Partition Reference State:"
    , ppincr2 (list <$> _xSt)
    , pp "Partition State:"
    , ppincr2 _sSt
    , pp "Renaming State:"
    , ppincr2 _emitSt
    ]
    where
      ppincr2 :: DafnyPrinter a => a -> Builder
      ppincr2 = pp . incr2
