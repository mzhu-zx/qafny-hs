module Qafny.Token where

import           Qafny.SrcLoc

data Token
  -- Dafny Fragments
  = TDafny String

  -- Constants
  | TLitInt Int

  -- Assertions
  | TRequires | TEnsures | TAssert
  | TSeparates | TInv

  -- Keywords
  | TMethod | TReturns
  | TAssign | TApply
  | TVar | TIf | TCl | TFor
  | TWith
  | TMea
  | TUnicodeMap
  | TUnicodeTensor

  -- Delimiters
  | TLPar | TRPar
  | TLAng | TRAng
  | TLBrace | TRBrace
  | TLBracket | TRBracket
  | TBar | TComma | TColon | TSemi
  | TDots | TDot

  -- Quantifiers
  | TForall
  | TIn
  | TUnicodeIn
  | TUnicodeSum

  -- Types
  | TArrow
  | TNat | TInt | TBool
  | TSeq | TNor | THad | TCH | TCH01
  | TQReg

  -- Identifiers
  | TId String
  | TWildcard

  -- Comparison
  | TEq | TLe | TGe

  -- Logical
  | TAnd | TOr | TNot

  -- Arithmetics
  | TMul | TAdd | TMod | TSub

  -- Gates
  | THApp | TQFT | TRQFT

  -- EOF
  | TEOF
   deriving (Show, Eq)


type SToken = (SrcLoc, Token)

to :: SToken -> f -> HasSrcLoc f
to (sl, _) = HasSrcLoc sl
