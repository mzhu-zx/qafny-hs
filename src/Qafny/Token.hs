module Qafny.Token where

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

  -- Delimiters
  | TLPar | TRPar
  | TLAng | TRAng
  | TLBrace | TRBrace
  | TLBracket | TRBracket
  | TBar | TComma | TColon | TSemi
  | TDots

  -- Quantifiers
  | TForall
  | TIn
  -- Types
  | TArrow
  | TNat | TInt | TBool
  | TSeq | TNor | THad | TCH
  -- Identifiers
  | TId String

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


data SrcLoc = SrcLoc
  { sLine :: !Int 
  , sColumn :: !Int
  }
  
type SToken = (SrcLoc, Token)

