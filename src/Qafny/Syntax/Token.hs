{-# LANGUAGE
    DeriveDataTypeable
  #-}
module Qafny.Syntax.Token where
import           Text.Printf (printf)
import           Data.Data

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
  | TSplit | TAt
  | TMeasure | TRepr
  | TUnicodeMap
  | TUnicodeTensor
  | TUnicodeOmega
  | TUnicodeSumOmega

  -- Delimiters
  | TLPar | TRPar | TTilde
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
  | TArrow | TTyArrow | TMeasured
  | TNat | TInt | TBool
  | TSeq | TNor | THad | TEn | TEn01
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

  -- Amplitudes
  | TISqrt | TSin | TCos 

  -- Gates
  | THApp | TQFT | TRQFT

  -- EOF
  | TEOF
   deriving (Show, Eq)


data SrcLoc = SrcLoc
  { sLine   :: !Int
  , sColumn :: !Int
  }
  deriving (Typeable, Data)

instance Show SrcLoc where
  show s = printf "(%d:%d)" (sLine s) (sColumn s)

type SToken = (SrcLoc, Token)

