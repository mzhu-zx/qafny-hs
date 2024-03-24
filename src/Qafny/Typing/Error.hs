{-# LANGUAGE
    NamedFieldPuns
  , TypeApplications
  #-}

module Qafny.Typing.Error where

import qualified Control.Carrier.Error.Either as ErrE
import           Control.Effect.Error
import           Qafny.Syntax.AST
    (Range)
import           Qafny.Syntax.Emit
    (byComma, showEmit0)
import           Qafny.Syntax.IR
import           Text.Printf
    (printf)

data SCError
  = SplitENError Locus Range Range [Range]
  | SplitOtherError String


instance Show SCError where
  show (SplitENError s@Locus{part} r0 rAff rs) = printf
    ("The partition %s cannot be obtained from the 'EN' partition %s.\n" ++
     "Reason: it requires tearing the range %s apart into %s.\n" ++
     "Advice: Use `EN01` isntead.\n" ++
     "Info: %s\n")
    (showEmit0 r0)
    (showEmit0 part)
    (showEmit0 rAff)
    (showEmit0 (byComma rs))
    (showEmit0 s)
  show (SplitOtherError s) = s

failureAsSCError
  :: ( Has (Error SCError) sig m )
    => ErrE.ErrorC String m b -> m b
failureAsSCError m = do
  e <- ErrE.runError @String m
  case e of
    Left err -> throwError $ SplitOtherError err
    Right v  -> return v

hdlSCError
  :: ( Has (Error String) sig m )
    => ErrE.ErrorC SCError m b -> m b
hdlSCError m = do
  e <- ErrE.runError @SCError m
  case e of
    Left err -> throwError $ show err
    Right v  -> return v

