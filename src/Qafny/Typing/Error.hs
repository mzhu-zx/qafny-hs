{-# LANGUAGE
    TypeApplications
  #-}

module Qafny.Typing.Error where

import qualified Control.Carrier.Error.Either as ErrE
import           Control.Effect.Error
import           Qafny.Env                    (STuple(..))
import           Qafny.Syntax.AST             (Range)
import           Qafny.Syntax.Emit            (byComma, showEmit0)
import           Text.Printf                  (printf)

data SCError
  = SplitENError STuple Range [Range]
  | SplitOtherError String


instance Show SCError where
  show (SplitENError s@(STuple (_, p, _)) r0 rs) = printf
    ("The partition %s cannot be obtained from the 'EN' partition %s.\n" ++
     "Reason: it requires tearing the range apart into %s.\n" ++
     "Advice: Use `EN01` isntead.\n" ++
     "Info: %s\n")
    (showEmit0 r0)
    (showEmit0 p)
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

