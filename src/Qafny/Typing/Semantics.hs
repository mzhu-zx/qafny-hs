module Qafny.Typing.Semantics where

import           Qafny.Syntax.AST

-- * "Semantics of Entanglement Types"

data TyComp
  = TL [Ty]
  | T0 Ty

class TyInjection a where
  tyInj :: a -> Maybe TyComp 

instance TyInjection Ty where
  tyInj = pure . T0

instance TyInjection [Ty] where
  tyInj = pure . TL


data TySem
  = TySem { tsKets  :: Maybe TyComp
          , tsPhase :: Maybe TyComp
          , tsInner :: Maybe TySem
          }

interp :: QTy -> TySem
interp qty = TySem {tsKets, tsPhase, tsInner}
  where
    (tsKets, tsPhase, tsInner) = case qty of
      TNor -> ( tyInj (TSeq TNat)
              , Nothing
              , Nothing
              )
      THad -> ( Nothing
              , tyInj (TSeq TNat)
              , Nothing
              )
      TEn  -> ( tyInj [TSeq TNat]
              , tyInj $ TSeq TNat
              , Nothing
              )
      TEn01-> ( tyInj [TSeq (TSeq TNat)]
              , tyInj $ TSeq TNat
              , Nothing
              )
      TQft -> ( tyInj [TSeq TNat]
              , Nothing
              , pure $ interp TEn
              )
