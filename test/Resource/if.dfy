include "../../external/QPreludeUntyped.dfy"

method DeutschJozsa (n : nat)
{
  var q__seq__nat___emited_1 : seq<nat> := seq<nat>(1, _ => 0);
  var p__seq__nat___emited_2 : seq<nat> := seq<nat>(1, _ => 0);
  var q__seq__nat___emited_3 : seq<nat> := CastNorHad(q__seq__nat___emited_1);
  var p__seq__nat___emited_4 : seq<nat> := CastNorHad(p__seq__nat___emited_2);
  if (//ESession (Session [Ran "q" (ENum 0) (ENum 1)]) should not be in emitted form!){
    // undefined builder for Stmt : SApply (Session [Ran "p" (ENum 0) (ENum 1)]) (ECl "x" (EOp2 OMod (EOp2 OAdd (EVar "x") (ENum 1)) (ENum 2)));
}
;
}

