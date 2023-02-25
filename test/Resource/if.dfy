include "../../external/QPreludeUntyped.dfy"
// target Dafny version: 3.12.0
abstract module QafnyDefault {
import opened QPreludeUntyped

method GHZ0 (n : nat)
{
  // Forward Declaration
  var q__seq__nat___emited_1 : seq<nat>;
  var p__seq__nat___emited_2 : seq<nat>;
  var q__seq__nat___emited_3 : seq<nat>;
  var p__seq__nat___emited_4 : seq<nat>;
  var p__5__seq__nat___emited_6 : seq<nat>;
  
  // Method Definition
  var q : seq<nat> := seq<nat>(1, _ => 0);
  var p : seq<nat> := seq<nat>(1, _ => 0);
  // Cast TNor ==> THad
  q__seq__nat___emited_3 := CastNorHad(q__seq__nat___emited_1);
  {
    // Cast TNor ==> TCH
    p__seq__nat___emited_4 := CastNorCH10(p__seq__nat___emited_2);
    p__5__seq__nat___emited_6 := p__seq__nat___emited_4;
    // undefined builder for Stmt : SApply (Session [Range "p" (ENum 0) (ENum 1)]) (ECl "x" (EOp2 OMod (EOp2 OAdd (EVar "x") (ENum 1)) (ENum 2)));
    p__seq__nat___emited_4 := p__5__seq__nat___emited_6 + p__seq__nat___emited_4;
  }

}

}
