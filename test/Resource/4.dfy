include "../../external/QPreludeUntyped.dfy"

method DeutschJozsa (n : nat)
{
  var q__seq__nat___emited_1 : seq<nat> := seq<nat>(1, _ => 0);
  var p__seq__nat___emited_2 : seq<nat> := seq<nat>(n, _ => 1);
  var q__seq__nat___emited_3 : seq<nat> := CastNorHad(q__seq__nat___emited_1);
  var p__seq__nat___emited_4 : seq<nat> := CastNorHad(p__seq__nat___emited_2);
}

