include "../../external/QPreludeUntyped.dfy"
include "../../external/libraries/src/Collections/Sequences/Seq.dfy"

// target Dafny version: 3.12.0
abstract module QafnyDefault {
import opened QPreludeUntyped
import opened Seq

method GHZ0 (n : nat)
{
  // Forward Declaration
  var q__seq__nat___emited_1 : seq<nat>;
  var p__seq__nat___emited_2 : seq<nat>;
  var q__seq__nat___emited_3 : seq<nat>;
  var p__seq__nat___emited_4 : seq<nat>;
  var p__5__seq__nat___emited_6 : seq<nat>;
  var q__seq__nat___emited_7 : seq<nat>;
  
  // Method Definition
  q__seq__nat___emited_1 := seq<nat>(1, _ => 0);
  p__seq__nat___emited_2 := seq<nat>(1, _ => 0);
  // Cast TNor ==> THad
  q__seq__nat___emited_3 := CastNorHad(q__seq__nat___emited_1);
  {
    // Cast TNor ==> TCH
    p__seq__nat___emited_4 := CastNorCH10(p__seq__nat___emited_2);
    p__5__seq__nat___emited_6 := p__seq__nat___emited_4;
    p__seq__nat___emited_4 := Map(x => 2 % 1 + x, p__seq__nat___emited_4);
    p__seq__nat___emited_4 := p__5__seq__nat___emited_6 + p__seq__nat___emited_4;
    // Body Session + Guard Session
    q__seq__nat___emited_7 := seq<nat>(|p__5__seq__nat___emited_6|, _ => 1) + seq<nat>(|p__5__seq__nat___emited_6|, _ => 0);
  }

}

}
