include "../../external/QPreludeUntyped.dfy"
include "../../external/libraries/src/Collections/Sequences/Seq.dfy"
include "../../external/libraries/src/NonlinearArithmetic/Power2.dfy"

// target Dafny version: 3.12.0
abstract module QafnyDefault {
import opened QPreludeUntyped
import opened Seq
import opened Power2

method For0 (n : nat)
{
  // Forward Declaration
  var q__seq__nat___emited_1 : seq<nat>;
  var p__seq__nat___emited_2 : seq<nat>;
  var q__seq__nat___emited_3 : seq<nat>;
  var p__seq__nat___emited_4 : seq<nat>;
  var q__5__seq__nat___emited_6 : seq<nat>;
  var q__seq__nat___emited_7 : seq<nat>;
  var p__8__seq__nat___emited_9 : seq<nat>;
  
  // Method Definition
  q__seq__nat___emited_1 := seq<nat>(1, _ => 0);
  p__seq__nat___emited_2 := seq<nat>(1, _ => 0);
  // Cast TNor ==> THad
  q__seq__nat___emited_3 := CastNorHad(q__seq__nat___emited_1);
  {
    // Cast TNor ==> TCH
    p__seq__nat___emited_4 := CastNorCH10(p__seq__nat___emited_2);
    q__5__seq__nat___emited_6 := q__seq__nat___emited_3;
    q__seq__nat___emited_7 := [];
    for i := 0 to 1
    {
      p__8__seq__nat___emited_9 := p__seq__nat___emited_4;
      {
        p__seq__nat___emited_4 := Map(x => x + 1 % 2, p__seq__nat___emited_4);
      }

      p__seq__nat___emited_4 := p__seq__nat___emited_4 + p__8__seq__nat___emited_9;
      q__seq__nat___emited_7 := q__seq__nat___emited_7 + Map(x__lambda => x__lambda + Pow2(i), q__seq__nat___emited_7);
    }

  }

}

}
