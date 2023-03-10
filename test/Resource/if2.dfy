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
  var g__seq__nat___emited_3 : seq<nat>;
  var q__seq__nat___emited_4 : seq<nat>;
  var p__seq__nat___emited_5 : seq<nat>;
  var g__seq__nat___emited_6 : seq<nat>;
  var g__7__seq__nat___emited_8 : seq<nat>;
  var q__seq__nat___emited_9 : seq<nat>;
  var g__10__seq__nat___emited_12 : seq<nat>;
  var q__11__seq__nat___emited_13 : seq<nat>;
  var p__seq__nat___emited_14 : seq<nat>;
  
  // Method Definition
  q__seq__nat___emited_1 := seq<nat>(1, _ => 0);
  p__seq__nat___emited_2 := seq<nat>(1, _ => 0);
  g__seq__nat___emited_3 := seq<nat>(1, _ => 0);
  // Cast TNor ==> THad
  q__seq__nat___emited_4 := CastNorHad(q__seq__nat___emited_1);
  // Cast TNor ==> THad
  p__seq__nat___emited_5 := CastNorHad(p__seq__nat___emited_2);
  {
    // Cast TNor ==> TCH
    g__seq__nat___emited_6 := CastNorCH10(g__seq__nat___emited_3);
    g__7__seq__nat___emited_8 := g__seq__nat___emited_6;
    g__seq__nat___emited_6 := Map(x => 2 % 1 + x, g__seq__nat___emited_6);
    g__seq__nat___emited_6 := g__7__seq__nat___emited_8 + g__seq__nat___emited_6;
    // Body Session + Guard Session
    q__seq__nat___emited_9 := seq<nat>(|g__7__seq__nat___emited_8|, _ => 1) + seq<nat>(|g__7__seq__nat___emited_8|, _ => 0);
  }

  {
    g__10__seq__nat___emited_12 := g__seq__nat___emited_6;
    q__11__seq__nat___emited_13 := q__seq__nat___emited_9;
    q__seq__nat___emited_9 := Map(x => 2 % 1 + x, q__seq__nat___emited_9);
    g__seq__nat___emited_6 := Map(x => 2 % 1 + x, g__seq__nat___emited_6);
    g__seq__nat___emited_6 := g__10__seq__nat___emited_12 + g__seq__nat___emited_6;
    q__seq__nat___emited_9 := q__11__seq__nat___emited_13 + q__seq__nat___emited_9;
    // Body Session + Guard Session
    p__seq__nat___emited_14 := seq<nat>(|g__10__seq__nat___emited_12|, _ => 1) + seq<nat>(|g__10__seq__nat___emited_12|, _ => 0);
  }

}

}
