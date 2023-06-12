include "../../external//QPreludeUntyped.dfy"
include "../../external//libraries/src/Collections/Sequences/Seq.dfy"
include "../../external//libraries/src/NonlinearArithmetic/Power2.dfy"

// target Dafny version: 3.12.0
abstract module QafnyDefault {
import opened QPreludeUntyped
import opened Seq
import opened Power2

method GHZ0 (n : nat)
{
  // Forward Declaration
  var q : seq<nat>;
  var p : seq<nat>;
  var p : seq<nat>;
  var q : seq<nat>;
  var p : seq<nat>;
  var q : seq<nat>;
  
  // Method Definition
  q__seq__nat____0 := seq<nat>(1, _ => 0);
  p__seq__nat____1 := seq<nat>(1, _ => 0);
  // Cast TNor ==> THad
  q__seq__nat____2 := CastNorHad(q__seq__nat____0);
  // Cast TNor ==> TCH
  p__seq__nat____3 := CastNorCH10(p__seq__nat____1);
  p__seq__nat____4 := p__seq__nat____3;
  {
    p__seq__nat____3 := Map(x => x + 1 % 2, p__seq__nat____3);  }

  p__seq__nat____3 := p__seq__nat____3 + p__seq__nat____4;
  // Body Session + Guard Session
  q__seq__nat____5 := seq<seq<nat>>(|p__seq__nat____3|, _ => 1) + seq<seq<nat>>(|p__seq__nat____4|, _ => 0);}

}