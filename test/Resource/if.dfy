include "../../external//QPreludeUntyped.dfy"
include "../../external//libraries/src/Collections/Sequences/Seq.dfy"
include "../../external//libraries/src/NonlinearArithmetic/Power2.dfy"

// target Dafny version: 3.12.0
abstract module QafnyDefault {
import opened QPreludeUntyped
import opened Seq
import opened Power2


// For Qafny Commit: 561f5bbbcb1f81abacf2654b75761d1370184ad4

method GHZ0 (n : nat)
{
  // Forward Declaration
  var q__0__1__seq__nat____6 : seq<nat>;
  var p__0__1__seq__nat____5 : seq<nat>;
  var p__0__1__seq__nat____4 : seq<nat>;
  var p__0__1__seq__nat____3 : seq<nat>;
  var q__0__1__seq__nat____2 : seq<nat>;
  var p__0__1__seq__nat____1 : seq<nat>;
  var q__0__1__seq__nat____0 : seq<nat>;
  
  // Method Definition
  q__0__1__seq__nat____0 := seq<nat>(1, _ => 0);
  p__0__1__seq__nat____1 := seq<nat>(1, _ => 0);
  // Cast TNor ==> THad
  q__0__1__seq__nat____2 := CastNorHad(q__0__1__seq__nat____0);
  // Cast Body Partition TNor => TCH
  // Cast TNor ==> TCH
  p__0__1__seq__nat____3 := CastNorCH10(p__0__1__seq__nat____1);
  p__0__1__seq__nat____4 := p__0__1__seq__nat____5;
  {
    p__0__1__seq__nat____5 := Map(x => x + 1 % 2, p__0__1__seq__nat____5);
  }

  p__0__1__seq__nat____5 := p__0__1__seq__nat____5 + p__0__1__seq__nat____4;
  // Merge: Body partition + the Guard partition.
  q__0__1__seq__nat____6 := seq<nat>(|p__0__1__seq__nat____5|, _ => 0 + 1) + seq<nat>(|p__0__1__seq__nat____4|, _ => 0);
}

}
