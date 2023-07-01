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
  var p__0__1__seq__nat____13 : seq<nat>;
  var q__0__1__seq__nat____12 : seq<nat>;
  var g__0__1__seq__nat____11 : seq<nat>;
  var q__0__1__seq__nat____10 : seq<nat>;
  var g__0__1__seq__nat____9 : seq<nat>;
  var q__0__1__seq__nat____8 : seq<nat>;
  var g__0__1__seq__nat____7 : seq<nat>;
  var g__0__1__seq__nat____6 : seq<nat>;
  var g__0__1__seq__nat____5 : seq<nat>;
  var p__0__1__seq__nat____4 : seq<nat>;
  var q__0__1__seq__nat____3 : seq<nat>;
  var g__0__1__seq__nat____2 : seq<nat>;
  var p__0__1__seq__nat____1 : seq<nat>;
  var q__0__1__seq__nat____0 : seq<nat>;
  
  // Method Definition
  q__0__1__seq__nat____0 := seq<nat>(1, _ => 0);
  p__0__1__seq__nat____1 := seq<nat>(1, _ => 0);
  g__0__1__seq__nat____2 := seq<nat>(1, _ => 0);
  // Cast TNor ==> THad
  q__0__1__seq__nat____3 := CastNorHad(q__0__1__seq__nat____0);
  // Cast TNor ==> THad
  p__0__1__seq__nat____4 := CastNorHad(p__0__1__seq__nat____1);
  // Cast Body Partition TNor => TCH
  // Cast TNor ==> TCH
  g__0__1__seq__nat____5 := CastNorCH10(g__0__1__seq__nat____2);
  g__0__1__seq__nat____6 := g__0__1__seq__nat____7;
  {
    g__0__1__seq__nat____7 := Map(x => x + 1 % 2, g__0__1__seq__nat____7);
  }

  g__0__1__seq__nat____7 := g__0__1__seq__nat____7 + g__0__1__seq__nat____6;
  // Merge: Body partition + the Guard partition.
  q__0__1__seq__nat____8 := seq<nat>(|g__0__1__seq__nat____7|, _ => 0 + 1) + seq<nat>(|g__0__1__seq__nat____6|, _ => 0);
  g__0__1__seq__nat____9 := g__0__1__seq__nat____11;
  q__0__1__seq__nat____10 := q__0__1__seq__nat____12;
  {
    q__0__1__seq__nat____12 := Map(x => x + 1 % 2, q__0__1__seq__nat____12);
    g__0__1__seq__nat____11 := Map(x => x + 1 % 2, g__0__1__seq__nat____11);
  }

  g__0__1__seq__nat____11 := g__0__1__seq__nat____11 + g__0__1__seq__nat____9;
  q__0__1__seq__nat____12 := q__0__1__seq__nat____12 + q__0__1__seq__nat____10;
  // Merge: Body partition + the Guard partition.
  p__0__1__seq__nat____13 := seq<nat>(|g__0__1__seq__nat____11|, _ => 0 + 1) + seq<nat>(|g__0__1__seq__nat____9|, _ => 0);
}

}
