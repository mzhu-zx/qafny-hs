include "../../external//QPreludeUntyped.dfy"
include "../../external//libraries/src/Collections/Sequences/Seq.dfy"
include "../../external//libraries/src/NonlinearArithmetic/Power2.dfy"

// target Dafny version: 3.12.0
abstract module QafnyDefault {
import opened QPreludeUntyped
import opened Seq
import opened Power2

method Test ()
  requires forall i : nat | 0 <= i < 10 :: q__0__10__seq__nat____0[i] == 0
{
  // Forward Declaration
  var q__0__1__seq__nat____3 : seq<nat>;
  var q__1__10__seq__nat____2 : seq<nat>;
  var q__0__1__seq__nat____1 : seq<nat>;
  
  // Method Definition
  q__0__1__seq__nat____1 := q__0__10__seq__nat____0[0..1];
  q__1__10__seq__nat____2 := q__0__10__seq__nat____0[1..10];
  // Cast TNor ==> THad
  q__0__1__seq__nat____3 := CastNorHad(q__0__1__seq__nat____1);
}

}
