include "../../external//QPreludeUntyped.dfy"
include "../../external//libraries/src/Collections/Sequences/Seq.dfy"
include "../../external//libraries/src/NonlinearArithmetic/Power2.dfy"

// target Dafny version: 3.12.0
abstract module QafnyDefault {
import opened QPreludeUntyped
import opened Seq
import opened Power2

method SplitTest ()
{
  // Forward Declaration
  var q__2__8__seq__nat____4 : seq<nat>;
  var q__8__10__seq__nat____3 : seq<nat>;
  var q__0__2__seq__nat____2 : seq<nat>;
  var q__2__8__seq__nat____1 : seq<nat>;
  var q__0__10__seq__nat____0 : seq<nat>;
  
  // Method Definition
  q__0__10__seq__nat____0 := seq<nat>(10, _ => 0);
  q__2__8__seq__nat____1 := q__0__10__seq__nat____0[2..8];
  q__0__2__seq__nat____2 := q__0__10__seq__nat____0[0..2];
  q__8__10__seq__nat____3 := q__0__10__seq__nat____0[8..10];
  // Cast TNor ==> THad
  q__2__8__seq__nat____4 := CastNorHad(q__2__8__seq__nat____1);
}

}
