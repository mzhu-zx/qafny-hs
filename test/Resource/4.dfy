include "../../external//QPreludeUntyped.dfy"
include "../../external//libraries/src/Collections/Sequences/Seq.dfy"
include "../../external//libraries/src/NonlinearArithmetic/Power2.dfy"

// target Dafny version: 3.12.0
abstract module QafnyDefault {
import opened QPreludeUntyped
import opened Seq
import opened Power2

method DeutschJozsa (n : nat)
{
  // Forward Declaration
  var p__0__n__seq__nat____3 : seq<nat>;
  var q__0__1__seq__nat____2 : seq<nat>;
  var p__0__n__seq__nat____1 : seq<nat>;
  var q__0__1__seq__nat____0 : seq<nat>;
  
  // Method Definition
  q__0__1__seq__nat____0 := seq<nat>(1, _ => 0);
  p__0__n__seq__nat____1 := seq<nat>(n, _ => 1);
  // Cast TNor ==> THad
  q__0__1__seq__nat____2 := CastNorHad(q__0__1__seq__nat____0);
  // Cast TNor ==> THad
  p__0__n__seq__nat____3 := CastNorHad(p__0__n__seq__nat____1);
}

}
