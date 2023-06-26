include "../../external//QPreludeUntyped.dfy"
include "../../external//libraries/src/Collections/Sequences/Seq.dfy"
include "../../external//libraries/src/NonlinearArithmetic/Power2.dfy"

// target Dafny version: 3.12.0
abstract module QafnyDefault {
import opened QPreludeUntyped
import opened Seq
import opened Power2

method Test (q__seq__nat____0 : seq<nat>)
  requires forall i : nat | 0 <= i < 10 :: q__seq__nat____0[i] == 0
{
  // Forward Declaration
  var q__seq__nat____1 : seq<nat>;
  
  // Method Definition
  // Cast TNor ==> THad
  q__seq__nat____1 := CastNorHad(q__seq__nat____0);
}

}
