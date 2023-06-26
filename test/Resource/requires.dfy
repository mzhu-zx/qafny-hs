include "../../external//QPreludeUntyped.dfy"
include "../../external//libraries/src/Collections/Sequences/Seq.dfy"
include "../../external//libraries/src/NonlinearArithmetic/Power2.dfy"

// target Dafny version: 3.12.0
abstract module QafnyDefault {
import opened QPreludeUntyped
import opened Seq
import opened Power2

method GHZ (q__seq__nat____0 : seq<nat>, q__seq__nat____1 : seq<nat>, n : nat, m : nat)
  requires n < m < 10
  requires forall i : nat | 0 <= i < 10 :: q__seq__nat____0[i] == 0 && forall i : nat | 0 <= i < 10 :: q__seq__nat____1[i] == 1
{
  // Forward Declaration
  
  // Method Definition
}

}
