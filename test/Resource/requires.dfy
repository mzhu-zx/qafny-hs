include "../../external//QPreludeUntyped.dfy"
include "../../external//libraries/src/Collections/Sequences/Seq.dfy"
include "../../external//libraries/src/NonlinearArithmetic/Power2.dfy"

// target Dafny version: 3.12.0
abstract module QafnyDefault {
import opened QPreludeUntyped
import opened Seq
import opened Power2

method EN (q_0_5___seqL_nat_R___0__emit : seq<nat>, q_5_10___seqL_nat_R___1__emit : seq<nat>) returns (q_0_5___seqL_nat_R___0__emit : seq<nat>, q_5_10___seqL_nat_R___1__emit : seq<nat>)
  requires 10 == |q_0_5___seqL_nat_R___0__emit| && (forall i : nat | 0 <= i < 10 :: q_0_5___seqL_nat_R___0__emit[i] == 0) && 10 == |q_5_10___seqL_nat_R___1__emit| && (forall i : nat | 0 <= i < 10 :: q_5_10___seqL_nat_R___1__emit[i] == 1)
{
  // Forward Declaration
  
  // Method Definition
  assert 10 == |q_0_5___seqL_nat_R___0__emit|;
  assert (forall i : nat | 0 <= i < 10 :: q_0_5___seqL_nat_R___0__emit[i] == 0);
  assert 10 == |q_5_10___seqL_nat_R___1__emit|;
  assert (forall i : nat | 0 <= i < 10 :: q_5_10___seqL_nat_R___1__emit[i] == 1);
}

}
