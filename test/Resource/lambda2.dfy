include "../../external//QPreludeUntyped.dfy"
include "../../external//libraries/src/Collections/Sequences/Seq.dfy"
include "../../external//libraries/src/NonlinearArithmetic/Power2.dfy"

// target Dafny version: 3.12.0
abstract module QafnyDefault {
import opened QPreludeUntyped
import opened Seq
import opened Power2

method TestLambda ()
  requires forall i : nat | 0 <= i < 2 :: q_0_10___seqL_nat_R___0__emit[i] == i
{
  // Forward Declaration
  
  // Method Definition
  q_0_10___seqL_nat_R___0__emit := Map(x => 2 * x, q_0_10___seqL_nat_R___0__emit);
}

}
