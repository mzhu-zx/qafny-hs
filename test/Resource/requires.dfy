include "../../external//QPreludeUntyped.dfy"
include "../../external//libraries/src/Collections/Sequences/Seq.dfy"
include "../../external//libraries/src/NonlinearArithmetic/Power2.dfy"

// target Dafny version: 3.12.0
abstract module QafnyDefault {
import opened QPreludeUntyped
import opened Seq
import opened Power2

method CH (n : nat, m : nat)
  requires forall i : nat | 0 <= i < 10 :: q_0_n___seqL_nat_R___0__emit[i] == 0 && forall i : nat | 0 <= i < 10 :: q_m_10___seqL_nat_R___1__emit[i] == 1
  requires n < m < 10
{
  // Forward Declaration
  
  // Method Definition
}

}
