include "../../../external//QPreludeUntyped.dfy"
include "../../../external//libraries/src/Collections/Sequences/Seq.dfy"
include "../../../external//libraries/src/NonlinearArithmetic/Power2.dfy"
include "../../../external//libraries/src/NonlinearArithmetic/Power.dfy"

// target Dafny version: 3.12.0
abstract module QafnyDefault {
import opened QPreludeUntyped
import opened Seq
import opened Power2
import opened Power
import opened DivMod

method Intros1 (N : nat, q_seq'nat'_2__emit : seq<nat>, loc__loc__requires_0_1_0__emit : seq<nat>, loc__loc__requires_0_1_1__emit : nat)
  requires N >= 2
  requires 4 == loc__loc__requires_0_1_1__emit
  requires 1 == |loc__loc__requires_0_1_0__emit|
  requires (forall i : nat | 0 <= i < 1 :: 1 == loc__loc__requires_0_1_0__emit[i])
  requires 1 == |q_seq'nat'_2__emit|
  requires (forall i : nat | 0 <= i < 1 :: q_seq'nat'_2__emit[i] == 0)
{
  var q_seq'nat'_3__emit : seq<nat> := q_seq'nat'_2__emit;
  // Forward Declaration
  reveal Map();
  reveal Pow2();
  
  // Method Definition
}

}