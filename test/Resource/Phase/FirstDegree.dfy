include "../../../external//QPreludeUntyped.dfy"
include "../../../external//libraries/src/Collections/Sequences/Seq.dfy"
include "../../../external//libraries/src/NonlinearArithmetic/Power2.dfy"
include "../../../external//libraries/src/NonlinearArithmetic/Power.dfy"

// target Dafny version: 4.2.0
abstract module QafnyDefault {
import opened QPreludeUntyped
import opened Seq
import opened Power2
import opened Power
import opened DivMod

method AddQuarter (N : nat, q_seq'nat'_2__emit : seq<nat>, loc__loc__requires_0_1_0__emit : seq<nat>, loc__loc__requires_0_1_1__emit : nat) returns (q_seq'nat'_8__emit : seq<nat>, loc__loc__requires_0_1_6__emit : seq<nat>, loc__loc__requires_0_1_7__emit : nat)
  requires N >= 2
  requires 4 == loc__loc__requires_0_1_1__emit
  requires 1 == |loc__loc__requires_0_1_0__emit|
  requires (forall i : nat | 0 <= i < 1 :: 1 == loc__loc__requires_0_1_0__emit[i])
  requires 1 == |q_seq'nat'_2__emit|
  requires (forall i : nat | 0 <= i < 1 :: q_seq'nat'_2__emit[i] == 0)
  ensures 4 == loc__loc__requires_0_1_7__emit
  ensures 1 == |loc__loc__requires_0_1_6__emit|
  ensures (forall i : nat | 0 <= i < 1 :: 2 == loc__loc__requires_0_1_6__emit[i])
  ensures 1 == |q_seq'nat'_8__emit|
  ensures (forall i : nat | 0 <= i < 1 :: q_seq'nat'_8__emit[i] == 0)
{
  var q_seq'nat'_3__emit : seq<nat> := q_seq'nat'_2__emit;
  var loc__loc__requires_0_1_4__emit : nat := loc__loc__requires_0_1_1__emit;
  var loc__loc__requires_0_1_5__emit : seq<nat> := loc__loc__requires_0_1_0__emit;
  // Forward Declaration
  reveal Map();
  reveal Pow2();
  
  // Method Definition
  assert 4 == loc__loc__requires_0_1_4__emit;
  assert 1 == |loc__loc__requires_0_1_5__emit|;
  assert (forall i : nat | 0 <= i < 1 :: 1 == loc__loc__requires_0_1_5__emit[i]);
  assert 1 == |q_seq'nat'_3__emit|;
  assert (forall i : nat | 0 <= i < 1 :: q_seq'nat'_3__emit[i] == 0);
  q_seq'nat'_3__emit := Map(x => x, q_seq'nat'_3__emit);
  q_seq'nat'_8__emit := q_seq'nat'_3__emit;
  loc__loc__requires_0_1_6__emit := loc__loc__requires_0_1_5__emit;
  loc__loc__requires_0_1_7__emit := loc__loc__requires_0_1_4__emit;
}

}