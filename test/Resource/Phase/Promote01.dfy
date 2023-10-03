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

method PromoteZeroPhaseIdentity (N : nat, q_seq'nat'_0__emit : seq<nat>) returns (q_seq'nat'_7__emit : seq<nat>, loc__loc__requires_0_1_5__emit : seq<nat>, loc__loc__requires_0_1_6__emit : nat)
  requires N >= 2
  requires 1 == |q_seq'nat'_0__emit|
  requires (forall i : nat | 0 <= i < 1 :: q_seq'nat'_0__emit[i] == 0)
  ensures 4 == loc__loc__requires_0_1_6__emit
  ensures 1 == |loc__loc__requires_0_1_5__emit|
  ensures (forall i : nat | 0 <= i < 1 :: 1 == loc__loc__requires_0_1_5__emit[i])
  ensures 1 == |q_seq'nat'_7__emit|
  ensures (forall i : nat | 0 <= i < 1 :: q_seq'nat'_7__emit[i] == 0)
{
  var q_seq'nat'_1__emit : seq<nat> := q_seq'nat'_0__emit;
  // Forward Declaration
  var loc__loc__requires_0_1_4__emit : nat;
  var loc__loc__requires_0_1_3__emit : seq<nat>;
  var q_seq'nat'_2__emit : seq<nat>;
  reveal Map();
  reveal Pow2();
  
  // Method Definition
  // Cast TNor ==> TEN
  q_seq'nat'_2__emit := CastNorEN(q_seq'nat'_1__emit);
  loc__loc__requires_0_1_3__emit := seq<nat>(|q_seq'nat'_2__emit|, _ => 1);
  loc__loc__requires_0_1_4__emit := 4;
  q_seq'nat'_2__emit := Map(x => x, q_seq'nat'_2__emit);
  q_seq'nat'_7__emit := q_seq'nat'_2__emit;
  loc__loc__requires_0_1_5__emit := loc__loc__requires_0_1_3__emit;
  loc__loc__requires_0_1_6__emit := loc__loc__requires_0_1_4__emit;
}

}