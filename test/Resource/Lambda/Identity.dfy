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

method ApplyIdentity (N : nat, q_seq'nat'_0__emit : seq<nat>) returns (q_seq'nat'_3__emit : seq<nat>)
  requires N >= 2
  requires 1 == |q_seq'nat'_0__emit|
  requires (forall i : nat | 0 <= i < 1 :: q_seq'nat'_0__emit[i] == 0)
  ensures 1 == |q_seq'nat'_3__emit|
  ensures (forall i : nat | 0 <= i < 1 :: q_seq'nat'_3__emit[i] == 0)
{
  var q_seq'nat'_1__emit : seq<nat> := q_seq'nat'_0__emit;
  // Forward Declaration
  var q_seq'nat'_2__emit : seq<nat>;
  reveal Map();
  reveal Pow2();
  
  // Method Definition
  // Cast TNor ==> TEN
  q_seq'nat'_2__emit := CastNorEN(q_seq'nat'_1__emit);
  q_seq'nat'_2__emit := Map(x => x, q_seq'nat'_2__emit);
  q_seq'nat'_3__emit := q_seq'nat'_2__emit;
}

}