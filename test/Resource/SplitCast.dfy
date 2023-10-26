include "../../external//QPreludeUntyped.dfy"
include "../../external//libraries/src/Collections/Sequences/Seq.dfy"
include "../../external//libraries/src/NonlinearArithmetic/Power2.dfy"
include "../../external//libraries/src/NonlinearArithmetic/Power.dfy"

// target Dafny version: 4.2.0
abstract module QafnyDefault {
import opened QPreludeUntyped
import opened Seq
import opened Power2
import opened Power
import opened DivMod

method Test (q_seq'nat'_0__emit : seq<nat>) returns (q_seq'nat'_5__emit : seq<nat>)
  requires 10 == |q_seq'nat'_0__emit|
  requires (forall i : nat | 0 <= i < 10 :: q_seq'nat'_0__emit[i] == 0)
  ensures 1 == |q_seq'nat'_5__emit|
  ensures (forall i : nat | 0 <= i < 1 :: q_seq'nat'_5__emit[i] == 1)
{
  var q_seq'nat'_1__emit : seq<nat> := q_seq'nat'_0__emit;
  // Forward Declaration
  var q_seq'nat'_4__emit : seq<nat>;
  var q_seq'nat'_3__emit : seq<nat>;
  var q_seq'nat'_2__emit : seq<nat>;
  reveal Map();
  reveal Pow2();
  
  // Method Definition
  q_seq'nat'_2__emit := q_seq'nat'_1__emit[0..5];
  // I have no idea why this assertion about equality is necessary....
  assert q_seq'nat'_1__emit[0..5] == q_seq'nat'_2__emit[0..5];
  q_seq'nat'_3__emit := q_seq'nat'_1__emit[5..10];
  // I have no idea why this assertion about equality is necessary....
  assert q_seq'nat'_1__emit[5..10] == q_seq'nat'_3__emit[0..5];
  // Cast TNor ==> TEN
  q_seq'nat'_4__emit := CastNorEN(q_seq'nat'_2__emit);
  q_seq'nat'_4__emit := Map(x => x + 1, q_seq'nat'_4__emit);
  q_seq'nat'_5__emit := q_seq'nat'_4__emit;
}

}