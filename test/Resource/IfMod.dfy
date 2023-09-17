include "../../external//QPreludeUntyped.dfy"
include "../../external//libraries/src/Collections/Sequences/Seq.dfy"
include "../../external//libraries/src/NonlinearArithmetic/Power2.dfy"
include "../../external//libraries/src/NonlinearArithmetic/Power.dfy"

// target Dafny version: 3.12.0
abstract module QafnyDefault {
import opened QPreludeUntyped
import opened Seq
import opened Power2
import opened Power
import opened DivMod

method Shor (base : nat, q_seq'nat'_0__emit : seq<nat>, p_seq'nat'_1__emit : seq<nat>) returns (q_seq'nat'_8__emit : seq<nat>, p_seq'nat'_9__emit : seq<nat>, q_seq'nat'_10__emit : seq<nat>)
  requires 10 == |q_seq'nat'_0__emit|
  requires (forall i : nat | 0 <= i < 10 :: q_seq'nat'_0__emit[i] == 1)
  requires 1 == |p_seq'nat'_1__emit|
  requires (forall i : nat | 0 <= i < 1 :: p_seq'nat'_1__emit[i] == 1)
  ensures 2 == |q_seq'nat'_8__emit|
  ensures (forall k : nat | 0 <= k < 2 :: q_seq'nat'_8__emit[k] == k)
  ensures 2 == |p_seq'nat'_9__emit|
  ensures (forall k : nat | 0 <= k < 2 :: p_seq'nat'_9__emit[k] == (Pow(base, k)) % (10))
  ensures 9 == |q_seq'nat'_10__emit|
  ensures (forall i : nat | 0 <= i < 9 :: q_seq'nat'_10__emit[i] == 1)
{
  var p_seq'nat'_2__emit : seq<nat> := p_seq'nat'_1__emit;
  var q_seq'nat'_3__emit : seq<nat> := q_seq'nat'_0__emit;
  // Forward Declaration
  var q_seq'nat'_7__emit : seq<nat>;
  var p_seq'nat'_6__emit : seq<nat>;
  var q_seq'nat'_5__emit : seq<nat>;
  var q_seq'nat'_4__emit : seq<nat>;
  reveal Map();
  reveal Pow2();
  
  // Method Definition
  q_seq'nat'_4__emit := q_seq'nat'_3__emit[0..1];
  // I have no idea why this assertion about equality is necessary....
  assert q_seq'nat'_3__emit[0..1] == q_seq'nat'_4__emit[0..1];
  q_seq'nat'_5__emit := q_seq'nat'_3__emit[1..10];
  // I have no idea why this assertion about equality is necessary....
  assert q_seq'nat'_3__emit[1..10] == q_seq'nat'_5__emit[0..9];
  // Duplicate
  p_seq'nat'_6__emit := p_seq'nat'_2__emit;
  {
    p_seq'nat'_2__emit := Map(x => (Pow(base, 1) * x) % (10), p_seq'nat'_2__emit);
  }

  var card_3 : nat := |p_seq'nat'_2__emit|;
  var card_4 : nat := |p_seq'nat'_6__emit|;
  p_seq'nat'_2__emit := p_seq'nat'_6__emit + p_seq'nat'_2__emit;
  // Merge: Body partition + the Guard partition.
  q_seq'nat'_7__emit := seq<nat>(card_4, _ => 0) + seq<nat>(card_3, _ => 1);
  assert 2 == |q_seq'nat'_7__emit|;
  assert (forall k : nat | 0 <= k < 2 :: q_seq'nat'_7__emit[k] == k);
  assert 2 == |p_seq'nat'_2__emit|;
  assert (forall k : nat | 0 <= k < 2 :: p_seq'nat'_2__emit[k] == (Pow(base, k)) % (10));
  q_seq'nat'_8__emit := q_seq'nat'_7__emit;
  p_seq'nat'_9__emit := p_seq'nat'_2__emit;
  q_seq'nat'_10__emit := q_seq'nat'_5__emit;
}

}