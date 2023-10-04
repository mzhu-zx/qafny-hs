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

method For0 (n : nat)
  requires n >= 2
{
  // Forward Declaration
  var p_seq'nat'_14__emit : seq<nat>;
  var q_seq'nat'_13__emit : seq<nat>;
  var q_seq'nat'_12__emit : seq<nat>;
  var q_seq'nat'_11__emit : seq<nat>;
  var p_seq'nat'_10__emit : seq<nat>;
  var q_seq'nat'_9__emit : seq<nat>;
  var q_seq'nat'_8__emit : seq<nat>;
  var q_seq'nat'_7__emit : seq<nat>;
  var p_seq'nat'_6__emit : seq<nat>;
  var p_seq'nat'_5__emit : seq<nat>;
  var q_seq'nat'_4__emit : seq<nat>;
  var q_seq'nat'_3__emit : seq<nat>;
  var q_seq'nat'_2__emit : seq<nat>;
  var p_seq'nat'_1__emit : seq<nat>;
  var q_seq'nat'_0__emit : seq<nat>;
  reveal Map();
  reveal Pow2();
  
  // Method Definition
  q_seq'nat'_0__emit := seq<nat>(n, _ => 0);
  p_seq'nat'_1__emit := seq<nat>(n, _ => 0);
  // Cast (TNor,[0]) ==> THad
  q_seq'nat'_2__emit := CastNorHad(q_seq'nat'_0__emit);
  q_seq'nat'_3__emit := q_seq'nat'_2__emit[0..1];
  // I have no idea why this assertion about equality is necessary....
  assert q_seq'nat'_2__emit[0..1] == q_seq'nat'_3__emit[0..1];
  q_seq'nat'_4__emit := q_seq'nat'_2__emit[1..n];
  // I have no idea why this assertion about equality is necessary....
  assert q_seq'nat'_2__emit[1..n] == q_seq'nat'_4__emit[0..-1 + n];
  // Cast Body Partition TNor => TEN
  // Cast (TNor,[0]) ==> TEN
  p_seq'nat'_5__emit := CastNorEN(p_seq'nat'_1__emit);
  // Duplicate
  p_seq'nat'_6__emit := p_seq'nat'_5__emit;
  {
    p_seq'nat'_5__emit := Map(x => x, p_seq'nat'_5__emit);
  }

  var card_3 : nat := |p_seq'nat'_5__emit|;
  var card_4 : nat := |p_seq'nat'_6__emit|;
  p_seq'nat'_5__emit := p_seq'nat'_6__emit + p_seq'nat'_5__emit;
  // Merge: Body partition + the Guard partition.
  q_seq'nat'_7__emit := seq<nat>(card_4, _ => 0) + seq<nat>(card_3, _ => 1);
  p_seq'nat'_10__emit := p_seq'nat'_5__emit;
  q_seq'nat'_9__emit := q_seq'nat'_7__emit;
  q_seq'nat'_8__emit := q_seq'nat'_4__emit;
  for i := 1 to n
    invariant - i + n == |q_seq'nat'_8__emit|
    invariant (forall k : nat | 0 <= k < - i + n :: q_seq'nat'_8__emit[k] == 1)
    invariant Pow2(i) == |q_seq'nat'_9__emit|
    invariant (forall j : nat | 0 <= j < Pow2(i) :: q_seq'nat'_9__emit[j] == j)
    invariant Pow2(i) == |p_seq'nat'_10__emit|
    invariant (forall j : nat | 0 <= j < Pow2(i) :: p_seq'nat'_10__emit[j] == 0)
  {
    q_seq'nat'_11__emit := q_seq'nat'_8__emit[0..1];
    // I have no idea why this assertion about equality is necessary....
    assert q_seq'nat'_8__emit[0..1] == q_seq'nat'_11__emit[0..1];
    q_seq'nat'_12__emit := q_seq'nat'_8__emit[1..- i + n];
    // I have no idea why this assertion about equality is necessary....
    assert q_seq'nat'_8__emit[1..- i + n] == q_seq'nat'_12__emit[0..-1 + n - i];
    // Duplicate
    q_seq'nat'_13__emit := q_seq'nat'_9__emit;
    p_seq'nat'_14__emit := p_seq'nat'_10__emit;
    {
      p_seq'nat'_10__emit := Map(x => x, p_seq'nat'_10__emit);
    }

    p_seq'nat'_10__emit := p_seq'nat'_14__emit + p_seq'nat'_10__emit;
    q_seq'nat'_9__emit := q_seq'nat'_9__emit + Map(x__lambda => x__lambda + Pow2(i), q_seq'nat'_9__emit);
    q_seq'nat'_8__emit := q_seq'nat'_12__emit;
  }

}

}