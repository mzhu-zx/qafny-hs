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

method GHZ (n : nat, q_seq'nat'_0__emit : seq<nat>) returns (q_seq'seq'nat''_15__emit : seq<seq<nat>>)
  requires n >= 2
  requires n == |q_seq'nat'_0__emit|
  requires (forall i : nat | 0 <= i < n :: q_seq'nat'_0__emit[i] == 0)
  ensures 2 == |q_seq'seq'nat''_15__emit|
  ensures (forall j : nat | 0 <= j < 2 :: (forall k : nat | 0 <= k < n :: n == |q_seq'seq'nat''_15__emit[j]|))
  ensures (forall j : nat | 0 <= j < 2 :: (forall k : nat | 0 <= k < n :: q_seq'seq'nat''_15__emit[j][k] == j))
{
  var q_seq'nat'_1__emit : seq<nat> := q_seq'nat'_0__emit;
  // Forward Declaration
  var q_seq'seq'nat''_14__emit : seq<seq<nat>>;
  var q_seq'nat'_13__emit : seq<nat>;
  var q_seq'nat'_12__emit : seq<nat>;
  var q_seq'seq'nat''_11__emit : seq<seq<nat>>;
  var q_seq'nat'_10__emit : seq<nat>;
  var q_seq'nat'_9__emit : seq<nat>;
  var q_seq'seq'nat''_8__emit : seq<seq<nat>>;
  var q_seq'nat'_7__emit : seq<nat>;
  var q_seq'seq'nat''_6__emit : seq<seq<nat>>;
  var q_seq'seq'nat''_5__emit : seq<seq<nat>>;
  var q_seq'nat'_4__emit : seq<nat>;
  var q_seq'nat'_3__emit : seq<nat>;
  var q_seq'nat'_2__emit : seq<nat>;
  reveal Map();
  reveal Pow2();
  
  // Method Definition
  q_seq'nat'_2__emit := q_seq'nat'_1__emit[0..1];
  // I have no idea why this assertion about equality is necessary....
  assert q_seq'nat'_1__emit[0..1] == q_seq'nat'_2__emit[0..1];
  q_seq'nat'_3__emit := q_seq'nat'_1__emit[1..n];
  // I have no idea why this assertion about equality is necessary....
  assert q_seq'nat'_1__emit[1..n] == q_seq'nat'_3__emit[0..-1 + n];
  // Cast (TNor,[0]) ==> THad
  q_seq'nat'_4__emit := CastNorHad(q_seq'nat'_2__emit);
  // Cast THad ==> TEN01
  q_seq'seq'nat''_5__emit := CastHadEN01'1(q_seq'nat'_4__emit);
  q_seq'seq'nat''_6__emit := q_seq'seq'nat''_5__emit;
  q_seq'nat'_7__emit := q_seq'nat'_3__emit;
  for i := 0 to n - 1
    invariant 2 == |q_seq'seq'nat''_6__emit|
    invariant (forall j : nat | 0 <= j < 2 :: (forall k : nat | 0 <= k < 1 + i :: 1 + i == |q_seq'seq'nat''_6__emit[j]|))
    invariant (forall j : nat | 0 <= j < 2 :: (forall k : nat | 0 <= k < 1 + i :: q_seq'seq'nat''_6__emit[j][k] == j))
    invariant -1 + n - i == |q_seq'nat'_7__emit|
    invariant (forall k : nat | 0 <= k < -1 + n - i :: q_seq'nat'_7__emit[k] == 0)
  {
    q_seq'seq'nat''_8__emit := q_seq'seq'nat''_6__emit[0..1];
    q_seq'seq'nat''_6__emit := q_seq'seq'nat''_6__emit[1..|q_seq'seq'nat''_6__emit|];
    // begin false
    q_seq'nat'_9__emit := q_seq'nat'_7__emit[0..1];
    // I have no idea why this assertion about equality is necessary....
    assert q_seq'nat'_7__emit[0..1] == q_seq'nat'_9__emit[0..1];
    q_seq'nat'_10__emit := q_seq'nat'_7__emit[1..-1 + n - i];
    // I have no idea why this assertion about equality is necessary....
    assert q_seq'nat'_7__emit[1..-1 + n - i] == q_seq'nat'_10__emit[0..-2 + n - i];
    q_seq'seq'nat''_11__emit := Map(lambda_x_5 => lambda_x_5 + q_seq'nat'_9__emit, q_seq'seq'nat''_8__emit);
    // end false
    // begin true
    q_seq'nat'_12__emit := q_seq'nat'_7__emit[0..1];
    // I have no idea why this assertion about equality is necessary....
    assert q_seq'nat'_7__emit[0..1] == q_seq'nat'_12__emit[0..1];
    q_seq'nat'_13__emit := q_seq'nat'_7__emit[1..-1 + n - i];
    // I have no idea why this assertion about equality is necessary....
    assert q_seq'nat'_7__emit[1..-1 + n - i] == q_seq'nat'_13__emit[0..-2 + n - i];
    q_seq'nat'_12__emit := q_seq'nat'_12__emit[0..0] + Map(x => (x + 1) % (2), q_seq'nat'_12__emit[0..1]) + q_seq'nat'_12__emit[1..|q_seq'nat'_12__emit|];
    q_seq'seq'nat''_14__emit := Map(lambda_x_7 => lambda_x_7 + q_seq'nat'_12__emit, q_seq'seq'nat''_6__emit);
    // end true
    // begin true-false
    q_seq'seq'nat''_11__emit := q_seq'seq'nat''_11__emit + q_seq'seq'nat''_14__emit;
    // end true-false
    // Match Begin-End
    q_seq'seq'nat''_6__emit := q_seq'seq'nat''_11__emit;
    q_seq'nat'_7__emit := q_seq'nat'_10__emit;
  }

  q_seq'seq'nat''_15__emit := q_seq'seq'nat''_6__emit;
}

}