include "../../external//QPreludeUntyped.dfy"
include "../../external//libraries/src/Collections/Sequences/Seq.dfy"
include "../../external//libraries/src/NonlinearArithmetic/Power2.dfy"

// target Dafny version: 3.12.0
abstract module QafnyDefault {
import opened QPreludeUntyped
import opened Seq
import opened Power2

method GHZ (q_seq'nat'_0__emit : seq<nat>) returns (q_seq'seq'nat''_7__emit : seq<seq<nat>>, q_seq'nat'_8__emit : seq<nat>, q_seq'nat'_9__emit : seq<nat>)
  requires (15 == |q_seq'nat'_0__emit|) && ((forall i : nat | 0 <= i < 15 :: q_seq'nat'_0__emit[i] == 0))
  ensures ((2 == |q_seq'seq'nat''_7__emit|) && ((forall j : nat | 0 <= j < 2 :: (forall k : nat | 0 <= k < 10 :: 10 == |q_seq'seq'nat''_7__emit[j]|)))) && ((forall j : nat | 0 <= j < 2 :: (forall k : nat | 0 <= k < 10 :: q_seq'seq'nat''_7__emit[j][k] == j)))
  ensures (5 == |q_seq'nat'_9__emit|) && ((forall i : nat | 0 <= i < 5 :: q_seq'nat'_9__emit[i] == 0))
{
  // Forward Declaration
  var q_seq'seq'nat''_16__emit : seq<seq<nat>>;
  var q_seq'nat'_15__emit : seq<nat>;
  var q_seq'nat'_14__emit : seq<nat>;
  var q_seq'seq'nat''_13__emit : seq<seq<nat>>;
  var q_seq'nat'_12__emit : seq<nat>;
  var q_seq'nat'_11__emit : seq<nat>;
  var q_seq'seq'nat''_10__emit : seq<seq<nat>>;
  var q_seq'nat'_6__emit : seq<nat>;
  var q_seq'nat'_5__emit : seq<nat>;
  var q_seq'seq'nat''_4__emit : seq<seq<nat>>;
  var q_seq'nat'_3__emit : seq<nat>;
  var q_seq'nat'_2__emit : seq<nat>;
  var q_seq'nat'_1__emit : seq<nat>;
  reveal Map();
  
  // Method Definition
  q_seq'nat'_1__emit := q_seq'nat'_0__emit[0..1];
  // I have no idea why this assertion about equality is necessary....
  assert q_seq'nat'_0__emit[0..1] == q_seq'nat'_1__emit[0..1];
  q_seq'nat'_2__emit := q_seq'nat'_0__emit[1..15];
  // I have no idea why this assertion about equality is necessary....
  assert q_seq'nat'_0__emit[1..15] == q_seq'nat'_2__emit[0..14];
  // Cast TNor ==> THad
  q_seq'nat'_3__emit := CastNorHad(q_seq'nat'_1__emit);
  assert 1 == |q_seq'nat'_3__emit|;
  assert (forall i : nat | 0 <= i < 1 :: q_seq'nat'_3__emit[i] == 1);
  // Cast THad ==> TEN01
  q_seq'seq'nat''_4__emit := CastHadEN01'1(q_seq'nat'_3__emit);
  q_seq'nat'_5__emit := q_seq'nat'_2__emit[0..9];
  // I have no idea why this assertion about equality is necessary....
  assert q_seq'nat'_2__emit[0..9] == q_seq'nat'_5__emit[0..9];
  q_seq'nat'_6__emit := q_seq'nat'_2__emit[9..14];
  // I have no idea why this assertion about equality is necessary....
  assert q_seq'nat'_2__emit[9..14] == q_seq'nat'_6__emit[0..5];
  q_seq'seq'nat''_7__emit := q_seq'seq'nat''_4__emit;
  q_seq'nat'_8__emit := q_seq'nat'_5__emit;
  q_seq'nat'_9__emit := q_seq'nat'_6__emit;
  for i := 0 to 9
    invariant 2 == |q_seq'seq'nat''_7__emit|
    invariant (forall j : nat | 0 <= j < 2 :: (forall k : nat | 0 <= k < 1 + i :: 1 + i == |q_seq'seq'nat''_7__emit[j]|))
    invariant (forall j : nat | 0 <= j < 2 :: (forall k : nat | 0 <= k < 1 + i :: q_seq'seq'nat''_7__emit[j][k] == j))
    invariant 9 - i == |q_seq'nat'_8__emit|
    invariant (forall k : nat | 0 <= k < 9 - i :: q_seq'nat'_8__emit[k] == 0)
    invariant 5 == |q_seq'nat'_9__emit|
    invariant (forall i : nat | 0 <= i < 5 :: q_seq'nat'_9__emit[i] == 0)
  {
    q_seq'seq'nat''_10__emit := q_seq'seq'nat''_7__emit[0..1];
    q_seq'seq'nat''_7__emit := q_seq'seq'nat''_7__emit[1..|q_seq'seq'nat''_7__emit|];
    // begin false
    q_seq'nat'_11__emit := q_seq'nat'_8__emit[0..1];
    // I have no idea why this assertion about equality is necessary....
    assert q_seq'nat'_8__emit[0..1] == q_seq'nat'_11__emit[0..1];
    q_seq'nat'_12__emit := q_seq'nat'_8__emit[1..9 - i];
    // I have no idea why this assertion about equality is necessary....
    assert q_seq'nat'_8__emit[1..9 - i] == q_seq'nat'_12__emit[0..8 - i];
    q_seq'seq'nat''_13__emit := Map(lambda_x_7 => lambda_x_7 + q_seq'nat'_11__emit, q_seq'seq'nat''_10__emit);
    // end false
    // begin true
    q_seq'nat'_14__emit := q_seq'nat'_8__emit[0..1];
    // I have no idea why this assertion about equality is necessary....
    assert q_seq'nat'_8__emit[0..1] == q_seq'nat'_14__emit[0..1];
    q_seq'nat'_15__emit := q_seq'nat'_8__emit[1..9 - i];
    // I have no idea why this assertion about equality is necessary....
    assert q_seq'nat'_8__emit[1..9 - i] == q_seq'nat'_15__emit[0..8 - i];
    q_seq'nat'_14__emit := q_seq'nat'_14__emit[0..0] + Map(x => x + 1 % 2, q_seq'nat'_14__emit[0..1]) + q_seq'nat'_14__emit[1..|q_seq'nat'_14__emit|];
    q_seq'seq'nat''_16__emit := Map(lambda_x_9 => lambda_x_9 + q_seq'nat'_14__emit, q_seq'seq'nat''_7__emit);
    // end true
    // begin true-false
    q_seq'seq'nat''_13__emit := q_seq'seq'nat''_13__emit + q_seq'seq'nat''_16__emit;
    // end true-false
    // Match Begin-End
    q_seq'seq'nat''_7__emit := q_seq'seq'nat''_13__emit;
    q_seq'nat'_9__emit := q_seq'nat'_9__emit;
    q_seq'nat'_8__emit := q_seq'nat'_12__emit;
  }

}

}