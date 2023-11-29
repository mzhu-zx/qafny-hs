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

method MultiModFull (N : nat, base : nat, q_seq'nat'_0__emit : seq<nat>, p_seq'nat'_1__emit : seq<nat>) returns (q_seq'nat'_10__emit : seq<nat>, p_seq'nat'_11__emit : seq<nat>)
  requires N >= 3
  requires base >= 3
  requires N == |q_seq'nat'_0__emit|
  requires (forall i : nat | 0 <= i < N :: q_seq'nat'_0__emit[i] == 1)
  requires 1 == |p_seq'nat'_1__emit|
  requires (forall i : nat | 0 <= i < 1 :: p_seq'nat'_1__emit[i] == 1)
  ensures Pow2(N) == |q_seq'nat'_10__emit|
  ensures (forall k : nat | 0 <= k < Pow2(N) :: q_seq'nat'_10__emit[k] == k)
  ensures Pow2(N) == |p_seq'nat'_11__emit|
  ensures (forall k : nat | 0 <= k < Pow2(N) :: p_seq'nat'_11__emit[k] == (Pow(base, k)) % (N))
{
  var p_seq'nat'_2__emit : seq<nat> := p_seq'nat'_1__emit;
  var q_seq'nat'_3__emit : seq<nat> := q_seq'nat'_0__emit;
  // Forward Declaration
  var p_seq'nat'_9__emit : seq<nat>;
  var q_seq'nat'_8__emit : seq<nat>;
  var p_seq'nat'_7__emit : seq<nat>;
  var q_seq'nat'_6__emit : seq<nat>;
  var q_seq'nat'_5__emit : seq<nat>;
  var q_seq'nat'_4__emit : seq<nat>;
  reveal Map();
  reveal Pow2();
  
  // Method Definition
  q_seq'nat'_4__emit := q_seq'nat'_3__emit[0..1];
  // I have no idea why this assertion about equality is necessary....
  assert q_seq'nat'_3__emit[0..1] == q_seq'nat'_4__emit[0..1];
  q_seq'nat'_5__emit := q_seq'nat'_3__emit[1..N];
  // I have no idea why this assertion about equality is necessary....
  assert q_seq'nat'_3__emit[1..N] == q_seq'nat'_5__emit[0..-1 + N];
  q_seq'nat'_6__emit, p_seq'nat'_7__emit := EntangleOne1(N, base, q_seq'nat'_4__emit, p_seq'nat'_2__emit);
  q_seq'nat'_8__emit, p_seq'nat'_9__emit := MultiMod(N, base, q_seq'nat'_5__emit, q_seq'nat'_6__emit, p_seq'nat'_7__emit);
  q_seq'nat'_10__emit := q_seq'nat'_8__emit;
  p_seq'nat'_11__emit := p_seq'nat'_9__emit;
}

method EntangleOne1 (N : nat, base : nat, q_seq'nat'_0__emit : seq<nat>, p_seq'nat'_1__emit : seq<nat>) returns (q_seq'nat'_6__emit : seq<nat>, p_seq'nat'_7__emit : seq<nat>)
  requires N >= 3
  requires 1 == |q_seq'nat'_0__emit|
  requires (forall i : nat | 0 <= i < 1 :: q_seq'nat'_0__emit[i] == 1)
  requires 1 == |p_seq'nat'_1__emit|
  requires (forall i : nat | 0 <= i < 1 :: p_seq'nat'_1__emit[i] == 1)
  ensures 2 == |q_seq'nat'_6__emit|
  ensures (forall k : nat | 0 <= k < 2 :: q_seq'nat'_6__emit[k] == k)
  ensures 2 == |p_seq'nat'_7__emit|
  ensures (forall k : nat | 0 <= k < 2 :: p_seq'nat'_7__emit[k] == (Pow(base, k)) % (N))
{
  var p_seq'nat'_2__emit : seq<nat> := p_seq'nat'_1__emit;
  var q_seq'nat'_3__emit : seq<nat> := q_seq'nat'_0__emit;
  // Forward Declaration
  var q_seq'nat'_5__emit : seq<nat>;
  var p_seq'nat'_4__emit : seq<nat>;
  reveal Map();
  reveal Pow2();
  
  // Method Definition
  // Duplicate
  p_seq'nat'_4__emit := p_seq'nat'_2__emit;
  {
    p_seq'nat'_2__emit := Map(x => (Pow(base, 1) * x) % (N), p_seq'nat'_2__emit);
  }

  var card_2 : nat := |p_seq'nat'_2__emit|;
  var card_3 : nat := |p_seq'nat'_4__emit|;
  p_seq'nat'_2__emit := p_seq'nat'_4__emit + p_seq'nat'_2__emit;
  // Merge: Body partition + the Guard partition.
  q_seq'nat'_5__emit := seq<nat>(card_3, _ => 0) + seq<nat>(card_2, _ => 1);
  q_seq'nat'_6__emit := q_seq'nat'_5__emit;
  p_seq'nat'_7__emit := p_seq'nat'_2__emit;
}

method MultiMod (N : nat, base : nat, q_seq'nat'_0__emit : seq<nat>, q_seq'nat'_1__emit : seq<nat>, p_seq'nat'_2__emit : seq<nat>) returns (q_seq'nat'_13__emit : seq<nat>, p_seq'nat'_14__emit : seq<nat>)
  requires N >= 3
  requires base >= 3
  requires -1 + N == |q_seq'nat'_0__emit|
  requires (forall i : nat | 0 <= i < -1 + N :: q_seq'nat'_0__emit[i] == 1)
  requires 2 == |q_seq'nat'_1__emit|
  requires (forall k : nat | 0 <= k < 2 :: q_seq'nat'_1__emit[k] == k)
  requires 2 == |p_seq'nat'_2__emit|
  requires (forall k : nat | 0 <= k < 2 :: p_seq'nat'_2__emit[k] == (Pow(base, k)) % (N))
  ensures Pow2(N) == |q_seq'nat'_13__emit|
  ensures (forall k : nat | 0 <= k < Pow2(N) :: q_seq'nat'_13__emit[k] == k)
  ensures Pow2(N) == |p_seq'nat'_14__emit|
  ensures (forall k : nat | 0 <= k < Pow2(N) :: p_seq'nat'_14__emit[k] == (Pow(base, k)) % (N))
{
  var p_seq'nat'_3__emit : seq<nat> := p_seq'nat'_2__emit;
  var q_seq'nat'_4__emit : seq<nat> := q_seq'nat'_1__emit;
  var q_seq'nat'_5__emit : seq<nat> := q_seq'nat'_0__emit;
  // Forward Declaration
  var p_seq'nat'_12__emit : seq<nat>;
  var q_seq'nat'_11__emit : seq<nat>;
  var q_seq'nat'_10__emit : seq<nat>;
  var q_seq'nat'_9__emit : seq<nat>;
  var q_seq'nat'_8__emit : seq<nat>;
  var p_seq'nat'_7__emit : seq<nat>;
  var q_seq'nat'_6__emit : seq<nat>;
  reveal Map();
  reveal Pow2();
  
  // Method Definition
  p_seq'nat'_7__emit := p_seq'nat'_3__emit;
  q_seq'nat'_6__emit := q_seq'nat'_4__emit;
  q_seq'nat'_8__emit := q_seq'nat'_5__emit;
  for i := 1 to N
    invariant Pow2(i) == |q_seq'nat'_6__emit|
    invariant (forall k : nat | 0 <= k < Pow2(i) :: q_seq'nat'_6__emit[k] == k)
    invariant Pow2(i) == |p_seq'nat'_7__emit|
    invariant (forall k : nat | 0 <= k < Pow2(i) :: p_seq'nat'_7__emit[k] == (Pow(base, k)) % (N))
    invariant N - i == |q_seq'nat'_8__emit|
    invariant (forall k : nat | 0 <= k < N - i :: q_seq'nat'_8__emit[k] == 1)
  {
    q_seq'nat'_9__emit := q_seq'nat'_8__emit[0..1];
    // I have no idea why this assertion about equality is necessary....
    assert q_seq'nat'_8__emit[0..1] == q_seq'nat'_9__emit[0..1];
    q_seq'nat'_10__emit := q_seq'nat'_8__emit[1..N - i];
    // I have no idea why this assertion about equality is necessary....
    assert q_seq'nat'_8__emit[1..N - i] == q_seq'nat'_10__emit[0..-1 - i + N];
    // Duplicate
    q_seq'nat'_11__emit := q_seq'nat'_6__emit;
    p_seq'nat'_12__emit := p_seq'nat'_7__emit;
    {
      p_seq'nat'_7__emit := Map(x => (Pow(base, Pow2(i)) * x) % (N), p_seq'nat'_7__emit);
      LemmaPowEquiv(p_seq'nat'_7__emit, base, i, N);
    }

    p_seq'nat'_7__emit := p_seq'nat'_12__emit + p_seq'nat'_7__emit;
    q_seq'nat'_6__emit := q_seq'nat'_6__emit + Map(x__lambda => x__lambda + Pow2(i), q_seq'nat'_6__emit);
    q_seq'nat'_8__emit := q_seq'nat'_10__emit;
  }

  q_seq'nat'_13__emit := q_seq'nat'_6__emit;
  p_seq'nat'_14__emit := p_seq'nat'_7__emit;
}

lemma LemmaPowEquiv(s : seq<nat>, a : nat, i : nat, N : nat)
  requires |s| == Pow2(i) && N >= 2
  requires forall k | 0 <= k < Pow2(i) :: s[k] == ((Pow(a, Pow2(i)) * (Pow(a, k) % N)) % N)
  ensures forall k | 0 <= k < Pow2(i) :: s[k] == (Pow(a, (Pow2(i) + k)) % N)
{ 
  forall k | 0 <= k < Pow2(i) {
    calc == {
      s[k] == ((Pow(a, Pow2(i)) * (Pow(a, k) % N)) % N);
     { LemmaMulModNoopRightAuto(); } // crush double Ns
      s[k] == ((Pow(a, Pow2(i)) * Pow(a, k)) % N);
     { LemmaPowAdds(a, Pow2(i), k); } // crush the add on Power
     s[k] == (Pow(a, (Pow2(i) + k)) % N);
    }
  }
} 
}