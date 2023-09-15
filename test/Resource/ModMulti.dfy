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

method Shor (base : nat, q_seq'nat'_0__emit : seq<nat>, p_seq'nat'_1__emit : seq<nat>, q_seq'nat'_2__emit : seq<nat>)
  requires base >= 3
  requires 2 == |q_seq'nat'_0__emit|
  requires (forall k : nat | 0 <= k < 2 :: q_seq'nat'_0__emit[k] == k)
  requires 2 == |p_seq'nat'_1__emit|
  requires (forall k : nat | 0 <= k < 2 :: p_seq'nat'_1__emit[k] == (Pow(base, k)) % (10))
  requires 9 == |q_seq'nat'_2__emit|
  requires (forall i : nat | 0 <= i < 9 :: q_seq'nat'_2__emit[i] == 1)
{
  var p_seq'nat'_3__emit : seq<nat> := p_seq'nat'_1__emit;
  var q_seq'nat'_4__emit : seq<nat> := q_seq'nat'_0__emit;
  var q_seq'nat'_5__emit : seq<nat> := q_seq'nat'_2__emit;
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
  for i := 1 to 10
    invariant Pow2(i) == |q_seq'nat'_6__emit|
    invariant (forall k : nat | 0 <= k < Pow2(i) :: q_seq'nat'_6__emit[k] == k)
    invariant Pow2(i) == |p_seq'nat'_7__emit|
    invariant (forall k : nat | 0 <= k < Pow2(i) :: p_seq'nat'_7__emit[k] == (Pow(base, k)) % (10))
    invariant 10 - i == |q_seq'nat'_8__emit|
    invariant (forall k : nat | 0 <= k < 10 - i :: q_seq'nat'_8__emit[k] == 1)
  {
    q_seq'nat'_9__emit := q_seq'nat'_8__emit[0..1];
    // I have no idea why this assertion about equality is necessary....
    assert q_seq'nat'_8__emit[0..1] == q_seq'nat'_9__emit[0..1];
    q_seq'nat'_10__emit := q_seq'nat'_8__emit[1..10 - i];
    // I have no idea why this assertion about equality is necessary....
    assert q_seq'nat'_8__emit[1..10 - i] == q_seq'nat'_10__emit[0..9 - i];
    // Duplicate
    q_seq'nat'_11__emit := q_seq'nat'_6__emit;
    p_seq'nat'_12__emit := p_seq'nat'_7__emit;
    {
      p_seq'nat'_7__emit := Map(x => (Pow(base, Pow2(i)) * x) % (10), p_seq'nat'_7__emit);
      LemmaPowEquiv(p_seq'nat'_7__emit, base, i, 10);
    }

    p_seq'nat'_7__emit := p_seq'nat'_12__emit + p_seq'nat'_7__emit;
    q_seq'nat'_6__emit := q_seq'nat'_6__emit + Map(x__lambda => x__lambda + Pow2(i), q_seq'nat'_6__emit);
    q_seq'nat'_8__emit := q_seq'nat'_10__emit;
  }

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