// TODO: study what the `LittleEndianNatConversions` is
// include "libraries/src/Collections/Sequences/LittleEndianNatConversions.dfy"
include "libraries/src/Collections/Sequences/LittleEndianNat.dfy"
include "libraries/src/Collections/Sequences/Seq.dfy"
include "libraries/src/NonlinearArithmetic/Power2.dfy"

abstract module {:options "-functionSyntax:4"} QPreludeUntyped {
  import opened LittleEndianNat
  import opened Power2
  import opened Seq

  // import opened Seq
  // cast nor type qubit to had type qubit by applying an 'H' gate to it
  function CastNorHad(q : seq<nat>) : (h : seq<int>) 
    requires forall k : nat | k < |q| :: q[k] == 0 || q[k] == 1
    ensures |h| == |q| && forall k : nat | k < |q| ::
    (q[k] == 0 ==> h[k] == 1) && (q[k] == 1 ==> h[k] == (- 1))


  function {:opaque} CastNorEN(q : seq<nat>) : (c : seq<nat>)
    requires forall k : nat | k < |q| :: q[k] == 0 || q[k] == 1
    ensures (forall k : nat | k < |q| :: q[k] == 0) ==> c == [0]
    ensures c == [LittleEndianNat.ToNatRight(q)]
  {
    if q == SeqZero(|q|)
      then [LittleEndianNat.ToNatRight(q)]
      else [LittleEndianNat.ToNatRight(q)]
  }

  function CastNorEN01(q : seq<nat>) : (c : seq<seq<nat>>)
    requires forall k : nat | k < |q| :: q[k] == 0 || q[k] == 1
    ensures c == [q]


  // (|0⟩ + α|1⟩) ⊗ (|0⟩ + α|1⟩) ⊗ (|0⟩ + β|1⟩)
  // |0, 0, 0⟩ + α|1, 0, 0⟩ + ...
  //
  function CastHadEN01(q : seq<int>) : (c : seq<seq<nat>>)
    requires forall k : nat | k < |q| :: q[k] == 1 || q[k] == -1
    ensures |c| == Pow2(|q|) && forall i : nat | i < |c| :: |c[i]| == |q|
    ensures forall i : nat | i < Pow2(|q|) :: 
            forall j : nat | j < |q| :: Locate(i, j) == c[i][j]


  function CastHadEN01'1(q : seq<int>) : (c : seq<seq<nat>>)
    requires |q| == 1
    requires forall k : nat | k < |q| :: q[k] == 1 || q[k] == -1
    ensures c == [[0], [1]]



  function Locate(i : nat, j : nat) : nat
  {
    if i % Pow2(j + 1) < Pow2(j) then 0 else 1
  }

}

