// TODO: study what the `LittleEndianNatConversions` is
// TODO: Prove the prelude in Coq
// include "libraries/src/Collections/Sequences/LittleEndianNatConversions.dfy"
include "libraries/src/Collections/Sequences/LittleEndianNat.dfy"
include "libraries/src/Collections/Sequences/Seq.dfy"
include "libraries/src/NonlinearArithmetic/Power2.dfy"

abstract module {:options "-functionSyntax:4"} QPreludeUntyped {
  import opened LittleEndianNat
  import opened Power2
  import opened Seq

  // Cast functions
  /* Cast ketful Nor into phaseful Had
   */
  function CastNorHad_Phase_1st(kets : seq<nat>) : (pb : seq<nat>) 
    requires forall k : nat | k < |kets| :: kets[k] == 0 || kets[k] == 1
    ensures |pb| == |kets|
    ensures  forall i : nat | i < |pb| ::
      ((kets[i] == 0) ==> (pb[i] == 0)) &&
      ((kets[i] == 1) ==> (pb[i] == 1))

  function {:opaque} CastNorEN_Ket(q : seq<nat>) : (c : seq<nat>)
    requires forall k : nat | k < |q| :: q[k] == 0 || q[k] == 1
    ensures (forall k : nat | k < |q| :: q[k] == 0) ==> c == [0]
    ensures c == [LittleEndianNat.ToNatRight(q)]
  {
    if q == SeqZero(|q|)
      then [LittleEndianNat.ToNatRight(q)]
      else [LittleEndianNat.ToNatRight(q)]
  }


  /* Cast a Had basis-ket to En by its cardinality only
   */
  function CastHadEn_Ket(card : nat) : (k : seq<nat>)
    ensures k == seq(card, i requires 0 <= i < card => Pow2(i))

  /* Cast an arbitrary 1st degree Had phase to an En phase
   */
  function CastHadEn_Phase_1st_(p : seq<nat>) : (p' : seq<nat>)
    decreases |p|
  {
    if |p| == 0 then
      []
    else
      var p'' := CastHadEn_Phase_1st_(p[1..]);
      var now := p[0];
      p'' + seq(|p''|, i requires 0 <= i < |p''| => now + p''[i])
  }
    
  /* Cast an arbitrary 1st degree Had phase to an En phase.
   * Optimize the case where Had phase is all zero. 
   */
  function CastHadEn_Phase_1st(p : seq<nat>, b: nat) : (p' : seq<nat>)
    ensures if (b == 2 && forall i : nat | i < |p| :: p[i] == 0)
            then p' == seq(Pow2(|p|), _ => 0)
            else p' == CastHadEn_Phase_1st_(p)

  /* Cast by lifting the ket sequence into a sequence of a sequence 
   */
  function CastNorEn01_Ket(q : seq<nat>) : (c : seq<seq<nat>>)
    requires forall k : nat | k < |q| :: q[k] == 0 || q[k] == 1
    ensures c == [q]


  /* Cast a Had basis-ket to En01 by its cardinality only
   *
   * (|0⟩ + α|1⟩) ⊗ (|0⟩ + α|1⟩) ⊗ (|0⟩ + β|1⟩)
   * |0, 0, 0⟩ + α|1, 0, 0⟩ + ...
   *
   */
  function CastHadEn01_Ket(card : nat) : (c : seq<seq<nat>>)
    ensures |c| == Pow2(card) && forall i : nat | i < |c| :: |c[i]| == card
    ensures
      forall i : nat | i < Pow2(card) :: 
      forall j : nat | j < card :: Locate(i, j) == c[i][j]

  function Locate(i : nat, j : nat) : nat
  {
    if i % Pow2(j + 1) < Pow2(j) then 0 else 1
  }

  /* If the cardinality is one, this is immediately [[0], [1]]
   */
  function CastHadEn01_Ket1() : (c : seq<seq<nat>>)
    ensures c == [[0], [1]]


}
