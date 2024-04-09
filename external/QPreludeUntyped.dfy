// TODO: study what the `LittleEndianNatConversions` is
// include "libraries/src/Collections/Sequences/LittleEndianNatConversions.dfy"
include "libraries/src/Collections/Sequences/LittleEndianNat.dfy"
include "libraries/src/Collections/Sequences/Seq.dfy"
include "libraries/src/NonlinearArithmetic/Power2.dfy"

abstract module {:options "-functionSyntax:4"} QPreludeUntyped {
  import opened LittleEndianNat
  import opened Power2
  import opened Seq

  // cast the ket reprs of a nor basis into 
  function CastNorHad(kets : seq<nat>) : (pb : (seq<nat>, nat)) 
    requires forall k : nat | k < |kets| :: kets[k] == 0 || kets[k] == 1
    ensures pb.1 == 2 
    ensures |pb.0| == |kets|
    ensures  forall i : nat | i < |pb.0| ::
      ((kets[i] == 0) ==> (pb.0[i] == 0)) &&
      ((kets[i] == 1) ==> (pb.0[i] == 1))

  // Cast functions

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
      var p'' := CastHadEn_Phase_(p[1..]);
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
