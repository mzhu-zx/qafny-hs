// include "libraries/src/NonlinearArithmetic/Power2.dfy"
// TODO: study what the `LittleEndianNatConversions` is
// include "libraries/src/Collections/Sequences/LittleEndianNatConversions.dfy"
include "libraries/src/Collections/Sequences/LittleEndianNat.dfy"
include "libraries/src/Collections/Sequences/Seq.dfy"

abstract module {:options "-functionSyntax:4"} QPreludeUntyped {
  import opened LittleEndianNat
  // import opened Seq
  import opened Seq

  // import opened Seq
  // cast nor type qubit to had type qubit
  function CastNorHad(q : seq<nat>) : (h : seq<int>) 
    requires forall k : nat | k < |q| :: q[k] == 0 || q[k] == 1
    ensures |h| == |q| && forall k : nat | k < |q| ::
    (q[k] == 0 ==> h[k] == 1) && (q[k] == 1 ==> h[k] == 0)
  ;

  function CastNorCH(q : seq<nat>) : (c : seq<nat>)
    requires forall k : nat | k < |q| :: q[k] == 0 || q[k] == 1
    ensures c == [LittleEndianNat.ToNatRight(q)]
  ;

  function CastNorCH01(q : seq<nat>) : (c : seq<seq<nat>>)
    requires forall k : nat | k < |q| :: q[k] == 0 || q[k] == 1
    ensures c == [q]
  ;
}
