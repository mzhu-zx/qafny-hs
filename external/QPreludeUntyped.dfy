// include "libraries/src/NonlinearArithmetic/Power2.dfy"
// TODO: study what the `LittleEndianNatConversions` is
// include "libraries/src/Collections/Sequences/LittleEndianNatConversions.dfy"
include "libraries/src/Collections/Sequences/LittleEndianNat.dfy"

abstract module QPreludeUntyped {
  import opened LittleEndianNat
  // import opened Seq
  // cast nor type qubit to had type qubit
  function method CastNorHad(q : seq<nat>) : (h : seq<int>) 
    requires forall k : nat | k < |q| :: q[k] == 0 || q[k] == 1
    ensures |h| == |q| && forall k : nat | k < |q| ::
    (q[k] == 0 ==> h[k] == 1) && (q[k] == 1 ==> h[k] == 0)
  ;

  function method CastNorCH10(q : seq<nat>) : (c : seq<nat>)
    requires forall k : nat | k < |q| :: q[k] == 0 || q[k] == 1
    ensures c == [LittleEndianNat.ToNatRight(q)]
  ;
}
