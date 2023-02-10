// include "~/libraries/src/NonlinearArithmetic/Power2.dfy"
// include "~/libraries/src/NonlinearArithmetic/Power.dfy"
// include "~/libraries/src/NonlinearArithmetic/DivMod.dfy"
// include "~/libraries/src/NonlinearArithmetic/Mul.dfy"
// include "~/libraries/src/Collections/Sequences/Seq.dfy"

// import opened Seq

// cast nor type qubit to had type qubit
function method CastNorHad(q : seq<nat>) : (h : seq<int>) 
  requires forall k : nat | k < |q| :: q[k] == 0 || q[k] == 1
  ensures |h| == |q| && forall k : nat | k < |q| ::
    (q[k] == 0 ==> h[k] == 1) && (q[k] == 1 ==> h[k] == 0)
