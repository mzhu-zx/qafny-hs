include "../../external//QPreludeUntyped.dfy"
include "../../external//libraries/src/Collections/Sequences/Seq.dfy"
include "../../external//libraries/src/NonlinearArithmetic/Power2.dfy"

// target Dafny version: 3.12.0
abstract module QafnyDefault {
import opened QPreludeUntyped
import opened Seq
import opened Power2

method Shor (q_seq'nat'_0__emit : seq<nat>, p_seq'nat'_1__emit : seq<nat>) returns (q_seq'nat'_0__emit : seq<nat>, p_seq'nat'_1__emit : seq<nat>)
  requires (10 == |q_seq'nat'_0__emit|) && ((forall i : nat | 0 <= i < 10 :: q_seq'nat'_0__emit[i] == 1))
  requires (1 == |p_seq'nat'_1__emit|) && ((forall i : nat | 0 <= i < 1 :: p_seq'nat'_1__emit[i] == 1))
{
  // Forward Declaration
  reveal Map();
  
  // Method Definition
}

}