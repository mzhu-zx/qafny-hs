include "../../external//QPreludeUntyped.dfy"
include "../../external//libraries/src/Collections/Sequences/Seq.dfy"
include "../../external//libraries/src/NonlinearArithmetic/Power2.dfy"
include "../../external//libraries/src/NonlinearArithmetic/Power.dfy"

// target Dafny version: 4.2.0
abstract module QafnyDefault {
import opened QPreludeUntyped
import opened Seq
import opened Power2
import opened Power
import opened DivMod

method MultiModFull (base : nat, q_seq'nat'_0__emit : seq<nat>, p_seq'nat'_1__emit : seq<nat>) returns (q_seq'nat'_10__emit : seq<nat>, p_seq'nat'_11__emit : seq<nat>)
  requires base >= 3
  requires 10 == |q_seq'nat'_0__emit|
  requires (forall i : nat | 0 <= i < 10 :: q_seq'nat'_0__emit[i] == 1)
  requires 1 == |p_seq'nat'_1__emit|
  requires