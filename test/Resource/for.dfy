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

method For0 (n : nat)
  requires n > 0
{
  // Forward Declaration
  var p_seq'nat'_9__emit : seq<nat>;
  var q_seq'nat'_8__emit : seq<nat>;
  var q_seq'nat'_7__emit : seq<nat>;
  var q_seq'nat'_6__emit : seq<nat>;
  var p_seq'nat'_5__emit : seq<nat>;
  var q_seq'nat'_4__emit : seq<nat>;
  var q_seq'nat'_3__emit : seq<nat>;
  var q_seq'nat'_2__emit : seq<nat>;
  var p_seq'nat'_1__emit : seq<nat>;
  var q_seq'nat'_0__emit : seq<nat>;
  reveal Map();
  reveal Pow2();
  
  // Method Definition
  q_seq'nat'_0__emit := seq<nat>(n, _ => 0);
  p_seq'nat'_1__emit := seq<nat>(n, _ => 0);
  // Cast (TNor,[0]) ==> THad
  q_seq'nat'_2__emit := CastNorHad(q_seq'nat'_0__emit);
  p_seq'nat'_5__emit := p_seq'nat'_1__emit;
  q_seq'nat'_3__emit := q_seq'nat'_2__emit;
  for i := 0 to n
    invariant //EOp1 ONeg (EVar "i") should not be in emitted form! + n == |q_seq'nat'_3__emit|
    invariant (forall k : nat | 0 <= k < //EOp1 ONeg (EVar "i") should not be in emitted form! + n :: q_seq'nat'_3__emit[k] == 1)
    invar