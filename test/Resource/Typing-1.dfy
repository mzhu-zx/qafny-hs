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

import opened DivMod
import opened Mul
import opened Power2
import opened Unity
method Typing0 (n : nat)
  requires n > 0
{
  // Forward Declaration
  var p_seq'nat'_3__emit : seq<nat>;
  var q_seq'nat'_2__emit : seq<nat>;
  var p_seq'nat'_1__emit : seq<nat>;
  var q_seq'nat'_0__emit : seq<nat>;
  reveal Map();
  reveal Pow2();
  
  // Method Definition
  q_seq'nat'_0__emit := seq<nat>(n, _ => 0);
  p_seq'nat'_1__emit := seq<nat>(1, _ => 1);
  // Cast (TNor,[0]) ==> THad
  q_seq'nat'_2__emit := CastNorHad(q_seq'nat'_0__emit);
  // Cast (TNor,[0]) ==> THad
  p_seq'nat'_3__emit := CastNorHad(p_seq'nat'_1__emit);
}

method CrossMinus (n : nat, m : nat, q : nat, p : nat)
{
  // Forward Declaration
  reveal Map();
  reveal Pow2();
  
  // Method Definition
}

}