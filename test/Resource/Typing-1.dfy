include "../../external//QPreludeUntyped.dfy"
include "../../external//libraries/src/Collections/Sequences/Seq.dfy"
include "../../external//libraries/src/NonlinearArithmetic/Power2.dfy"

// target Dafny version: 3.12.0
abstract module QafnyDefault {
import opened QPreludeUntyped
import opened Seq
import opened Power2

import opened DivMod
import opened Mul
import opened Power2
import opened Unity
method DeutschJozsa (n : nat)
{
  // Forward Declaration
  var p_0_1___seqL_nat_R___3__emit : seq<nat>;
  var q_0_n___seqL_nat_R___2__emit : seq<nat>;
  var p_0_1___seqL_nat_R___1__emit : seq<nat>;
  var q_0_n___seqL_nat_R___0__emit : seq<nat>;
  
  // Method Definition
  q_0_n___seqL_nat_R___0__emit := seq<nat>(n, _ => 0);
  p_0_1___seqL_nat_R___1__emit := seq<nat>(1, _ => 1);
  // Cast TNor ==> THad
  q_0_n___seqL_nat_R___2__emit := CastNorHad(q_0_n___seqL_nat_R___0__emit);
  // Cast TNor ==> THad
  p_0_1___seqL_nat_R___3__emit := CastNorHad(p_0_1___seqL_nat_R___1__emit);
}

method CrossMinus (n : nat, m : nat, q : nat, p : nat)
{
  // Forward Declaration
  
  // Method Definition
}

}