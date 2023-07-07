include "../../external//QPreludeUntyped.dfy"
include "../../external//libraries/src/Collections/Sequences/Seq.dfy"
include "../../external//libraries/src/NonlinearArithmetic/Power2.dfy"

// target Dafny version: 3.12.0
abstract module QafnyDefault {
import opened QPreludeUntyped
import opened Seq
import opened Power2


// For Qafny Commit: 561f5bbbcb1f81abacf2654b75761d1370184ad4

method GHZ0 (n : nat)
{
  // Forward Declaration
  var q_0_1___seqL_nat_R___6__emit : seq<nat>;
  var p_0_1___seqL_nat_R___5__emit : seq<nat>;
  var p_0_1___seqL_nat_R___4__emit : seq<nat>;
  var p_0_1___seqL_nat_R___3__emit : seq<nat>;
  var q_0_1___seqL_nat_R___2__emit : seq<nat>;
  var p_0_1___seqL_nat_R___1__emit : seq<nat>;
  var q_0_1___seqL_nat_R___0__emit : seq<nat>;
  
  // Method Definition
  q_0_1___seqL_nat_R___0__emit := seq<nat>(1, _ => 0);
  p_0_1___seqL_nat_R___1__emit := seq<nat>(1, _ => 0);
  // Cast TNor ==> THad
  q_0_1___seqL_nat_R___2__emit := CastNorHad(q_0_1___seqL_nat_R___0__emit);
  // Cast Body Partition TNor => TEN
  // Cast TNor ==> TEN
  p_0_1___seqL_nat_R___3__emit := CastNorEN(p_0_1___seqL_nat_R___1__emit);
  p_0_1___seqL_nat_R___4__emit := p_0_1___seqL_nat_R___5__emit;
  {
    p_0_1___seqL_nat_R___5__emit := Map(x => x + 1 % 2, p_0_1___seqL_nat_R___5__emit);
  }

  p_0_1___seqL_nat_R___5__emit := p_0_1___seqL_nat_R___5__emit + p_0_1___seqL_nat_R___4__emit;
  // Merge: Body partition + the Guard partition.
  q_0_1___seqL_nat_R___6__emit := seq<nat>(|p_0_1___seqL_nat_R___5__emit|, _ => 0 + 1) + seq<nat>(|p_0_1___seqL_nat_R___4__emit|, _ => 0);
}

}