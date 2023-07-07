include "../../external//QPreludeUntyped.dfy"
include "../../external//libraries/src/Collections/Sequences/Seq.dfy"
include "../../external//libraries/src/NonlinearArithmetic/Power2.dfy"

// target Dafny version: 3.12.0
abstract module QafnyDefault {
import opened QPreludeUntyped
import opened Seq
import opened Power2

method SplitTest ()
{
  // Forward Declaration
  var q_8_10___seqL_nat_R___6__emit : seq<nat>;
  var q_0_2___seqL_nat_R___5__emit : seq<nat>;
  var q_2_8___seqL_nat_R___4__emit : seq<nat>;
  var q_8_10___seqL_nat_R___3__emit : seq<nat>;
  var q_0_2___seqL_nat_R___2__emit : seq<nat>;
  var q_2_8___seqL_nat_R___1__emit : seq<nat>;
  var q_0_10___seqL_nat_R___0__emit : seq<nat>;
  
  // Method Definition
  q_0_10___seqL_nat_R___0__emit := seq<nat>(10, _ => 0);
  q_2_8___seqL_nat_R___1__emit := q_0_10___seqL_nat_R___0__emit[2..8];
  q_0_2___seqL_nat_R___2__emit := q_0_10___seqL_nat_R___0__emit[0..2];
  q_8_10___seqL_nat_R___3__emit := q_0_10___seqL_nat_R___0__emit[8..10];
  // Cast TNor ==> THad
  q_2_8___seqL_nat_R___4__emit := CastNorHad(q_2_8___seqL_nat_R___1__emit);
  // Cast TNor ==> THad
  q_0_2___seqL_nat_R___5__emit := CastNorHad(q_0_2___seqL_nat_R___2__emit);
  // Cast TNor ==> THad
  q_8_10___seqL_nat_R___6__emit := CastNorHad(q_8_10___seqL_nat_R___3__emit);
}

}