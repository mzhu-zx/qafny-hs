include "../../external//QPreludeUntyped.dfy"
include "../../external//libraries/src/Collections/Sequences/Seq.dfy"
include "../../external//libraries/src/NonlinearArithmetic/Power2.dfy"

// target Dafny version: 3.12.0
abstract module QafnyDefault {
import opened QPreludeUntyped
import opened Seq
import opened Power2

method GHZ (q_0_15___seqL_nat_R___0__emit : seq<nat>) returns (q_0_1___seqL__seqL_nat_R__R___4__emit : seq<seq<nat>>, q_1_10___seqL_nat_R___5__emit : seq<nat>, q_10_15___seqL_nat_R___6__emit : seq<nat>)
  requires 15 == |q_0_15___seqL_nat_R___0__emit| && (forall i : nat | 0 <= i < 15 :: q_0_15___seqL_nat_R___0__emit[i] == 0)
  ensures 5 == |q_10_15___seqL_nat_R___6__emit| && (forall i : nat | 0 <= i < 5 :: q_10_15___seqL_nat_R___6__emit[i] == 0)
{
  // Forward Declaration
  var q_0_l_i__add__1_r___seqL__seqL_nat_R__R___11__emit : seq<seq<nat>>;
  var q_0_l_i__add__1_r___seqL__seqL_nat_R__R___10__emit : seq<seq<nat>>;
  var q_l_i__add__1_r_10___seqL_nat_R___9__emit : seq<nat>;
  var q_l_i__add__1_r_10___seqL_nat_R___8__emit : seq<nat>;
  var q_0_l_i__add__1_r___seqL__seqL_nat_R__R___7__emit : seq<seq<nat>>;
  var q_0_1___seqL_nat_R___3__emit : seq<nat>;
  var q_1_15___seqL_nat_R___2__emit : seq<nat>;
  var q_0_1___seqL_nat_R___1__emit : seq<nat>;
  
  // Method Definition
  q_0_1___seqL_nat_R___1__emit := q_0_15___seqL_nat_R___0__emit[0..1];
  q_1_15___seqL_nat_R___2__emit := q_0_15___seqL_nat_R___0__emit[1..15];
  // Cast TNor ==> THad
  q_0_1___seqL_nat_R___3__emit := CastNorHad(q_0_1___seqL_nat_R___1__emit);
  // Cast THad ==> TEN01
  q_0_1___seqL__seqL_nat_R__R___4__emit := CastHadEN01'1(q_0_1___seqL_nat_R___3__emit);
  q_1_10___seqL_nat_R___5__emit := q_1_15___seqL_nat_R___2__emit[0..9];
  q_10_15___seqL_nat_R___6__emit := q_1_15___seqL_nat_R___2__emit[9..14];
  // Cast TNor ==> TEN
  q_l_i__add__1_r_10___seqL_nat_R___9__emit := CastNorEN(q_l_i__add__1_r_10___seqL_nat_R___8__emit);
  q_0_l_i__add__1_r___seqL__seqL_nat_R__R___10__emit := q_0_l_i__add__1_r___seqL__seqL_nat_R__R___11__emit;
  for i := 0 to 9
  {
  }

}

}