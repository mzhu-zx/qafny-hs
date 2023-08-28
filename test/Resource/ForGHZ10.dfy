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
  var q_0_compact___seqL__seqL_nat_R__R___15__emit : seq<seq<nat>>;
  var q_compact_10___seqL_nat_R___14__emit : seq<nat>;
  var q_compact_compact___seqL_nat_R___13__emit : seq<nat>;
  var q_0_compact___seqL__seqL_nat_R__R___12__emit : seq<seq<nat>>;
  var q_compact_10___seqL_nat_R___11__emit : seq<nat>;
  var q_compact_compact___seqL_nat_R___10__emit : seq<nat>;
  var q_0_compact___seqL__seqL_nat_R__R___9__emit : seq<seq<nat>>;
  var q_compact_10___seqL_nat_R___8__emit : seq<nat>;
  var q_0_compact___seqL__seqL_nat_R__R___7__emit : seq<seq<nat>>;
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
  for i := 0 to 9
    invariant (forall j : nat | 0 <= j < 2 :: (forall k : nat | 0 <= k < 1 + i :: q_0_compact___seqL__seqL_nat_R__R___7__emit[j][k] == j))
    invariant 9 + i == |q_compact_10___seqL_nat_R___8__emit|
    invariant (forall k : nat | 0 <= k < 9 + i :: q_compact_10___seqL_nat_R___8__emit[k] == 0)
  {
    q_0_compact___seqL__seqL_nat_R__R___9__emit := q_0_compact___seqL__seqL_nat_R__R___7__emit[0..1];
    q_0_compact___seqL__seqL_nat_R__R___7__emit := q_0_compact___seqL__seqL_nat_R__R___7__emit[1..|q_0_compact___seqL__seqL_nat_R__R___7__emit|];
    // // begin false
    q_0_compact___seqL__seqL_nat_R__R___12__emit := Map(lambda_x__6 => lambda_x__6 + q_compact_compact___seqL_nat_R___10__emit, q_0_compact___seqL__seqL_nat_R__R___9__emit);
    // // end false
    // // begin true
    q_compact_compact___seqL_nat_R___13__emit := q_compact_compact___seqL_nat_R___13__emit[0..0] + Map(x => x + 1 % 2, q_compact_compact___seqL_nat_R___13__emit[0..2 + i]) + q_compact_compact___seqL_nat_R___13__emit[2 + i..|q_compact_compact___seqL_nat_R___13__emit|];
    q_0_compact___seqL__seqL_nat_R__R___15__emit := Map(lambda_x__8 => lambda_x__8 + q_compact_compact___seqL_nat_R___13__emit, q_0_compact___seqL__seqL_nat_R__R___7__emit);
    // // end true
    q_0_compact___seqL__seqL_nat_R__R___7__emit := q_0_compact___seqL__seqL_nat_R__R___9__emit + q_0_compact___seqL__seqL_nat_R__R___7__emit;
  }

}

}