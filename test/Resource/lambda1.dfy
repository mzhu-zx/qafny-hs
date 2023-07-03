include "../../external//QPreludeUntyped.dfy"
include "../../external//libraries/src/Collections/Sequences/Seq.dfy"
include "../../external//libraries/src/NonlinearArithmetic/Power2.dfy"

// target Dafny version: 3.12.0
abstract module QafnyDefault {
import opened QPreludeUntyped
import opened Seq
import opened Power2

method TestLambda ()
{
  // Forward Declaration
  var q_0_1___seqL_nat_R___3__emit : seq<nat>;
  var q_1_10___seqL_nat_R___2__emit : seq<nat>;
  var q_0_1___seqL_nat_R___1__emit : seq<nat>;
  var q_0_10___seqL_nat_R___0__emit : seq<nat>;
  
  // Method Definition
  q_0_10___seqL_nat_R___0__emit := seq<nat>(10, _ => 0);
  q_0_1___seqL_nat_R___3__emit := Map(x => 1 + x, q_0_1___seqL_nat_R___3__emit);
}

}
