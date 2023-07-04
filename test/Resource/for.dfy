include "../../external//QPreludeUntyped.dfy"
include "../../external//libraries/src/Collections/Sequences/Seq.dfy"
include "../../external//libraries/src/NonlinearArithmetic/Power2.dfy"

// target Dafny version: 3.12.0
abstract module QafnyDefault {
import opened QPreludeUntyped
import opened Seq
import opened Power2

method For0 (n : nat)
  requires n > 0
{
  // Forward Declaration
  var p_0_n___seqL_nat_R___8__emit : seq<nat>;
  var p_0_n___seqL_nat_R___7__emit : seq<nat>;
  var q_0_n___seqL_nat_R___6__emit : seq<nat>;
  var q_0_n___seqL_nat_R___5__emit : seq<nat>;
  var q_0_n___seqL_nat_R___4__emit : seq<nat>;
  var p_0_n___seqL_nat_R___3__emit : seq<nat>;
  var q_0_n___seqL_nat_R___2__emit : seq<nat>;
  var p_0_n___seqL_nat_R___1__emit : seq<nat>;
  var q_0_n___seqL_nat_R___0__emit : seq<nat>;
  
  // Method Definition
  q_0_n___seqL_nat_R___0__emit := seq<nat>(n, _ => 0);
  p_0_n___seqL_nat_R___1__emit := seq<nat>(n, _ => 0);
  // Cast TNor ==> THad
  q_0_n___seqL_nat_R___2__emit := CastNorHad(q_0_n___seqL_nat_R___0__emit);
  // Cast TNor ==> TEN
  p_0_n___seqL_nat_R___3__emit := CastNorEN(p_0_n___seqL_nat_R___1__emit);
  q_0_n___seqL_nat_R___4__emit := q_0_n___seqL_nat_R___5__emit;
  // Retype from Had to EN and initialize with 0
  q_0_n___seqL_nat_R___6__emit := seq<nat>(|q_0_n___seqL_nat_R___6__emit|, _ => 0);
  for i := 0 to n
  {
    p_0_n___seqL_nat_R___7__emit := p_0_n___seqL_nat_R___8__emit;
    {
      p_0_n___seqL_nat_R___8__emit := Map(x => x + 1 % 2, p_0_n___seqL_nat_R___8__emit);
    }

    p_0_n___seqL_nat_R___8__emit := p_0_n___seqL_nat_R___8__emit + p_0_n___seqL_nat_R___7__emit;
    q_0_n___seqL_nat_R___6__emit := q_0_n___seqL_nat_R___6__emit + Map(x__lambda => x__lambda + Pow2(i), q_0_n___seqL_nat_R___6__emit);
  }

}

}
