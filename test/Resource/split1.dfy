include "../../external//QPreludeUntyped.dfy"
include "../../external//libraries/src/Collections/Sequences/Seq.dfy"
include "../../external//libraries/src/NonlinearArithmetic/Power2.dfy"
include "../../external//libraries/src/NonlinearArithmetic/Power.dfy"

// target Dafny version: 4.6.0
abstract module QafnyDefault {
import opened QPreludeUntyped
import opened Seq
import opened Power2
import opened Power
import opened DivMod

method SplitTest () 
  
{
  // Forward Declaration
  var loc__loc__q_0_phase_1__4__emit : seq<nat>;
  var loc__loc__q_0_phase_base_3__emit : nat;
  var q_seq'nat'_2__emit : seq<nat>;
  var q_seq'nat'_1__emit : seq<nat>;
  var q_seq'nat'_0__emit : seq<nat>;
  // Revealing
  reveal Map();
  reveal Pow2();

  // Method Definition
  q_seq'nat'_0__emit := seq<nat>(10, (_) => (0));
  assert |q_seq'nat'_0__emit| == 10;
  q_seq'nat'_2__emit := q_seq'nat'_0__emit[1..10];
  q_seq'nat'_1__emit := q_seq'nat'_0__emit[0..1];
  loc__loc__q_0_phase_1__4__emit := CastNorHad_Phase_1st(q_seq'nat'_1__emit);
  loc__loc__q_0_phase_base_3__emit := 2;
  assert |loc__loc__q_0_phase_1__4__emit| == 1;
  assert |q_seq'nat'_2__emit| == 9;
}
}
