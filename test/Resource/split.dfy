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

method SplitTest ()
{
  // Forward Declaration
  var q_seq'nat'_3__emit : seq<nat>;
  var q_seq'nat'_2__emit : seq<nat>;
  var q_seq'nat'_1__emit : seq<nat>;
  var q_seq'nat'_0__emit : seq<nat>;
  reveal Map();
  reveal Pow2();
  
  // Method Definition
  q_seq'nat'_0__emit := seq<nat>(10, _ => 0);
  q_seq'nat'_1__emit := q_seq'nat'_0__emit[0..1];
  // I have no idea why this assertion about equality is necessary....
  assert q_seq'nat'_0__emit[0..1] == q_seq'nat'_1__emit[0..1];
  q_seq'nat'_2__emit := q_seq'nat'_0__emit[1..10];
  // I have no idea why this assertion about equality is necessary....
  assert q_seq'nat'_0__emit[1..10] == q_seq'nat'_2__emit[0..9];
  // Cast (TNor,[0]) ==> THad
  q_seq'nat'_3__emit := CastNorHad(q_seq'nat'_1__emit);
}

}