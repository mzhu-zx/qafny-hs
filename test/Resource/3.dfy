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

// For Qafny Commit: 31dab660309f76006aa91f928e716dc3d852005b

method DeutschJozsa (n : nat)
{
  // Forward Declaration
  var p : seq<nat>;
  var q : seq<nat>;
  var p : seq<nat>;
  var q : seq<nat>;
  
  // Method Definition
  q__seq__nat____0 := seq<nat>(1, _ => 0);
  p__seq__nat____1 := seq<nat>(n, _ => 1);
  // Cast TNor ==> THad
  q__seq__nat____2 := CastNorHad(q__seq__nat____0);
  // Cast TNor ==> THad
  p__seq__nat____3 := CastNorHad(p__seq__nat____1);}

method CrossMinus (n : nat, m : nat, q : nat, p : nat)
{
  // Forward Declaration
  
  // Method Definition}

}