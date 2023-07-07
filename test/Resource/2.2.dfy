include "../../external//QPreludeUntyped.dfy"
include "../../external//libraries/src/Collections/Sequences/Seq.dfy"
include "../../external//libraries/src/NonlinearArithmetic/Power2.dfy"

// target Dafny version: 3.12.0
abstract module QafnyDefault {
import opened QPreludeUntyped
import opened Seq
import opened Power2

import opened QPrelude
import opened DivMod
import opened Mul
import opened Power2
import opened Unity
import opened Seq

// For Qafny Commit: 06badb404e5a1a5603b72ee1dc8c5b72fc5333e5

method DeutschJozsa (n : nat) returns (m : nat)
  requires n > 0
{
  var q : qreg := nor(n, _ => 0);
  var p : qreg := nor(1, _ => 1);
  q *= H;
  p *= H;
  assert typeof (q) is (n) $ had { forall i : nat | i < n :: q[i] == 1 };
  assert typeof (p) is (1) $ had { p[0] == -1 };
}
}