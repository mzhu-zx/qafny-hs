import opened QPrelude
import opened DivMod
import opened Mul
import opened Power2
import opened Unity
import opened Seq

// For Qafny Commit: fbb0b20eda52c82411cd90b35ef1a60699f59690

method DeutschJozsa(n : nat)
  requires n > 0
{
  var q : qreg := nor(n, _ => 0);
  var p : qreg := nor(1, _ => 1);
  q *= H;
  p *= H;
  assert typeof (q) is (n) $ had { forall i : nat | i < n :: q[i] == 1 };
  assert typeof (p) is (1) $ had { p[0] == -1 };
}