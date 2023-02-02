 
# import opened QPrelude
# import opened DivMod
# import opened Mul
# import opened Power2
# import opened Unity
# import opened Seq
# 
# // For Qafny Commit: fbb0b20eda52c82411cd90b35ef1a60699f59690
# 
# method DeutschJozsa(n : nat)
#   requires n > 0
# {
#   var q : qreg := nor(n, _ => 0);
#   var p : qreg := nor(1, _ => 1);
#   q *= H;
#   p *= H;
#   assert typeof (q) is (n) $ had { forall i : nat | i < n :: q[i] == 1 };
#   assert typeof (p) is (1) $ had { p[0] == -1 };
# }
# 
# 
# lemma PhaseEquivF(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m && (f(q[i]) == 0 || f(q[i]) == 1)) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m && (f(q[i]) == 0 || f(q[i]) == 1)) &&
#     (forall i : nat | i < m :: 
#       q.GetPhases()[2*i] == (phaseSinglePow(phasem1(), f(q[2*i]))) && 
#       q.GetPhases()[2*i+1] == (phaseSinglePow(phasem1(), (1 + f(q[2*i])))))
#   }
# {
# }
# 
# 
# // if f(x) with x 
# // {
# //   y *= X;
# // }
# 
# method CrossMinus(n : nat, m : nat, q : qreg, p : qreg)
#   requires typeof (q) is exactly (n) $ ch(m) { 
#     forall i : nat | i < m :: unitPhase(q.GetPhases()[i])
#   }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phaseSingleProduct(phase1(), old(q.GetPhases()[i]))) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phaseSingleProduct(phasem1(), old(q.GetPhases()[i]))) && 
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] == old(q.GetSession()[q])
#   }
#   modifies q, p
# 
# method DeutschJozsaOracle(n : nat, p : qreg, q : qreg)
#   requires n > 0
#   requires typeof (q) is (n) $ had { forall i : nat | i < n :: q[i] == 1 }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   modifies q, p
# { 
#   q.PlusToCH();
#   var m := Pow2(n);
#   CrossMinus(n, m, q, p);
#   LemmaSmallMod(2, 4);
#   LemmaSmallMod(0, 4);
#   // This postcondition looks nice but the precondition in
#   // [ApplyWithPositionIrrelavance] is more useful because of [Parititon]  
#   assert typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phase1()) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phasem1()) &&
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m)
#   };
# }
# 
# // We need to bridge the position irrelavence property here 
# method ApplyWithPositionIrrelavence(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

 import opened QPrelude
# import opened DivMod
# import opened Mul
# import opened Power2
# import opened Unity
# import opened Seq
# 
# // For Qafny Commit: fbb0b20eda52c82411cd90b35ef1a60699f59690
# 
# method DeutschJozsa(n : nat)
#   requires n > 0
# {
#   var q : qreg := nor(n, _ => 0);
#   var p : qreg := nor(1, _ => 1);
#   q *= H;
#   p *= H;
#   assert typeof (q) is (n) $ had { forall i : nat | i < n :: q[i] == 1 };
#   assert typeof (p) is (1) $ had { p[0] == -1 };
# }
# 
# 
# lemma PhaseEquivF(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m && (f(q[i]) == 0 || f(q[i]) == 1)) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m && (f(q[i]) == 0 || f(q[i]) == 1)) &&
#     (forall i : nat | i < m :: 
#       q.GetPhases()[2*i] == (phaseSinglePow(phasem1(), f(q[2*i]))) && 
#       q.GetPhases()[2*i+1] == (phaseSinglePow(phasem1(), (1 + f(q[2*i])))))
#   }
# {
# }
# 
# 
# // if f(x) with x 
# // {
# //   y *= X;
# // }
# 
# method CrossMinus(n : nat, m : nat, q : qreg, p : qreg)
#   requires typeof (q) is exactly (n) $ ch(m) { 
#     forall i : nat | i < m :: unitPhase(q.GetPhases()[i])
#   }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phaseSingleProduct(phase1(), old(q.GetPhases()[i]))) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phaseSingleProduct(phasem1(), old(q.GetPhases()[i]))) && 
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] == old(q.GetSession()[q])
#   }
#   modifies q, p
# 
# method DeutschJozsaOracle(n : nat, p : qreg, q : qreg)
#   requires n > 0
#   requires typeof (q) is (n) $ had { forall i : nat | i < n :: q[i] == 1 }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   modifies q, p
# { 
#   q.PlusToCH();
#   var m := Pow2(n);
#   CrossMinus(n, m, q, p);
#   LemmaSmallMod(2, 4);
#   LemmaSmallMod(0, 4);
#   // This postcondition looks nice but the precondition in
#   // [ApplyWithPositionIrrelavance] is more useful because of [Parititon]  
#   assert typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phase1()) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phasem1()) &&
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m)
#   };
# }
# 
# // We need to bridge the position irrelavence property here 
# method ApplyWithPositionIrrelavence(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

 import opened DivMod
# import opened Mul
# import opened Power2
# import opened Unity
# import opened Seq
# 
# // For Qafny Commit: fbb0b20eda52c82411cd90b35ef1a60699f59690
# 
# method DeutschJozsa(n : nat)
#   requires n > 0
# {
#   var q : qreg := nor(n, _ => 0);
#   var p : qreg := nor(1, _ => 1);
#   q *= H;
#   p *= H;
#   assert typeof (q) is (n) $ had { forall i : nat | i < n :: q[i] == 1 };
#   assert typeof (p) is (1) $ had { p[0] == -1 };
# }
# 
# 
# lemma PhaseEquivF(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m && (f(q[i]) == 0 || f(q[i]) == 1)) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m && (f(q[i]) == 0 || f(q[i]) == 1)) &&
#     (forall i : nat | i < m :: 
#       q.GetPhases()[2*i] == (phaseSinglePow(phasem1(), f(q[2*i]))) && 
#       q.GetPhases()[2*i+1] == (phaseSinglePow(phasem1(), (1 + f(q[2*i])))))
#   }
# {
# }
# 
# 
# // if f(x) with x 
# // {
# //   y *= X;
# // }
# 
# method CrossMinus(n : nat, m : nat, q : qreg, p : qreg)
#   requires typeof (q) is exactly (n) $ ch(m) { 
#     forall i : nat | i < m :: unitPhase(q.GetPhases()[i])
#   }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phaseSingleProduct(phase1(), old(q.GetPhases()[i]))) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phaseSingleProduct(phasem1(), old(q.GetPhases()[i]))) && 
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] == old(q.GetSession()[q])
#   }
#   modifies q, p
# 
# method DeutschJozsaOracle(n : nat, p : qreg, q : qreg)
#   requires n > 0
#   requires typeof (q) is (n) $ had { forall i : nat | i < n :: q[i] == 1 }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   modifies q, p
# { 
#   q.PlusToCH();
#   var m := Pow2(n);
#   CrossMinus(n, m, q, p);
#   LemmaSmallMod(2, 4);
#   LemmaSmallMod(0, 4);
#   // This postcondition looks nice but the precondition in
#   // [ApplyWithPositionIrrelavance] is more useful because of [Parititon]  
#   assert typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phase1()) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phasem1()) &&
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m)
#   };
# }
# 
# // We need to bridge the position irrelavence property here 
# method ApplyWithPositionIrrelavence(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

 import opened Mul
# import opened Power2
# import opened Unity
# import opened Seq
# 
# // For Qafny Commit: fbb0b20eda52c82411cd90b35ef1a60699f59690
# 
# method DeutschJozsa(n : nat)
#   requires n > 0
# {
#   var q : qreg := nor(n, _ => 0);
#   var p : qreg := nor(1, _ => 1);
#   q *= H;
#   p *= H;
#   assert typeof (q) is (n) $ had { forall i : nat | i < n :: q[i] == 1 };
#   assert typeof (p) is (1) $ had { p[0] == -1 };
# }
# 
# 
# lemma PhaseEquivF(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m && (f(q[i]) == 0 || f(q[i]) == 1)) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m && (f(q[i]) == 0 || f(q[i]) == 1)) &&
#     (forall i : nat | i < m :: 
#       q.GetPhases()[2*i] == (phaseSinglePow(phasem1(), f(q[2*i]))) && 
#       q.GetPhases()[2*i+1] == (phaseSinglePow(phasem1(), (1 + f(q[2*i])))))
#   }
# {
# }
# 
# 
# // if f(x) with x 
# // {
# //   y *= X;
# // }
# 
# method CrossMinus(n : nat, m : nat, q : qreg, p : qreg)
#   requires typeof (q) is exactly (n) $ ch(m) { 
#     forall i : nat | i < m :: unitPhase(q.GetPhases()[i])
#   }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phaseSingleProduct(phase1(), old(q.GetPhases()[i]))) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phaseSingleProduct(phasem1(), old(q.GetPhases()[i]))) && 
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] == old(q.GetSession()[q])
#   }
#   modifies q, p
# 
# method DeutschJozsaOracle(n : nat, p : qreg, q : qreg)
#   requires n > 0
#   requires typeof (q) is (n) $ had { forall i : nat | i < n :: q[i] == 1 }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   modifies q, p
# { 
#   q.PlusToCH();
#   var m := Pow2(n);
#   CrossMinus(n, m, q, p);
#   LemmaSmallMod(2, 4);
#   LemmaSmallMod(0, 4);
#   // This postcondition looks nice but the precondition in
#   // [ApplyWithPositionIrrelavance] is more useful because of [Parititon]  
#   assert typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phase1()) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phasem1()) &&
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m)
#   };
# }
# 
# // We need to bridge the position irrelavence property here 
# method ApplyWithPositionIrrelavence(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

 import opened Power2
# import opened Unity
# import opened Seq
# 
# // For Qafny Commit: fbb0b20eda52c82411cd90b35ef1a60699f59690
# 
# method DeutschJozsa(n : nat)
#   requires n > 0
# {
#   var q : qreg := nor(n, _ => 0);
#   var p : qreg := nor(1, _ => 1);
#   q *= H;
#   p *= H;
#   assert typeof (q) is (n) $ had { forall i : nat | i < n :: q[i] == 1 };
#   assert typeof (p) is (1) $ had { p[0] == -1 };
# }
# 
# 
# lemma PhaseEquivF(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m && (f(q[i]) == 0 || f(q[i]) == 1)) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m && (f(q[i]) == 0 || f(q[i]) == 1)) &&
#     (forall i : nat | i < m :: 
#       q.GetPhases()[2*i] == (phaseSinglePow(phasem1(), f(q[2*i]))) && 
#       q.GetPhases()[2*i+1] == (phaseSinglePow(phasem1(), (1 + f(q[2*i])))))
#   }
# {
# }
# 
# 
# // if f(x) with x 
# // {
# //   y *= X;
# // }
# 
# method CrossMinus(n : nat, m : nat, q : qreg, p : qreg)
#   requires typeof (q) is exactly (n) $ ch(m) { 
#     forall i : nat | i < m :: unitPhase(q.GetPhases()[i])
#   }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phaseSingleProduct(phase1(), old(q.GetPhases()[i]))) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phaseSingleProduct(phasem1(), old(q.GetPhases()[i]))) && 
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] == old(q.GetSession()[q])
#   }
#   modifies q, p
# 
# method DeutschJozsaOracle(n : nat, p : qreg, q : qreg)
#   requires n > 0
#   requires typeof (q) is (n) $ had { forall i : nat | i < n :: q[i] == 1 }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   modifies q, p
# { 
#   q.PlusToCH();
#   var m := Pow2(n);
#   CrossMinus(n, m, q, p);
#   LemmaSmallMod(2, 4);
#   LemmaSmallMod(0, 4);
#   // This postcondition looks nice but the precondition in
#   // [ApplyWithPositionIrrelavance] is more useful because of [Parititon]  
#   assert typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phase1()) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phasem1()) &&
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m)
#   };
# }
# 
# // We need to bridge the position irrelavence property here 
# method ApplyWithPositionIrrelavence(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

 import opened Unity
# import opened Seq
# 
# // For Qafny Commit: fbb0b20eda52c82411cd90b35ef1a60699f59690
# 
# method DeutschJozsa(n : nat)
#   requires n > 0
# {
#   var q : qreg := nor(n, _ => 0);
#   var p : qreg := nor(1, _ => 1);
#   q *= H;
#   p *= H;
#   assert typeof (q) is (n) $ had { forall i : nat | i < n :: q[i] == 1 };
#   assert typeof (p) is (1) $ had { p[0] == -1 };
# }
# 
# 
# lemma PhaseEquivF(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m && (f(q[i]) == 0 || f(q[i]) == 1)) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m && (f(q[i]) == 0 || f(q[i]) == 1)) &&
#     (forall i : nat | i < m :: 
#       q.GetPhases()[2*i] == (phaseSinglePow(phasem1(), f(q[2*i]))) && 
#       q.GetPhases()[2*i+1] == (phaseSinglePow(phasem1(), (1 + f(q[2*i])))))
#   }
# {
# }
# 
# 
# // if f(x) with x 
# // {
# //   y *= X;
# // }
# 
# method CrossMinus(n : nat, m : nat, q : qreg, p : qreg)
#   requires typeof (q) is exactly (n) $ ch(m) { 
#     forall i : nat | i < m :: unitPhase(q.GetPhases()[i])
#   }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phaseSingleProduct(phase1(), old(q.GetPhases()[i]))) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phaseSingleProduct(phasem1(), old(q.GetPhases()[i]))) && 
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] == old(q.GetSession()[q])
#   }
#   modifies q, p
# 
# method DeutschJozsaOracle(n : nat, p : qreg, q : qreg)
#   requires n > 0
#   requires typeof (q) is (n) $ had { forall i : nat | i < n :: q[i] == 1 }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   modifies q, p
# { 
#   q.PlusToCH();
#   var m := Pow2(n);
#   CrossMinus(n, m, q, p);
#   LemmaSmallMod(2, 4);
#   LemmaSmallMod(0, 4);
#   // This postcondition looks nice but the precondition in
#   // [ApplyWithPositionIrrelavance] is more useful because of [Parititon]  
#   assert typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phase1()) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phasem1()) &&
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m)
#   };
# }
# 
# // We need to bridge the position irrelavence property here 
# method ApplyWithPositionIrrelavence(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

 import opened Seq
# 
# // For Qafny Commit: fbb0b20eda52c82411cd90b35ef1a60699f59690
# 
# method DeutschJozsa(n : nat)
#   requires n > 0
# {
#   var q : qreg := nor(n, _ => 0);
#   var p : qreg := nor(1, _ => 1);
#   q *= H;
#   p *= H;
#   assert typeof (q) is (n) $ had { forall i : nat | i < n :: q[i] == 1 };
#   assert typeof (p) is (1) $ had { p[0] == -1 };
# }
# 
# 
# lemma PhaseEquivF(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m && (f(q[i]) == 0 || f(q[i]) == 1)) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m && (f(q[i]) == 0 || f(q[i]) == 1)) &&
#     (forall i : nat | i < m :: 
#       q.GetPhases()[2*i] == (phaseSinglePow(phasem1(), f(q[2*i]))) && 
#       q.GetPhases()[2*i+1] == (phaseSinglePow(phasem1(), (1 + f(q[2*i])))))
#   }
# {
# }
# 
# 
# // if f(x) with x 
# // {
# //   y *= X;
# // }
# 
# method CrossMinus(n : nat, m : nat, q : qreg, p : qreg)
#   requires typeof (q) is exactly (n) $ ch(m) { 
#     forall i : nat | i < m :: unitPhase(q.GetPhases()[i])
#   }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phaseSingleProduct(phase1(), old(q.GetPhases()[i]))) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phaseSingleProduct(phasem1(), old(q.GetPhases()[i]))) && 
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] == old(q.GetSession()[q])
#   }
#   modifies q, p
# 
# method DeutschJozsaOracle(n : nat, p : qreg, q : qreg)
#   requires n > 0
#   requires typeof (q) is (n) $ had { forall i : nat | i < n :: q[i] == 1 }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   modifies q, p
# { 
#   q.PlusToCH();
#   var m := Pow2(n);
#   CrossMinus(n, m, q, p);
#   LemmaSmallMod(2, 4);
#   LemmaSmallMod(0, 4);
#   // This postcondition looks nice but the precondition in
#   // [ApplyWithPositionIrrelavance] is more useful because of [Parititon]  
#   assert typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phase1()) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phasem1()) &&
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m)
#   };
# }
# 
# // We need to bridge the position irrelavence property here 
# method ApplyWithPositionIrrelavence(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

 
# // For Qafny Commit: fbb0b20eda52c82411cd90b35ef1a60699f59690
# 
# method DeutschJozsa(n : nat)
#   requires n > 0
# {
#   var q : qreg := nor(n, _ => 0);
#   var p : qreg := nor(1, _ => 1);
#   q *= H;
#   p *= H;
#   assert typeof (q) is (n) $ had { forall i : nat | i < n :: q[i] == 1 };
#   assert typeof (p) is (1) $ had { p[0] == -1 };
# }
# 
# 
# lemma PhaseEquivF(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m && (f(q[i]) == 0 || f(q[i]) == 1)) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m && (f(q[i]) == 0 || f(q[i]) == 1)) &&
#     (forall i : nat | i < m :: 
#       q.GetPhases()[2*i] == (phaseSinglePow(phasem1(), f(q[2*i]))) && 
#       q.GetPhases()[2*i+1] == (phaseSinglePow(phasem1(), (1 + f(q[2*i])))))
#   }
# {
# }
# 
# 
# // if f(x) with x 
# // {
# //   y *= X;
# // }
# 
# method CrossMinus(n : nat, m : nat, q : qreg, p : qreg)
#   requires typeof (q) is exactly (n) $ ch(m) { 
#     forall i : nat | i < m :: unitPhase(q.GetPhases()[i])
#   }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phaseSingleProduct(phase1(), old(q.GetPhases()[i]))) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phaseSingleProduct(phasem1(), old(q.GetPhases()[i]))) && 
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] == old(q.GetSession()[q])
#   }
#   modifies q, p
# 
# method DeutschJozsaOracle(n : nat, p : qreg, q : qreg)
#   requires n > 0
#   requires typeof (q) is (n) $ had { forall i : nat | i < n :: q[i] == 1 }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   modifies q, p
# { 
#   q.PlusToCH();
#   var m := Pow2(n);
#   CrossMinus(n, m, q, p);
#   LemmaSmallMod(2, 4);
#   LemmaSmallMod(0, 4);
#   // This postcondition looks nice but the precondition in
#   // [ApplyWithPositionIrrelavance] is more useful because of [Parititon]  
#   assert typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phase1()) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phasem1()) &&
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m)
#   };
# }
# 
# // We need to bridge the position irrelavence property here 
# method ApplyWithPositionIrrelavence(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

 // For Qafny Commit: fbb0b20eda52c82411cd90b35ef1a60699f59690
# 
# method DeutschJozsa(n : nat)
#   requires n > 0
# {
#   var q : qreg := nor(n, _ => 0);
#   var p : qreg := nor(1, _ => 1);
#   q *= H;
#   p *= H;
#   assert typeof (q) is (n) $ had { forall i : nat | i < n :: q[i] == 1 };
#   assert typeof (p) is (1) $ had { p[0] == -1 };
# }
# 
# 
# lemma PhaseEquivF(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m && (f(q[i]) == 0 || f(q[i]) == 1)) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m && (f(q[i]) == 0 || f(q[i]) == 1)) &&
#     (forall i : nat | i < m :: 
#       q.GetPhases()[2*i] == (phaseSinglePow(phasem1(), f(q[2*i]))) && 
#       q.GetPhases()[2*i+1] == (phaseSinglePow(phasem1(), (1 + f(q[2*i])))))
#   }
# {
# }
# 
# 
# // if f(x) with x 
# // {
# //   y *= X;
# // }
# 
# method CrossMinus(n : nat, m : nat, q : qreg, p : qreg)
#   requires typeof (q) is exactly (n) $ ch(m) { 
#     forall i : nat | i < m :: unitPhase(q.GetPhases()[i])
#   }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phaseSingleProduct(phase1(), old(q.GetPhases()[i]))) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phaseSingleProduct(phasem1(), old(q.GetPhases()[i]))) && 
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] == old(q.GetSession()[q])
#   }
#   modifies q, p
# 
# method DeutschJozsaOracle(n : nat, p : qreg, q : qreg)
#   requires n > 0
#   requires typeof (q) is (n) $ had { forall i : nat | i < n :: q[i] == 1 }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   modifies q, p
# { 
#   q.PlusToCH();
#   var m := Pow2(n);
#   CrossMinus(n, m, q, p);
#   LemmaSmallMod(2, 4);
#   LemmaSmallMod(0, 4);
#   // This postcondition looks nice but the precondition in
#   // [ApplyWithPositionIrrelavance] is more useful because of [Parititon]  
#   assert typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phase1()) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phasem1()) &&
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m)
#   };
# }
# 
# // We need to bridge the position irrelavence property here 
# method ApplyWithPositionIrrelavence(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

 
# method DeutschJozsa(n : nat)
#   requires n > 0
# {
#   var q : qreg := nor(n, _ => 0);
#   var p : qreg := nor(1, _ => 1);
#   q *= H;
#   p *= H;
#   assert typeof (q) is (n) $ had { forall i : nat | i < n :: q[i] == 1 };
#   assert typeof (p) is (1) $ had { p[0] == -1 };
# }
# 
# 
# lemma PhaseEquivF(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m && (f(q[i]) == 0 || f(q[i]) == 1)) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m && (f(q[i]) == 0 || f(q[i]) == 1)) &&
#     (forall i : nat | i < m :: 
#       q.GetPhases()[2*i] == (phaseSinglePow(phasem1(), f(q[2*i]))) && 
#       q.GetPhases()[2*i+1] == (phaseSinglePow(phasem1(), (1 + f(q[2*i])))))
#   }
# {
# }
# 
# 
# // if f(x) with x 
# // {
# //   y *= X;
# // }
# 
# method CrossMinus(n : nat, m : nat, q : qreg, p : qreg)
#   requires typeof (q) is exactly (n) $ ch(m) { 
#     forall i : nat | i < m :: unitPhase(q.GetPhases()[i])
#   }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phaseSingleProduct(phase1(), old(q.GetPhases()[i]))) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phaseSingleProduct(phasem1(), old(q.GetPhases()[i]))) && 
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] == old(q.GetSession()[q])
#   }
#   modifies q, p
# 
# method DeutschJozsaOracle(n : nat, p : qreg, q : qreg)
#   requires n > 0
#   requires typeof (q) is (n) $ had { forall i : nat | i < n :: q[i] == 1 }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   modifies q, p
# { 
#   q.PlusToCH();
#   var m := Pow2(n);
#   CrossMinus(n, m, q, p);
#   LemmaSmallMod(2, 4);
#   LemmaSmallMod(0, 4);
#   // This postcondition looks nice but the precondition in
#   // [ApplyWithPositionIrrelavance] is more useful because of [Parititon]  
#   assert typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phase1()) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phasem1()) &&
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m)
#   };
# }
# 
# // We need to bridge the position irrelavence property here 
# method ApplyWithPositionIrrelavence(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

 method DeutschJozsa(n : nat)
#   requires n > 0
# {
#   var q : qreg := nor(n, _ => 0);
#   var p : qreg := nor(1, _ => 1);
#   q *= H;
#   p *= H;
#   assert typeof (q) is (n) $ had { forall i : nat | i < n :: q[i] == 1 };
#   assert typeof (p) is (1) $ had { p[0] == -1 };
# }
# 
# 
# lemma PhaseEquivF(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m && (f(q[i]) == 0 || f(q[i]) == 1)) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m && (f(q[i]) == 0 || f(q[i]) == 1)) &&
#     (forall i : nat | i < m :: 
#       q.GetPhases()[2*i] == (phaseSinglePow(phasem1(), f(q[2*i]))) && 
#       q.GetPhases()[2*i+1] == (phaseSinglePow(phasem1(), (1 + f(q[2*i])))))
#   }
# {
# }
# 
# 
# // if f(x) with x 
# // {
# //   y *= X;
# // }
# 
# method CrossMinus(n : nat, m : nat, q : qreg, p : qreg)
#   requires typeof (q) is exactly (n) $ ch(m) { 
#     forall i : nat | i < m :: unitPhase(q.GetPhases()[i])
#   }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phaseSingleProduct(phase1(), old(q.GetPhases()[i]))) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phaseSingleProduct(phasem1(), old(q.GetPhases()[i]))) && 
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] == old(q.GetSession()[q])
#   }
#   modifies q, p
# 
# method DeutschJozsaOracle(n : nat, p : qreg, q : qreg)
#   requires n > 0
#   requires typeof (q) is (n) $ had { forall i : nat | i < n :: q[i] == 1 }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   modifies q, p
# { 
#   q.PlusToCH();
#   var m := Pow2(n);
#   CrossMinus(n, m, q, p);
#   LemmaSmallMod(2, 4);
#   LemmaSmallMod(0, 4);
#   // This postcondition looks nice but the precondition in
#   // [ApplyWithPositionIrrelavance] is more useful because of [Parititon]  
#   assert typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phase1()) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phasem1()) &&
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m)
#   };
# }
# 
# // We need to bridge the position irrelavence property here 
# method ApplyWithPositionIrrelavence(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

   requires n > 0
# {
#   var q : qreg := nor(n, _ => 0);
#   var p : qreg := nor(1, _ => 1);
#   q *= H;
#   p *= H;
#   assert typeof (q) is (n) $ had { forall i : nat | i < n :: q[i] == 1 };
#   assert typeof (p) is (1) $ had { p[0] == -1 };
# }
# 
# 
# lemma PhaseEquivF(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m && (f(q[i]) == 0 || f(q[i]) == 1)) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m && (f(q[i]) == 0 || f(q[i]) == 1)) &&
#     (forall i : nat | i < m :: 
#       q.GetPhases()[2*i] == (phaseSinglePow(phasem1(), f(q[2*i]))) && 
#       q.GetPhases()[2*i+1] == (phaseSinglePow(phasem1(), (1 + f(q[2*i])))))
#   }
# {
# }
# 
# 
# // if f(x) with x 
# // {
# //   y *= X;
# // }
# 
# method CrossMinus(n : nat, m : nat, q : qreg, p : qreg)
#   requires typeof (q) is exactly (n) $ ch(m) { 
#     forall i : nat | i < m :: unitPhase(q.GetPhases()[i])
#   }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phaseSingleProduct(phase1(), old(q.GetPhases()[i]))) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phaseSingleProduct(phasem1(), old(q.GetPhases()[i]))) && 
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] == old(q.GetSession()[q])
#   }
#   modifies q, p
# 
# method DeutschJozsaOracle(n : nat, p : qreg, q : qreg)
#   requires n > 0
#   requires typeof (q) is (n) $ had { forall i : nat | i < n :: q[i] == 1 }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   modifies q, p
# { 
#   q.PlusToCH();
#   var m := Pow2(n);
#   CrossMinus(n, m, q, p);
#   LemmaSmallMod(2, 4);
#   LemmaSmallMod(0, 4);
#   // This postcondition looks nice but the precondition in
#   // [ApplyWithPositionIrrelavance] is more useful because of [Parititon]  
#   assert typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phase1()) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phasem1()) &&
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m)
#   };
# }
# 
# // We need to bridge the position irrelavence property here 
# method ApplyWithPositionIrrelavence(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

 {
#   var q : qreg := nor(n, _ => 0);
#   var p : qreg := nor(1, _ => 1);
#   q *= H;
#   p *= H;
#   assert typeof (q) is (n) $ had { forall i : nat | i < n :: q[i] == 1 };
#   assert typeof (p) is (1) $ had { p[0] == -1 };
# }
# 
# 
# lemma PhaseEquivF(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m && (f(q[i]) == 0 || f(q[i]) == 1)) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m && (f(q[i]) == 0 || f(q[i]) == 1)) &&
#     (forall i : nat | i < m :: 
#       q.GetPhases()[2*i] == (phaseSinglePow(phasem1(), f(q[2*i]))) && 
#       q.GetPhases()[2*i+1] == (phaseSinglePow(phasem1(), (1 + f(q[2*i])))))
#   }
# {
# }
# 
# 
# // if f(x) with x 
# // {
# //   y *= X;
# // }
# 
# method CrossMinus(n : nat, m : nat, q : qreg, p : qreg)
#   requires typeof (q) is exactly (n) $ ch(m) { 
#     forall i : nat | i < m :: unitPhase(q.GetPhases()[i])
#   }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phaseSingleProduct(phase1(), old(q.GetPhases()[i]))) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phaseSingleProduct(phasem1(), old(q.GetPhases()[i]))) && 
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] == old(q.GetSession()[q])
#   }
#   modifies q, p
# 
# method DeutschJozsaOracle(n : nat, p : qreg, q : qreg)
#   requires n > 0
#   requires typeof (q) is (n) $ had { forall i : nat | i < n :: q[i] == 1 }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   modifies q, p
# { 
#   q.PlusToCH();
#   var m := Pow2(n);
#   CrossMinus(n, m, q, p);
#   LemmaSmallMod(2, 4);
#   LemmaSmallMod(0, 4);
#   // This postcondition looks nice but the precondition in
#   // [ApplyWithPositionIrrelavance] is more useful because of [Parititon]  
#   assert typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phase1()) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phasem1()) &&
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m)
#   };
# }
# 
# // We need to bridge the position irrelavence property here 
# method ApplyWithPositionIrrelavence(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

   var q : qreg := nor(n, _ => 0);
#   var p : qreg := nor(1, _ => 1);
#   q *= H;
#   p *= H;
#   assert typeof (q) is (n) $ had { forall i : nat | i < n :: q[i] == 1 };
#   assert typeof (p) is (1) $ had { p[0] == -1 };
# }
# 
# 
# lemma PhaseEquivF(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m && (f(q[i]) == 0 || f(q[i]) == 1)) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m && (f(q[i]) == 0 || f(q[i]) == 1)) &&
#     (forall i : nat | i < m :: 
#       q.GetPhases()[2*i] == (phaseSinglePow(phasem1(), f(q[2*i]))) && 
#       q.GetPhases()[2*i+1] == (phaseSinglePow(phasem1(), (1 + f(q[2*i])))))
#   }
# {
# }
# 
# 
# // if f(x) with x 
# // {
# //   y *= X;
# // }
# 
# method CrossMinus(n : nat, m : nat, q : qreg, p : qreg)
#   requires typeof (q) is exactly (n) $ ch(m) { 
#     forall i : nat | i < m :: unitPhase(q.GetPhases()[i])
#   }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phaseSingleProduct(phase1(), old(q.GetPhases()[i]))) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phaseSingleProduct(phasem1(), old(q.GetPhases()[i]))) && 
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] == old(q.GetSession()[q])
#   }
#   modifies q, p
# 
# method DeutschJozsaOracle(n : nat, p : qreg, q : qreg)
#   requires n > 0
#   requires typeof (q) is (n) $ had { forall i : nat | i < n :: q[i] == 1 }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   modifies q, p
# { 
#   q.PlusToCH();
#   var m := Pow2(n);
#   CrossMinus(n, m, q, p);
#   LemmaSmallMod(2, 4);
#   LemmaSmallMod(0, 4);
#   // This postcondition looks nice but the precondition in
#   // [ApplyWithPositionIrrelavance] is more useful because of [Parititon]  
#   assert typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phase1()) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phasem1()) &&
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m)
#   };
# }
# 
# // We need to bridge the position irrelavence property here 
# method ApplyWithPositionIrrelavence(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

   var p : qreg := nor(1, _ => 1);
#   q *= H;
#   p *= H;
#   assert typeof (q) is (n) $ had { forall i : nat | i < n :: q[i] == 1 };
#   assert typeof (p) is (1) $ had { p[0] == -1 };
# }
# 
# 
# lemma PhaseEquivF(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m && (f(q[i]) == 0 || f(q[i]) == 1)) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m && (f(q[i]) == 0 || f(q[i]) == 1)) &&
#     (forall i : nat | i < m :: 
#       q.GetPhases()[2*i] == (phaseSinglePow(phasem1(), f(q[2*i]))) && 
#       q.GetPhases()[2*i+1] == (phaseSinglePow(phasem1(), (1 + f(q[2*i])))))
#   }
# {
# }
# 
# 
# // if f(x) with x 
# // {
# //   y *= X;
# // }
# 
# method CrossMinus(n : nat, m : nat, q : qreg, p : qreg)
#   requires typeof (q) is exactly (n) $ ch(m) { 
#     forall i : nat | i < m :: unitPhase(q.GetPhases()[i])
#   }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phaseSingleProduct(phase1(), old(q.GetPhases()[i]))) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phaseSingleProduct(phasem1(), old(q.GetPhases()[i]))) && 
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] == old(q.GetSession()[q])
#   }
#   modifies q, p
# 
# method DeutschJozsaOracle(n : nat, p : qreg, q : qreg)
#   requires n > 0
#   requires typeof (q) is (n) $ had { forall i : nat | i < n :: q[i] == 1 }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   modifies q, p
# { 
#   q.PlusToCH();
#   var m := Pow2(n);
#   CrossMinus(n, m, q, p);
#   LemmaSmallMod(2, 4);
#   LemmaSmallMod(0, 4);
#   // This postcondition looks nice but the precondition in
#   // [ApplyWithPositionIrrelavance] is more useful because of [Parititon]  
#   assert typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phase1()) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phasem1()) &&
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m)
#   };
# }
# 
# // We need to bridge the position irrelavence property here 
# method ApplyWithPositionIrrelavence(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

   q *= H;
#   p *= H;
#   assert typeof (q) is (n) $ had { forall i : nat | i < n :: q[i] == 1 };
#   assert typeof (p) is (1) $ had { p[0] == -1 };
# }
# 
# 
# lemma PhaseEquivF(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m && (f(q[i]) == 0 || f(q[i]) == 1)) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m && (f(q[i]) == 0 || f(q[i]) == 1)) &&
#     (forall i : nat | i < m :: 
#       q.GetPhases()[2*i] == (phaseSinglePow(phasem1(), f(q[2*i]))) && 
#       q.GetPhases()[2*i+1] == (phaseSinglePow(phasem1(), (1 + f(q[2*i])))))
#   }
# {
# }
# 
# 
# // if f(x) with x 
# // {
# //   y *= X;
# // }
# 
# method CrossMinus(n : nat, m : nat, q : qreg, p : qreg)
#   requires typeof (q) is exactly (n) $ ch(m) { 
#     forall i : nat | i < m :: unitPhase(q.GetPhases()[i])
#   }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phaseSingleProduct(phase1(), old(q.GetPhases()[i]))) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phaseSingleProduct(phasem1(), old(q.GetPhases()[i]))) && 
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] == old(q.GetSession()[q])
#   }
#   modifies q, p
# 
# method DeutschJozsaOracle(n : nat, p : qreg, q : qreg)
#   requires n > 0
#   requires typeof (q) is (n) $ had { forall i : nat | i < n :: q[i] == 1 }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   modifies q, p
# { 
#   q.PlusToCH();
#   var m := Pow2(n);
#   CrossMinus(n, m, q, p);
#   LemmaSmallMod(2, 4);
#   LemmaSmallMod(0, 4);
#   // This postcondition looks nice but the precondition in
#   // [ApplyWithPositionIrrelavance] is more useful because of [Parititon]  
#   assert typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phase1()) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phasem1()) &&
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m)
#   };
# }
# 
# // We need to bridge the position irrelavence property here 
# method ApplyWithPositionIrrelavence(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

   p *= H;
#   assert typeof (q) is (n) $ had { forall i : nat | i < n :: q[i] == 1 };
#   assert typeof (p) is (1) $ had { p[0] == -1 };
# }
# 
# 
# lemma PhaseEquivF(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m && (f(q[i]) == 0 || f(q[i]) == 1)) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m && (f(q[i]) == 0 || f(q[i]) == 1)) &&
#     (forall i : nat | i < m :: 
#       q.GetPhases()[2*i] == (phaseSinglePow(phasem1(), f(q[2*i]))) && 
#       q.GetPhases()[2*i+1] == (phaseSinglePow(phasem1(), (1 + f(q[2*i])))))
#   }
# {
# }
# 
# 
# // if f(x) with x 
# // {
# //   y *= X;
# // }
# 
# method CrossMinus(n : nat, m : nat, q : qreg, p : qreg)
#   requires typeof (q) is exactly (n) $ ch(m) { 
#     forall i : nat | i < m :: unitPhase(q.GetPhases()[i])
#   }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phaseSingleProduct(phase1(), old(q.GetPhases()[i]))) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phaseSingleProduct(phasem1(), old(q.GetPhases()[i]))) && 
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] == old(q.GetSession()[q])
#   }
#   modifies q, p
# 
# method DeutschJozsaOracle(n : nat, p : qreg, q : qreg)
#   requires n > 0
#   requires typeof (q) is (n) $ had { forall i : nat | i < n :: q[i] == 1 }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   modifies q, p
# { 
#   q.PlusToCH();
#   var m := Pow2(n);
#   CrossMinus(n, m, q, p);
#   LemmaSmallMod(2, 4);
#   LemmaSmallMod(0, 4);
#   // This postcondition looks nice but the precondition in
#   // [ApplyWithPositionIrrelavance] is more useful because of [Parititon]  
#   assert typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phase1()) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phasem1()) &&
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m)
#   };
# }
# 
# // We need to bridge the position irrelavence property here 
# method ApplyWithPositionIrrelavence(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

   assert typeof (q) is (n) $ had { forall i : nat | i < n :: q[i] == 1 };
#   assert typeof (p) is (1) $ had { p[0] == -1 };
# }
# 
# 
# lemma PhaseEquivF(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m && (f(q[i]) == 0 || f(q[i]) == 1)) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m && (f(q[i]) == 0 || f(q[i]) == 1)) &&
#     (forall i : nat | i < m :: 
#       q.GetPhases()[2*i] == (phaseSinglePow(phasem1(), f(q[2*i]))) && 
#       q.GetPhases()[2*i+1] == (phaseSinglePow(phasem1(), (1 + f(q[2*i])))))
#   }
# {
# }
# 
# 
# // if f(x) with x 
# // {
# //   y *= X;
# // }
# 
# method CrossMinus(n : nat, m : nat, q : qreg, p : qreg)
#   requires typeof (q) is exactly (n) $ ch(m) { 
#     forall i : nat | i < m :: unitPhase(q.GetPhases()[i])
#   }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phaseSingleProduct(phase1(), old(q.GetPhases()[i]))) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phaseSingleProduct(phasem1(), old(q.GetPhases()[i]))) && 
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] == old(q.GetSession()[q])
#   }
#   modifies q, p
# 
# method DeutschJozsaOracle(n : nat, p : qreg, q : qreg)
#   requires n > 0
#   requires typeof (q) is (n) $ had { forall i : nat | i < n :: q[i] == 1 }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   modifies q, p
# { 
#   q.PlusToCH();
#   var m := Pow2(n);
#   CrossMinus(n, m, q, p);
#   LemmaSmallMod(2, 4);
#   LemmaSmallMod(0, 4);
#   // This postcondition looks nice but the precondition in
#   // [ApplyWithPositionIrrelavance] is more useful because of [Parititon]  
#   assert typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phase1()) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phasem1()) &&
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m)
#   };
# }
# 
# // We need to bridge the position irrelavence property here 
# method ApplyWithPositionIrrelavence(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

   assert typeof (p) is (1) $ had { p[0] == -1 };
# }
# 
# 
# lemma PhaseEquivF(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m && (f(q[i]) == 0 || f(q[i]) == 1)) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m && (f(q[i]) == 0 || f(q[i]) == 1)) &&
#     (forall i : nat | i < m :: 
#       q.GetPhases()[2*i] == (phaseSinglePow(phasem1(), f(q[2*i]))) && 
#       q.GetPhases()[2*i+1] == (phaseSinglePow(phasem1(), (1 + f(q[2*i])))))
#   }
# {
# }
# 
# 
# // if f(x) with x 
# // {
# //   y *= X;
# // }
# 
# method CrossMinus(n : nat, m : nat, q : qreg, p : qreg)
#   requires typeof (q) is exactly (n) $ ch(m) { 
#     forall i : nat | i < m :: unitPhase(q.GetPhases()[i])
#   }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phaseSingleProduct(phase1(), old(q.GetPhases()[i]))) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phaseSingleProduct(phasem1(), old(q.GetPhases()[i]))) && 
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] == old(q.GetSession()[q])
#   }
#   modifies q, p
# 
# method DeutschJozsaOracle(n : nat, p : qreg, q : qreg)
#   requires n > 0
#   requires typeof (q) is (n) $ had { forall i : nat | i < n :: q[i] == 1 }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   modifies q, p
# { 
#   q.PlusToCH();
#   var m := Pow2(n);
#   CrossMinus(n, m, q, p);
#   LemmaSmallMod(2, 4);
#   LemmaSmallMod(0, 4);
#   // This postcondition looks nice but the precondition in
#   // [ApplyWithPositionIrrelavance] is more useful because of [Parititon]  
#   assert typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phase1()) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phasem1()) &&
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m)
#   };
# }
# 
# // We need to bridge the position irrelavence property here 
# method ApplyWithPositionIrrelavence(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

 }
# 
# 
# lemma PhaseEquivF(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m && (f(q[i]) == 0 || f(q[i]) == 1)) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m && (f(q[i]) == 0 || f(q[i]) == 1)) &&
#     (forall i : nat | i < m :: 
#       q.GetPhases()[2*i] == (phaseSinglePow(phasem1(), f(q[2*i]))) && 
#       q.GetPhases()[2*i+1] == (phaseSinglePow(phasem1(), (1 + f(q[2*i])))))
#   }
# {
# }
# 
# 
# // if f(x) with x 
# // {
# //   y *= X;
# // }
# 
# method CrossMinus(n : nat, m : nat, q : qreg, p : qreg)
#   requires typeof (q) is exactly (n) $ ch(m) { 
#     forall i : nat | i < m :: unitPhase(q.GetPhases()[i])
#   }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phaseSingleProduct(phase1(), old(q.GetPhases()[i]))) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phaseSingleProduct(phasem1(), old(q.GetPhases()[i]))) && 
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] == old(q.GetSession()[q])
#   }
#   modifies q, p
# 
# method DeutschJozsaOracle(n : nat, p : qreg, q : qreg)
#   requires n > 0
#   requires typeof (q) is (n) $ had { forall i : nat | i < n :: q[i] == 1 }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   modifies q, p
# { 
#   q.PlusToCH();
#   var m := Pow2(n);
#   CrossMinus(n, m, q, p);
#   LemmaSmallMod(2, 4);
#   LemmaSmallMod(0, 4);
#   // This postcondition looks nice but the precondition in
#   // [ApplyWithPositionIrrelavance] is more useful because of [Parititon]  
#   assert typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phase1()) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phasem1()) &&
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m)
#   };
# }
# 
# // We need to bridge the position irrelavence property here 
# method ApplyWithPositionIrrelavence(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

 
# 
# lemma PhaseEquivF(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m && (f(q[i]) == 0 || f(q[i]) == 1)) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m && (f(q[i]) == 0 || f(q[i]) == 1)) &&
#     (forall i : nat | i < m :: 
#       q.GetPhases()[2*i] == (phaseSinglePow(phasem1(), f(q[2*i]))) && 
#       q.GetPhases()[2*i+1] == (phaseSinglePow(phasem1(), (1 + f(q[2*i])))))
#   }
# {
# }
# 
# 
# // if f(x) with x 
# // {
# //   y *= X;
# // }
# 
# method CrossMinus(n : nat, m : nat, q : qreg, p : qreg)
#   requires typeof (q) is exactly (n) $ ch(m) { 
#     forall i : nat | i < m :: unitPhase(q.GetPhases()[i])
#   }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phaseSingleProduct(phase1(), old(q.GetPhases()[i]))) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phaseSingleProduct(phasem1(), old(q.GetPhases()[i]))) && 
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] == old(q.GetSession()[q])
#   }
#   modifies q, p
# 
# method DeutschJozsaOracle(n : nat, p : qreg, q : qreg)
#   requires n > 0
#   requires typeof (q) is (n) $ had { forall i : nat | i < n :: q[i] == 1 }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   modifies q, p
# { 
#   q.PlusToCH();
#   var m := Pow2(n);
#   CrossMinus(n, m, q, p);
#   LemmaSmallMod(2, 4);
#   LemmaSmallMod(0, 4);
#   // This postcondition looks nice but the precondition in
#   // [ApplyWithPositionIrrelavance] is more useful because of [Parititon]  
#   assert typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phase1()) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phasem1()) &&
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m)
#   };
# }
# 
# // We need to bridge the position irrelavence property here 
# method ApplyWithPositionIrrelavence(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

 
# lemma PhaseEquivF(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m && (f(q[i]) == 0 || f(q[i]) == 1)) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m && (f(q[i]) == 0 || f(q[i]) == 1)) &&
#     (forall i : nat | i < m :: 
#       q.GetPhases()[2*i] == (phaseSinglePow(phasem1(), f(q[2*i]))) && 
#       q.GetPhases()[2*i+1] == (phaseSinglePow(phasem1(), (1 + f(q[2*i])))))
#   }
# {
# }
# 
# 
# // if f(x) with x 
# // {
# //   y *= X;
# // }
# 
# method CrossMinus(n : nat, m : nat, q : qreg, p : qreg)
#   requires typeof (q) is exactly (n) $ ch(m) { 
#     forall i : nat | i < m :: unitPhase(q.GetPhases()[i])
#   }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phaseSingleProduct(phase1(), old(q.GetPhases()[i]))) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phaseSingleProduct(phasem1(), old(q.GetPhases()[i]))) && 
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] == old(q.GetSession()[q])
#   }
#   modifies q, p
# 
# method DeutschJozsaOracle(n : nat, p : qreg, q : qreg)
#   requires n > 0
#   requires typeof (q) is (n) $ had { forall i : nat | i < n :: q[i] == 1 }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   modifies q, p
# { 
#   q.PlusToCH();
#   var m := Pow2(n);
#   CrossMinus(n, m, q, p);
#   LemmaSmallMod(2, 4);
#   LemmaSmallMod(0, 4);
#   // This postcondition looks nice but the precondition in
#   // [ApplyWithPositionIrrelavance] is more useful because of [Parititon]  
#   assert typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phase1()) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phasem1()) &&
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m)
#   };
# }
# 
# // We need to bridge the position irrelavence property here 
# method ApplyWithPositionIrrelavence(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

 lemma PhaseEquivF(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m && (f(q[i]) == 0 || f(q[i]) == 1)) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m && (f(q[i]) == 0 || f(q[i]) == 1)) &&
#     (forall i : nat | i < m :: 
#       q.GetPhases()[2*i] == (phaseSinglePow(phasem1(), f(q[2*i]))) && 
#       q.GetPhases()[2*i+1] == (phaseSinglePow(phasem1(), (1 + f(q[2*i])))))
#   }
# {
# }
# 
# 
# // if f(x) with x 
# // {
# //   y *= X;
# // }
# 
# method CrossMinus(n : nat, m : nat, q : qreg, p : qreg)
#   requires typeof (q) is exactly (n) $ ch(m) { 
#     forall i : nat | i < m :: unitPhase(q.GetPhases()[i])
#   }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phaseSingleProduct(phase1(), old(q.GetPhases()[i]))) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phaseSingleProduct(phasem1(), old(q.GetPhases()[i]))) && 
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] == old(q.GetSession()[q])
#   }
#   modifies q, p
# 
# method DeutschJozsaOracle(n : nat, p : qreg, q : qreg)
#   requires n > 0
#   requires typeof (q) is (n) $ had { forall i : nat | i < n :: q[i] == 1 }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   modifies q, p
# { 
#   q.PlusToCH();
#   var m := Pow2(n);
#   CrossMinus(n, m, q, p);
#   LemmaSmallMod(2, 4);
#   LemmaSmallMod(0, 4);
#   // This postcondition looks nice but the precondition in
#   // [ApplyWithPositionIrrelavance] is more useful because of [Parititon]  
#   assert typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phase1()) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phasem1()) &&
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m)
#   };
# }
# 
# // We need to bridge the position irrelavence property here 
# method ApplyWithPositionIrrelavence(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m && (f(q[i]) == 0 || f(q[i]) == 1)) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m && (f(q[i]) == 0 || f(q[i]) == 1)) &&
#     (forall i : nat | i < m :: 
#       q.GetPhases()[2*i] == (phaseSinglePow(phasem1(), f(q[2*i]))) && 
#       q.GetPhases()[2*i+1] == (phaseSinglePow(phasem1(), (1 + f(q[2*i])))))
#   }
# {
# }
# 
# 
# // if f(x) with x 
# // {
# //   y *= X;
# // }
# 
# method CrossMinus(n : nat, m : nat, q : qreg, p : qreg)
#   requires typeof (q) is exactly (n) $ ch(m) { 
#     forall i : nat | i < m :: unitPhase(q.GetPhases()[i])
#   }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phaseSingleProduct(phase1(), old(q.GetPhases()[i]))) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phaseSingleProduct(phasem1(), old(q.GetPhases()[i]))) && 
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] == old(q.GetSession()[q])
#   }
#   modifies q, p
# 
# method DeutschJozsaOracle(n : nat, p : qreg, q : qreg)
#   requires n > 0
#   requires typeof (q) is (n) $ had { forall i : nat | i < n :: q[i] == 1 }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   modifies q, p
# { 
#   q.PlusToCH();
#   var m := Pow2(n);
#   CrossMinus(n, m, q, p);
#   LemmaSmallMod(2, 4);
#   LemmaSmallMod(0, 4);
#   // This postcondition looks nice but the precondition in
#   // [ApplyWithPositionIrrelavance] is more useful because of [Parititon]  
#   assert typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phase1()) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phasem1()) &&
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m)
#   };
# }
# 
# // We need to bridge the position irrelavence property here 
# method ApplyWithPositionIrrelavence(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m && (f(q[i]) == 0 || f(q[i]) == 1)) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m && (f(q[i]) == 0 || f(q[i]) == 1)) &&
#     (forall i : nat | i < m :: 
#       q.GetPhases()[2*i] == (phaseSinglePow(phasem1(), f(q[2*i]))) && 
#       q.GetPhases()[2*i+1] == (phaseSinglePow(phasem1(), (1 + f(q[2*i])))))
#   }
# {
# }
# 
# 
# // if f(x) with x 
# // {
# //   y *= X;
# // }
# 
# method CrossMinus(n : nat, m : nat, q : qreg, p : qreg)
#   requires typeof (q) is exactly (n) $ ch(m) { 
#     forall i : nat | i < m :: unitPhase(q.GetPhases()[i])
#   }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phaseSingleProduct(phase1(), old(q.GetPhases()[i]))) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phaseSingleProduct(phasem1(), old(q.GetPhases()[i]))) && 
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] == old(q.GetSession()[q])
#   }
#   modifies q, p
# 
# method DeutschJozsaOracle(n : nat, p : qreg, q : qreg)
#   requires n > 0
#   requires typeof (q) is (n) $ had { forall i : nat | i < n :: q[i] == 1 }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   modifies q, p
# { 
#   q.PlusToCH();
#   var m := Pow2(n);
#   CrossMinus(n, m, q, p);
#   LemmaSmallMod(2, 4);
#   LemmaSmallMod(0, 4);
#   // This postcondition looks nice but the precondition in
#   // [ApplyWithPositionIrrelavance] is more useful because of [Parititon]  
#   assert typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phase1()) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phasem1()) &&
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m)
#   };
# }
# 
# // We need to bridge the position irrelavence property here 
# method ApplyWithPositionIrrelavence(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m && (f(q[i]) == 0 || f(q[i]) == 1)) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m && (f(q[i]) == 0 || f(q[i]) == 1)) &&
#     (forall i : nat | i < m :: 
#       q.GetPhases()[2*i] == (phaseSinglePow(phasem1(), f(q[2*i]))) && 
#       q.GetPhases()[2*i+1] == (phaseSinglePow(phasem1(), (1 + f(q[2*i])))))
#   }
# {
# }
# 
# 
# // if f(x) with x 
# // {
# //   y *= X;
# // }
# 
# method CrossMinus(n : nat, m : nat, q : qreg, p : qreg)
#   requires typeof (q) is exactly (n) $ ch(m) { 
#     forall i : nat | i < m :: unitPhase(q.GetPhases()[i])
#   }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phaseSingleProduct(phase1(), old(q.GetPhases()[i]))) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phaseSingleProduct(phasem1(), old(q.GetPhases()[i]))) && 
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] == old(q.GetSession()[q])
#   }
#   modifies q, p
# 
# method DeutschJozsaOracle(n : nat, p : qreg, q : qreg)
#   requires n > 0
#   requires typeof (q) is (n) $ had { forall i : nat | i < n :: q[i] == 1 }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   modifies q, p
# { 
#   q.PlusToCH();
#   var m := Pow2(n);
#   CrossMinus(n, m, q, p);
#   LemmaSmallMod(2, 4);
#   LemmaSmallMod(0, 4);
#   // This postcondition looks nice but the precondition in
#   // [ApplyWithPositionIrrelavance] is more useful because of [Parititon]  
#   assert typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phase1()) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phasem1()) &&
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m)
#   };
# }
# 
# // We need to bridge the position irrelavence property here 
# method ApplyWithPositionIrrelavence(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

     (forall i : nat | i < 2 * m :: 0 <= q[i] < m && (f(q[i]) == 0 || f(q[i]) == 1)) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m && (f(q[i]) == 0 || f(q[i]) == 1)) &&
#     (forall i : nat | i < m :: 
#       q.GetPhases()[2*i] == (phaseSinglePow(phasem1(), f(q[2*i]))) && 
#       q.GetPhases()[2*i+1] == (phaseSinglePow(phasem1(), (1 + f(q[2*i])))))
#   }
# {
# }
# 
# 
# // if f(x) with x 
# // {
# //   y *= X;
# // }
# 
# method CrossMinus(n : nat, m : nat, q : qreg, p : qreg)
#   requires typeof (q) is exactly (n) $ ch(m) { 
#     forall i : nat | i < m :: unitPhase(q.GetPhases()[i])
#   }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phaseSingleProduct(phase1(), old(q.GetPhases()[i]))) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phaseSingleProduct(phasem1(), old(q.GetPhases()[i]))) && 
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] == old(q.GetSession()[q])
#   }
#   modifies q, p
# 
# method DeutschJozsaOracle(n : nat, p : qreg, q : qreg)
#   requires n > 0
#   requires typeof (q) is (n) $ had { forall i : nat | i < n :: q[i] == 1 }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   modifies q, p
# { 
#   q.PlusToCH();
#   var m := Pow2(n);
#   CrossMinus(n, m, q, p);
#   LemmaSmallMod(2, 4);
#   LemmaSmallMod(0, 4);
#   // This postcondition looks nice but the precondition in
#   // [ApplyWithPositionIrrelavance] is more useful because of [Parititon]  
#   assert typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phase1()) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phasem1()) &&
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m)
#   };
# }
# 
# // We need to bridge the position irrelavence property here 
# method ApplyWithPositionIrrelavence(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m && (f(q[i]) == 0 || f(q[i]) == 1)) &&
#     (forall i : nat | i < m :: 
#       q.GetPhases()[2*i] == (phaseSinglePow(phasem1(), f(q[2*i]))) && 
#       q.GetPhases()[2*i+1] == (phaseSinglePow(phasem1(), (1 + f(q[2*i])))))
#   }
# {
# }
# 
# 
# // if f(x) with x 
# // {
# //   y *= X;
# // }
# 
# method CrossMinus(n : nat, m : nat, q : qreg, p : qreg)
#   requires typeof (q) is exactly (n) $ ch(m) { 
#     forall i : nat | i < m :: unitPhase(q.GetPhases()[i])
#   }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phaseSingleProduct(phase1(), old(q.GetPhases()[i]))) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phaseSingleProduct(phasem1(), old(q.GetPhases()[i]))) && 
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] == old(q.GetSession()[q])
#   }
#   modifies q, p
# 
# method DeutschJozsaOracle(n : nat, p : qreg, q : qreg)
#   requires n > 0
#   requires typeof (q) is (n) $ had { forall i : nat | i < n :: q[i] == 1 }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   modifies q, p
# { 
#   q.PlusToCH();
#   var m := Pow2(n);
#   CrossMinus(n, m, q, p);
#   LemmaSmallMod(2, 4);
#   LemmaSmallMod(0, 4);
#   // This postcondition looks nice but the precondition in
#   // [ApplyWithPositionIrrelavance] is more useful because of [Parititon]  
#   assert typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phase1()) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phasem1()) &&
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m)
#   };
# }
# 
# // We need to bridge the position irrelavence property here 
# method ApplyWithPositionIrrelavence(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m && (f(q[i]) == 0 || f(q[i]) == 1)) &&
#     (forall i : nat | i < m :: 
#       q.GetPhases()[2*i] == (phaseSinglePow(phasem1(), f(q[2*i]))) && 
#       q.GetPhases()[2*i+1] == (phaseSinglePow(phasem1(), (1 + f(q[2*i])))))
#   }
# {
# }
# 
# 
# // if f(x) with x 
# // {
# //   y *= X;
# // }
# 
# method CrossMinus(n : nat, m : nat, q : qreg, p : qreg)
#   requires typeof (q) is exactly (n) $ ch(m) { 
#     forall i : nat | i < m :: unitPhase(q.GetPhases()[i])
#   }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phaseSingleProduct(phase1(), old(q.GetPhases()[i]))) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phaseSingleProduct(phasem1(), old(q.GetPhases()[i]))) && 
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] == old(q.GetSession()[q])
#   }
#   modifies q, p
# 
# method DeutschJozsaOracle(n : nat, p : qreg, q : qreg)
#   requires n > 0
#   requires typeof (q) is (n) $ had { forall i : nat | i < n :: q[i] == 1 }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   modifies q, p
# { 
#   q.PlusToCH();
#   var m := Pow2(n);
#   CrossMinus(n, m, q, p);
#   LemmaSmallMod(2, 4);
#   LemmaSmallMod(0, 4);
#   // This postcondition looks nice but the precondition in
#   // [ApplyWithPositionIrrelavance] is more useful because of [Parititon]  
#   assert typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phase1()) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phasem1()) &&
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m)
#   };
# }
# 
# // We need to bridge the position irrelavence property here 
# method ApplyWithPositionIrrelavence(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m && (f(q[i]) == 0 || f(q[i]) == 1)) &&
#     (forall i : nat | i < m :: 
#       q.GetPhases()[2*i] == (phaseSinglePow(phasem1(), f(q[2*i]))) && 
#       q.GetPhases()[2*i+1] == (phaseSinglePow(phasem1(), (1 + f(q[2*i])))))
#   }
# {
# }
# 
# 
# // if f(x) with x 
# // {
# //   y *= X;
# // }
# 
# method CrossMinus(n : nat, m : nat, q : qreg, p : qreg)
#   requires typeof (q) is exactly (n) $ ch(m) { 
#     forall i : nat | i < m :: unitPhase(q.GetPhases()[i])
#   }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phaseSingleProduct(phase1(), old(q.GetPhases()[i]))) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phaseSingleProduct(phasem1(), old(q.GetPhases()[i]))) && 
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] == old(q.GetSession()[q])
#   }
#   modifies q, p
# 
# method DeutschJozsaOracle(n : nat, p : qreg, q : qreg)
#   requires n > 0
#   requires typeof (q) is (n) $ had { forall i : nat | i < n :: q[i] == 1 }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   modifies q, p
# { 
#   q.PlusToCH();
#   var m := Pow2(n);
#   CrossMinus(n, m, q, p);
#   LemmaSmallMod(2, 4);
#   LemmaSmallMod(0, 4);
#   // This postcondition looks nice but the precondition in
#   // [ApplyWithPositionIrrelavance] is more useful because of [Parititon]  
#   assert typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phase1()) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phasem1()) &&
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m)
#   };
# }
# 
# // We need to bridge the position irrelavence property here 
# method ApplyWithPositionIrrelavence(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m && (f(q[i]) == 0 || f(q[i]) == 1)) &&
#     (forall i : nat | i < m :: 
#       q.GetPhases()[2*i] == (phaseSinglePow(phasem1(), f(q[2*i]))) && 
#       q.GetPhases()[2*i+1] == (phaseSinglePow(phasem1(), (1 + f(q[2*i])))))
#   }
# {
# }
# 
# 
# // if f(x) with x 
# // {
# //   y *= X;
# // }
# 
# method CrossMinus(n : nat, m : nat, q : qreg, p : qreg)
#   requires typeof (q) is exactly (n) $ ch(m) { 
#     forall i : nat | i < m :: unitPhase(q.GetPhases()[i])
#   }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phaseSingleProduct(phase1(), old(q.GetPhases()[i]))) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phaseSingleProduct(phasem1(), old(q.GetPhases()[i]))) && 
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] == old(q.GetSession()[q])
#   }
#   modifies q, p
# 
# method DeutschJozsaOracle(n : nat, p : qreg, q : qreg)
#   requires n > 0
#   requires typeof (q) is (n) $ had { forall i : nat | i < n :: q[i] == 1 }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   modifies q, p
# { 
#   q.PlusToCH();
#   var m := Pow2(n);
#   CrossMinus(n, m, q, p);
#   LemmaSmallMod(2, 4);
#   LemmaSmallMod(0, 4);
#   // This postcondition looks nice but the precondition in
#   // [ApplyWithPositionIrrelavance] is more useful because of [Parititon]  
#   assert typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phase1()) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phasem1()) &&
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m)
#   };
# }
# 
# // We need to bridge the position irrelavence property here 
# method ApplyWithPositionIrrelavence(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m && (f(q[i]) == 0 || f(q[i]) == 1)) &&
#     (forall i : nat | i < m :: 
#       q.GetPhases()[2*i] == (phaseSinglePow(phasem1(), f(q[2*i]))) && 
#       q.GetPhases()[2*i+1] == (phaseSinglePow(phasem1(), (1 + f(q[2*i])))))
#   }
# {
# }
# 
# 
# // if f(x) with x 
# // {
# //   y *= X;
# // }
# 
# method CrossMinus(n : nat, m : nat, q : qreg, p : qreg)
#   requires typeof (q) is exactly (n) $ ch(m) { 
#     forall i : nat | i < m :: unitPhase(q.GetPhases()[i])
#   }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phaseSingleProduct(phase1(), old(q.GetPhases()[i]))) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phaseSingleProduct(phasem1(), old(q.GetPhases()[i]))) && 
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] == old(q.GetSession()[q])
#   }
#   modifies q, p
# 
# method DeutschJozsaOracle(n : nat, p : qreg, q : qreg)
#   requires n > 0
#   requires typeof (q) is (n) $ had { forall i : nat | i < n :: q[i] == 1 }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   modifies q, p
# { 
#   q.PlusToCH();
#   var m := Pow2(n);
#   CrossMinus(n, m, q, p);
#   LemmaSmallMod(2, 4);
#   LemmaSmallMod(0, 4);
#   // This postcondition looks nice but the precondition in
#   // [ApplyWithPositionIrrelavance] is more useful because of [Parititon]  
#   assert typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phase1()) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phasem1()) &&
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m)
#   };
# }
# 
# // We need to bridge the position irrelavence property here 
# method ApplyWithPositionIrrelavence(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m && (f(q[i]) == 0 || f(q[i]) == 1)) &&
#     (forall i : nat | i < m :: 
#       q.GetPhases()[2*i] == (phaseSinglePow(phasem1(), f(q[2*i]))) && 
#       q.GetPhases()[2*i+1] == (phaseSinglePow(phasem1(), (1 + f(q[2*i])))))
#   }
# {
# }
# 
# 
# // if f(x) with x 
# // {
# //   y *= X;
# // }
# 
# method CrossMinus(n : nat, m : nat, q : qreg, p : qreg)
#   requires typeof (q) is exactly (n) $ ch(m) { 
#     forall i : nat | i < m :: unitPhase(q.GetPhases()[i])
#   }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phaseSingleProduct(phase1(), old(q.GetPhases()[i]))) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phaseSingleProduct(phasem1(), old(q.GetPhases()[i]))) && 
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] == old(q.GetSession()[q])
#   }
#   modifies q, p
# 
# method DeutschJozsaOracle(n : nat, p : qreg, q : qreg)
#   requires n > 0
#   requires typeof (q) is (n) $ had { forall i : nat | i < n :: q[i] == 1 }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   modifies q, p
# { 
#   q.PlusToCH();
#   var m := Pow2(n);
#   CrossMinus(n, m, q, p);
#   LemmaSmallMod(2, 4);
#   LemmaSmallMod(0, 4);
#   // This postcondition looks nice but the precondition in
#   // [ApplyWithPositionIrrelavance] is more useful because of [Parititon]  
#   assert typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phase1()) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phasem1()) &&
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m)
#   };
# }
# 
# // We need to bridge the position irrelavence property here 
# method ApplyWithPositionIrrelavence(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m && (f(q[i]) == 0 || f(q[i]) == 1)) &&
#     (forall i : nat | i < m :: 
#       q.GetPhases()[2*i] == (phaseSinglePow(phasem1(), f(q[2*i]))) && 
#       q.GetPhases()[2*i+1] == (phaseSinglePow(phasem1(), (1 + f(q[2*i])))))
#   }
# {
# }
# 
# 
# // if f(x) with x 
# // {
# //   y *= X;
# // }
# 
# method CrossMinus(n : nat, m : nat, q : qreg, p : qreg)
#   requires typeof (q) is exactly (n) $ ch(m) { 
#     forall i : nat | i < m :: unitPhase(q.GetPhases()[i])
#   }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phaseSingleProduct(phase1(), old(q.GetPhases()[i]))) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phaseSingleProduct(phasem1(), old(q.GetPhases()[i]))) && 
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] == old(q.GetSession()[q])
#   }
#   modifies q, p
# 
# method DeutschJozsaOracle(n : nat, p : qreg, q : qreg)
#   requires n > 0
#   requires typeof (q) is (n) $ had { forall i : nat | i < n :: q[i] == 1 }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   modifies q, p
# { 
#   q.PlusToCH();
#   var m := Pow2(n);
#   CrossMinus(n, m, q, p);
#   LemmaSmallMod(2, 4);
#   LemmaSmallMod(0, 4);
#   // This postcondition looks nice but the precondition in
#   // [ApplyWithPositionIrrelavance] is more useful because of [Parititon]  
#   assert typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phase1()) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phasem1()) &&
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m)
#   };
# }
# 
# // We need to bridge the position irrelavence property here 
# method ApplyWithPositionIrrelavence(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m && (f(q[i]) == 0 || f(q[i]) == 1)) &&
#     (forall i : nat | i < m :: 
#       q.GetPhases()[2*i] == (phaseSinglePow(phasem1(), f(q[2*i]))) && 
#       q.GetPhases()[2*i+1] == (phaseSinglePow(phasem1(), (1 + f(q[2*i])))))
#   }
# {
# }
# 
# 
# // if f(x) with x 
# // {
# //   y *= X;
# // }
# 
# method CrossMinus(n : nat, m : nat, q : qreg, p : qreg)
#   requires typeof (q) is exactly (n) $ ch(m) { 
#     forall i : nat | i < m :: unitPhase(q.GetPhases()[i])
#   }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phaseSingleProduct(phase1(), old(q.GetPhases()[i]))) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phaseSingleProduct(phasem1(), old(q.GetPhases()[i]))) && 
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] == old(q.GetSession()[q])
#   }
#   modifies q, p
# 
# method DeutschJozsaOracle(n : nat, p : qreg, q : qreg)
#   requires n > 0
#   requires typeof (q) is (n) $ had { forall i : nat | i < n :: q[i] == 1 }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   modifies q, p
# { 
#   q.PlusToCH();
#   var m := Pow2(n);
#   CrossMinus(n, m, q, p);
#   LemmaSmallMod(2, 4);
#   LemmaSmallMod(0, 4);
#   // This postcondition looks nice but the precondition in
#   // [ApplyWithPositionIrrelavance] is more useful because of [Parititon]  
#   assert typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phase1()) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phasem1()) &&
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m)
#   };
# }
# 
# // We need to bridge the position irrelavence property here 
# method ApplyWithPositionIrrelavence(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

     (forall i : nat | i < 2 * m :: 0 <= q[i] < m && (f(q[i]) == 0 || f(q[i]) == 1)) &&
#     (forall i : nat | i < m :: 
#       q.GetPhases()[2*i] == (phaseSinglePow(phasem1(), f(q[2*i]))) && 
#       q.GetPhases()[2*i+1] == (phaseSinglePow(phasem1(), (1 + f(q[2*i])))))
#   }
# {
# }
# 
# 
# // if f(x) with x 
# // {
# //   y *= X;
# // }
# 
# method CrossMinus(n : nat, m : nat, q : qreg, p : qreg)
#   requires typeof (q) is exactly (n) $ ch(m) { 
#     forall i : nat | i < m :: unitPhase(q.GetPhases()[i])
#   }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phaseSingleProduct(phase1(), old(q.GetPhases()[i]))) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phaseSingleProduct(phasem1(), old(q.GetPhases()[i]))) && 
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] == old(q.GetSession()[q])
#   }
#   modifies q, p
# 
# method DeutschJozsaOracle(n : nat, p : qreg, q : qreg)
#   requires n > 0
#   requires typeof (q) is (n) $ had { forall i : nat | i < n :: q[i] == 1 }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   modifies q, p
# { 
#   q.PlusToCH();
#   var m := Pow2(n);
#   CrossMinus(n, m, q, p);
#   LemmaSmallMod(2, 4);
#   LemmaSmallMod(0, 4);
#   // This postcondition looks nice but the precondition in
#   // [ApplyWithPositionIrrelavance] is more useful because of [Parititon]  
#   assert typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phase1()) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phasem1()) &&
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m)
#   };
# }
# 
# // We need to bridge the position irrelavence property here 
# method ApplyWithPositionIrrelavence(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

     (forall i : nat | i < m :: 
#       q.GetPhases()[2*i] == (phaseSinglePow(phasem1(), f(q[2*i]))) && 
#       q.GetPhases()[2*i+1] == (phaseSinglePow(phasem1(), (1 + f(q[2*i])))))
#   }
# {
# }
# 
# 
# // if f(x) with x 
# // {
# //   y *= X;
# // }
# 
# method CrossMinus(n : nat, m : nat, q : qreg, p : qreg)
#   requires typeof (q) is exactly (n) $ ch(m) { 
#     forall i : nat | i < m :: unitPhase(q.GetPhases()[i])
#   }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phaseSingleProduct(phase1(), old(q.GetPhases()[i]))) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phaseSingleProduct(phasem1(), old(q.GetPhases()[i]))) && 
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] == old(q.GetSession()[q])
#   }
#   modifies q, p
# 
# method DeutschJozsaOracle(n : nat, p : qreg, q : qreg)
#   requires n > 0
#   requires typeof (q) is (n) $ had { forall i : nat | i < n :: q[i] == 1 }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   modifies q, p
# { 
#   q.PlusToCH();
#   var m := Pow2(n);
#   CrossMinus(n, m, q, p);
#   LemmaSmallMod(2, 4);
#   LemmaSmallMod(0, 4);
#   // This postcondition looks nice but the precondition in
#   // [ApplyWithPositionIrrelavance] is more useful because of [Parititon]  
#   assert typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phase1()) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phasem1()) &&
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m)
#   };
# }
# 
# // We need to bridge the position irrelavence property here 
# method ApplyWithPositionIrrelavence(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

       q.GetPhases()[2*i] == (phaseSinglePow(phasem1(), f(q[2*i]))) && 
#       q.GetPhases()[2*i+1] == (phaseSinglePow(phasem1(), (1 + f(q[2*i])))))
#   }
# {
# }
# 
# 
# // if f(x) with x 
# // {
# //   y *= X;
# // }
# 
# method CrossMinus(n : nat, m : nat, q : qreg, p : qreg)
#   requires typeof (q) is exactly (n) $ ch(m) { 
#     forall i : nat | i < m :: unitPhase(q.GetPhases()[i])
#   }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phaseSingleProduct(phase1(), old(q.GetPhases()[i]))) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phaseSingleProduct(phasem1(), old(q.GetPhases()[i]))) && 
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] == old(q.GetSession()[q])
#   }
#   modifies q, p
# 
# method DeutschJozsaOracle(n : nat, p : qreg, q : qreg)
#   requires n > 0
#   requires typeof (q) is (n) $ had { forall i : nat | i < n :: q[i] == 1 }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   modifies q, p
# { 
#   q.PlusToCH();
#   var m := Pow2(n);
#   CrossMinus(n, m, q, p);
#   LemmaSmallMod(2, 4);
#   LemmaSmallMod(0, 4);
#   // This postcondition looks nice but the precondition in
#   // [ApplyWithPositionIrrelavance] is more useful because of [Parititon]  
#   assert typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phase1()) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phasem1()) &&
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m)
#   };
# }
# 
# // We need to bridge the position irrelavence property here 
# method ApplyWithPositionIrrelavence(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

       q.GetPhases()[2*i+1] == (phaseSinglePow(phasem1(), (1 + f(q[2*i])))))
#   }
# {
# }
# 
# 
# // if f(x) with x 
# // {
# //   y *= X;
# // }
# 
# method CrossMinus(n : nat, m : nat, q : qreg, p : qreg)
#   requires typeof (q) is exactly (n) $ ch(m) { 
#     forall i : nat | i < m :: unitPhase(q.GetPhases()[i])
#   }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phaseSingleProduct(phase1(), old(q.GetPhases()[i]))) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phaseSingleProduct(phasem1(), old(q.GetPhases()[i]))) && 
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] == old(q.GetSession()[q])
#   }
#   modifies q, p
# 
# method DeutschJozsaOracle(n : nat, p : qreg, q : qreg)
#   requires n > 0
#   requires typeof (q) is (n) $ had { forall i : nat | i < n :: q[i] == 1 }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   modifies q, p
# { 
#   q.PlusToCH();
#   var m := Pow2(n);
#   CrossMinus(n, m, q, p);
#   LemmaSmallMod(2, 4);
#   LemmaSmallMod(0, 4);
#   // This postcondition looks nice but the precondition in
#   // [ApplyWithPositionIrrelavance] is more useful because of [Parititon]  
#   assert typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phase1()) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phasem1()) &&
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m)
#   };
# }
# 
# // We need to bridge the position irrelavence property here 
# method ApplyWithPositionIrrelavence(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

   }
# {
# }
# 
# 
# // if f(x) with x 
# // {
# //   y *= X;
# // }
# 
# method CrossMinus(n : nat, m : nat, q : qreg, p : qreg)
#   requires typeof (q) is exactly (n) $ ch(m) { 
#     forall i : nat | i < m :: unitPhase(q.GetPhases()[i])
#   }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phaseSingleProduct(phase1(), old(q.GetPhases()[i]))) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phaseSingleProduct(phasem1(), old(q.GetPhases()[i]))) && 
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] == old(q.GetSession()[q])
#   }
#   modifies q, p
# 
# method DeutschJozsaOracle(n : nat, p : qreg, q : qreg)
#   requires n > 0
#   requires typeof (q) is (n) $ had { forall i : nat | i < n :: q[i] == 1 }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   modifies q, p
# { 
#   q.PlusToCH();
#   var m := Pow2(n);
#   CrossMinus(n, m, q, p);
#   LemmaSmallMod(2, 4);
#   LemmaSmallMod(0, 4);
#   // This postcondition looks nice but the precondition in
#   // [ApplyWithPositionIrrelavance] is more useful because of [Parititon]  
#   assert typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phase1()) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phasem1()) &&
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m)
#   };
# }
# 
# // We need to bridge the position irrelavence property here 
# method ApplyWithPositionIrrelavence(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

 {
# }
# 
# 
# // if f(x) with x 
# // {
# //   y *= X;
# // }
# 
# method CrossMinus(n : nat, m : nat, q : qreg, p : qreg)
#   requires typeof (q) is exactly (n) $ ch(m) { 
#     forall i : nat | i < m :: unitPhase(q.GetPhases()[i])
#   }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phaseSingleProduct(phase1(), old(q.GetPhases()[i]))) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phaseSingleProduct(phasem1(), old(q.GetPhases()[i]))) && 
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] == old(q.GetSession()[q])
#   }
#   modifies q, p
# 
# method DeutschJozsaOracle(n : nat, p : qreg, q : qreg)
#   requires n > 0
#   requires typeof (q) is (n) $ had { forall i : nat | i < n :: q[i] == 1 }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   modifies q, p
# { 
#   q.PlusToCH();
#   var m := Pow2(n);
#   CrossMinus(n, m, q, p);
#   LemmaSmallMod(2, 4);
#   LemmaSmallMod(0, 4);
#   // This postcondition looks nice but the precondition in
#   // [ApplyWithPositionIrrelavance] is more useful because of [Parititon]  
#   assert typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phase1()) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phasem1()) &&
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m)
#   };
# }
# 
# // We need to bridge the position irrelavence property here 
# method ApplyWithPositionIrrelavence(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

 }
# 
# 
# // if f(x) with x 
# // {
# //   y *= X;
# // }
# 
# method CrossMinus(n : nat, m : nat, q : qreg, p : qreg)
#   requires typeof (q) is exactly (n) $ ch(m) { 
#     forall i : nat | i < m :: unitPhase(q.GetPhases()[i])
#   }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phaseSingleProduct(phase1(), old(q.GetPhases()[i]))) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phaseSingleProduct(phasem1(), old(q.GetPhases()[i]))) && 
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] == old(q.GetSession()[q])
#   }
#   modifies q, p
# 
# method DeutschJozsaOracle(n : nat, p : qreg, q : qreg)
#   requires n > 0
#   requires typeof (q) is (n) $ had { forall i : nat | i < n :: q[i] == 1 }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   modifies q, p
# { 
#   q.PlusToCH();
#   var m := Pow2(n);
#   CrossMinus(n, m, q, p);
#   LemmaSmallMod(2, 4);
#   LemmaSmallMod(0, 4);
#   // This postcondition looks nice but the precondition in
#   // [ApplyWithPositionIrrelavance] is more useful because of [Parititon]  
#   assert typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phase1()) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phasem1()) &&
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m)
#   };
# }
# 
# // We need to bridge the position irrelavence property here 
# method ApplyWithPositionIrrelavence(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

 
# 
# // if f(x) with x 
# // {
# //   y *= X;
# // }
# 
# method CrossMinus(n : nat, m : nat, q : qreg, p : qreg)
#   requires typeof (q) is exactly (n) $ ch(m) { 
#     forall i : nat | i < m :: unitPhase(q.GetPhases()[i])
#   }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phaseSingleProduct(phase1(), old(q.GetPhases()[i]))) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phaseSingleProduct(phasem1(), old(q.GetPhases()[i]))) && 
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] == old(q.GetSession()[q])
#   }
#   modifies q, p
# 
# method DeutschJozsaOracle(n : nat, p : qreg, q : qreg)
#   requires n > 0
#   requires typeof (q) is (n) $ had { forall i : nat | i < n :: q[i] == 1 }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   modifies q, p
# { 
#   q.PlusToCH();
#   var m := Pow2(n);
#   CrossMinus(n, m, q, p);
#   LemmaSmallMod(2, 4);
#   LemmaSmallMod(0, 4);
#   // This postcondition looks nice but the precondition in
#   // [ApplyWithPositionIrrelavance] is more useful because of [Parititon]  
#   assert typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phase1()) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phasem1()) &&
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m)
#   };
# }
# 
# // We need to bridge the position irrelavence property here 
# method ApplyWithPositionIrrelavence(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

 
# // if f(x) with x 
# // {
# //   y *= X;
# // }
# 
# method CrossMinus(n : nat, m : nat, q : qreg, p : qreg)
#   requires typeof (q) is exactly (n) $ ch(m) { 
#     forall i : nat | i < m :: unitPhase(q.GetPhases()[i])
#   }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phaseSingleProduct(phase1(), old(q.GetPhases()[i]))) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phaseSingleProduct(phasem1(), old(q.GetPhases()[i]))) && 
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] == old(q.GetSession()[q])
#   }
#   modifies q, p
# 
# method DeutschJozsaOracle(n : nat, p : qreg, q : qreg)
#   requires n > 0
#   requires typeof (q) is (n) $ had { forall i : nat | i < n :: q[i] == 1 }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   modifies q, p
# { 
#   q.PlusToCH();
#   var m := Pow2(n);
#   CrossMinus(n, m, q, p);
#   LemmaSmallMod(2, 4);
#   LemmaSmallMod(0, 4);
#   // This postcondition looks nice but the precondition in
#   // [ApplyWithPositionIrrelavance] is more useful because of [Parititon]  
#   assert typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phase1()) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phasem1()) &&
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m)
#   };
# }
# 
# // We need to bridge the position irrelavence property here 
# method ApplyWithPositionIrrelavence(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

 // if f(x) with x 
# // {
# //   y *= X;
# // }
# 
# method CrossMinus(n : nat, m : nat, q : qreg, p : qreg)
#   requires typeof (q) is exactly (n) $ ch(m) { 
#     forall i : nat | i < m :: unitPhase(q.GetPhases()[i])
#   }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phaseSingleProduct(phase1(), old(q.GetPhases()[i]))) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phaseSingleProduct(phasem1(), old(q.GetPhases()[i]))) && 
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] == old(q.GetSession()[q])
#   }
#   modifies q, p
# 
# method DeutschJozsaOracle(n : nat, p : qreg, q : qreg)
#   requires n > 0
#   requires typeof (q) is (n) $ had { forall i : nat | i < n :: q[i] == 1 }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   modifies q, p
# { 
#   q.PlusToCH();
#   var m := Pow2(n);
#   CrossMinus(n, m, q, p);
#   LemmaSmallMod(2, 4);
#   LemmaSmallMod(0, 4);
#   // This postcondition looks nice but the precondition in
#   // [ApplyWithPositionIrrelavance] is more useful because of [Parititon]  
#   assert typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phase1()) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phasem1()) &&
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m)
#   };
# }
# 
# // We need to bridge the position irrelavence property here 
# method ApplyWithPositionIrrelavence(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

 // {
# //   y *= X;
# // }
# 
# method CrossMinus(n : nat, m : nat, q : qreg, p : qreg)
#   requires typeof (q) is exactly (n) $ ch(m) { 
#     forall i : nat | i < m :: unitPhase(q.GetPhases()[i])
#   }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phaseSingleProduct(phase1(), old(q.GetPhases()[i]))) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phaseSingleProduct(phasem1(), old(q.GetPhases()[i]))) && 
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] == old(q.GetSession()[q])
#   }
#   modifies q, p
# 
# method DeutschJozsaOracle(n : nat, p : qreg, q : qreg)
#   requires n > 0
#   requires typeof (q) is (n) $ had { forall i : nat | i < n :: q[i] == 1 }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   modifies q, p
# { 
#   q.PlusToCH();
#   var m := Pow2(n);
#   CrossMinus(n, m, q, p);
#   LemmaSmallMod(2, 4);
#   LemmaSmallMod(0, 4);
#   // This postcondition looks nice but the precondition in
#   // [ApplyWithPositionIrrelavance] is more useful because of [Parititon]  
#   assert typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phase1()) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phasem1()) &&
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m)
#   };
# }
# 
# // We need to bridge the position irrelavence property here 
# method ApplyWithPositionIrrelavence(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

 //   y *= X;
# // }
# 
# method CrossMinus(n : nat, m : nat, q : qreg, p : qreg)
#   requires typeof (q) is exactly (n) $ ch(m) { 
#     forall i : nat | i < m :: unitPhase(q.GetPhases()[i])
#   }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phaseSingleProduct(phase1(), old(q.GetPhases()[i]))) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phaseSingleProduct(phasem1(), old(q.GetPhases()[i]))) && 
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] == old(q.GetSession()[q])
#   }
#   modifies q, p
# 
# method DeutschJozsaOracle(n : nat, p : qreg, q : qreg)
#   requires n > 0
#   requires typeof (q) is (n) $ had { forall i : nat | i < n :: q[i] == 1 }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   modifies q, p
# { 
#   q.PlusToCH();
#   var m := Pow2(n);
#   CrossMinus(n, m, q, p);
#   LemmaSmallMod(2, 4);
#   LemmaSmallMod(0, 4);
#   // This postcondition looks nice but the precondition in
#   // [ApplyWithPositionIrrelavance] is more useful because of [Parititon]  
#   assert typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phase1()) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phasem1()) &&
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m)
#   };
# }
# 
# // We need to bridge the position irrelavence property here 
# method ApplyWithPositionIrrelavence(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

 // }
# 
# method CrossMinus(n : nat, m : nat, q : qreg, p : qreg)
#   requires typeof (q) is exactly (n) $ ch(m) { 
#     forall i : nat | i < m :: unitPhase(q.GetPhases()[i])
#   }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phaseSingleProduct(phase1(), old(q.GetPhases()[i]))) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phaseSingleProduct(phasem1(), old(q.GetPhases()[i]))) && 
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] == old(q.GetSession()[q])
#   }
#   modifies q, p
# 
# method DeutschJozsaOracle(n : nat, p : qreg, q : qreg)
#   requires n > 0
#   requires typeof (q) is (n) $ had { forall i : nat | i < n :: q[i] == 1 }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   modifies q, p
# { 
#   q.PlusToCH();
#   var m := Pow2(n);
#   CrossMinus(n, m, q, p);
#   LemmaSmallMod(2, 4);
#   LemmaSmallMod(0, 4);
#   // This postcondition looks nice but the precondition in
#   // [ApplyWithPositionIrrelavance] is more useful because of [Parititon]  
#   assert typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phase1()) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phasem1()) &&
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m)
#   };
# }
# 
# // We need to bridge the position irrelavence property here 
# method ApplyWithPositionIrrelavence(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

 
# method CrossMinus(n : nat, m : nat, q : qreg, p : qreg)
#   requires typeof (q) is exactly (n) $ ch(m) { 
#     forall i : nat | i < m :: unitPhase(q.GetPhases()[i])
#   }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phaseSingleProduct(phase1(), old(q.GetPhases()[i]))) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phaseSingleProduct(phasem1(), old(q.GetPhases()[i]))) && 
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] == old(q.GetSession()[q])
#   }
#   modifies q, p
# 
# method DeutschJozsaOracle(n : nat, p : qreg, q : qreg)
#   requires n > 0
#   requires typeof (q) is (n) $ had { forall i : nat | i < n :: q[i] == 1 }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   modifies q, p
# { 
#   q.PlusToCH();
#   var m := Pow2(n);
#   CrossMinus(n, m, q, p);
#   LemmaSmallMod(2, 4);
#   LemmaSmallMod(0, 4);
#   // This postcondition looks nice but the precondition in
#   // [ApplyWithPositionIrrelavance] is more useful because of [Parititon]  
#   assert typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phase1()) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phasem1()) &&
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m)
#   };
# }
# 
# // We need to bridge the position irrelavence property here 
# method ApplyWithPositionIrrelavence(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

 method CrossMinus(n : nat, m : nat, q : qreg, p : qreg)
#   requires typeof (q) is exactly (n) $ ch(m) { 
#     forall i : nat | i < m :: unitPhase(q.GetPhases()[i])
#   }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phaseSingleProduct(phase1(), old(q.GetPhases()[i]))) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phaseSingleProduct(phasem1(), old(q.GetPhases()[i]))) && 
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] == old(q.GetSession()[q])
#   }
#   modifies q, p
# 
# method DeutschJozsaOracle(n : nat, p : qreg, q : qreg)
#   requires n > 0
#   requires typeof (q) is (n) $ had { forall i : nat | i < n :: q[i] == 1 }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   modifies q, p
# { 
#   q.PlusToCH();
#   var m := Pow2(n);
#   CrossMinus(n, m, q, p);
#   LemmaSmallMod(2, 4);
#   LemmaSmallMod(0, 4);
#   // This postcondition looks nice but the precondition in
#   // [ApplyWithPositionIrrelavance] is more useful because of [Parititon]  
#   assert typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phase1()) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phasem1()) &&
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m)
#   };
# }
# 
# // We need to bridge the position irrelavence property here 
# method ApplyWithPositionIrrelavence(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

   requires typeof (q) is exactly (n) $ ch(m) { 
#     forall i : nat | i < m :: unitPhase(q.GetPhases()[i])
#   }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phaseSingleProduct(phase1(), old(q.GetPhases()[i]))) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phaseSingleProduct(phasem1(), old(q.GetPhases()[i]))) && 
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] == old(q.GetSession()[q])
#   }
#   modifies q, p
# 
# method DeutschJozsaOracle(n : nat, p : qreg, q : qreg)
#   requires n > 0
#   requires typeof (q) is (n) $ had { forall i : nat | i < n :: q[i] == 1 }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   modifies q, p
# { 
#   q.PlusToCH();
#   var m := Pow2(n);
#   CrossMinus(n, m, q, p);
#   LemmaSmallMod(2, 4);
#   LemmaSmallMod(0, 4);
#   // This postcondition looks nice but the precondition in
#   // [ApplyWithPositionIrrelavance] is more useful because of [Parititon]  
#   assert typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phase1()) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phasem1()) &&
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m)
#   };
# }
# 
# // We need to bridge the position irrelavence property here 
# method ApplyWithPositionIrrelavence(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

     forall i : nat | i < m :: unitPhase(q.GetPhases()[i])
#   }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phaseSingleProduct(phase1(), old(q.GetPhases()[i]))) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phaseSingleProduct(phasem1(), old(q.GetPhases()[i]))) && 
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] == old(q.GetSession()[q])
#   }
#   modifies q, p
# 
# method DeutschJozsaOracle(n : nat, p : qreg, q : qreg)
#   requires n > 0
#   requires typeof (q) is (n) $ had { forall i : nat | i < n :: q[i] == 1 }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   modifies q, p
# { 
#   q.PlusToCH();
#   var m := Pow2(n);
#   CrossMinus(n, m, q, p);
#   LemmaSmallMod(2, 4);
#   LemmaSmallMod(0, 4);
#   // This postcondition looks nice but the precondition in
#   // [ApplyWithPositionIrrelavance] is more useful because of [Parititon]  
#   assert typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phase1()) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phasem1()) &&
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m)
#   };
# }
# 
# // We need to bridge the position irrelavence property here 
# method ApplyWithPositionIrrelavence(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

   }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phaseSingleProduct(phase1(), old(q.GetPhases()[i]))) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phaseSingleProduct(phasem1(), old(q.GetPhases()[i]))) && 
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] == old(q.GetSession()[q])
#   }
#   modifies q, p
# 
# method DeutschJozsaOracle(n : nat, p : qreg, q : qreg)
#   requires n > 0
#   requires typeof (q) is (n) $ had { forall i : nat | i < n :: q[i] == 1 }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   modifies q, p
# { 
#   q.PlusToCH();
#   var m := Pow2(n);
#   CrossMinus(n, m, q, p);
#   LemmaSmallMod(2, 4);
#   LemmaSmallMod(0, 4);
#   // This postcondition looks nice but the precondition in
#   // [ApplyWithPositionIrrelavance] is more useful because of [Parititon]  
#   assert typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phase1()) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phasem1()) &&
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m)
#   };
# }
# 
# // We need to bridge the position irrelavence property here 
# method ApplyWithPositionIrrelavence(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

   requires typeof (p) is (1) $ had { p[0] == -1 }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phaseSingleProduct(phase1(), old(q.GetPhases()[i]))) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phaseSingleProduct(phasem1(), old(q.GetPhases()[i]))) && 
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] == old(q.GetSession()[q])
#   }
#   modifies q, p
# 
# method DeutschJozsaOracle(n : nat, p : qreg, q : qreg)
#   requires n > 0
#   requires typeof (q) is (n) $ had { forall i : nat | i < n :: q[i] == 1 }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   modifies q, p
# { 
#   q.PlusToCH();
#   var m := Pow2(n);
#   CrossMinus(n, m, q, p);
#   LemmaSmallMod(2, 4);
#   LemmaSmallMod(0, 4);
#   // This postcondition looks nice but the precondition in
#   // [ApplyWithPositionIrrelavance] is more useful because of [Parititon]  
#   assert typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phase1()) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phasem1()) &&
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m)
#   };
# }
# 
# // We need to bridge the position irrelavence property here 
# method ApplyWithPositionIrrelavence(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phaseSingleProduct(phase1(), old(q.GetPhases()[i]))) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phaseSingleProduct(phasem1(), old(q.GetPhases()[i]))) && 
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] == old(q.GetSession()[q])
#   }
#   modifies q, p
# 
# method DeutschJozsaOracle(n : nat, p : qreg, q : qreg)
#   requires n > 0
#   requires typeof (q) is (n) $ had { forall i : nat | i < n :: q[i] == 1 }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   modifies q, p
# { 
#   q.PlusToCH();
#   var m := Pow2(n);
#   CrossMinus(n, m, q, p);
#   LemmaSmallMod(2, 4);
#   LemmaSmallMod(0, 4);
#   // This postcondition looks nice but the precondition in
#   // [ApplyWithPositionIrrelavance] is more useful because of [Parititon]  
#   assert typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phase1()) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phasem1()) &&
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m)
#   };
# }
# 
# // We need to bridge the position irrelavence property here 
# method ApplyWithPositionIrrelavence(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phaseSingleProduct(phase1(), old(q.GetPhases()[i]))) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phaseSingleProduct(phasem1(), old(q.GetPhases()[i]))) && 
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] == old(q.GetSession()[q])
#   }
#   modifies q, p
# 
# method DeutschJozsaOracle(n : nat, p : qreg, q : qreg)
#   requires n > 0
#   requires typeof (q) is (n) $ had { forall i : nat | i < n :: q[i] == 1 }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   modifies q, p
# { 
#   q.PlusToCH();
#   var m := Pow2(n);
#   CrossMinus(n, m, q, p);
#   LemmaSmallMod(2, 4);
#   LemmaSmallMod(0, 4);
#   // This postcondition looks nice but the precondition in
#   // [ApplyWithPositionIrrelavance] is more useful because of [Parititon]  
#   assert typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phase1()) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phasem1()) &&
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m)
#   };
# }
# 
# // We need to bridge the position irrelavence property here 
# method ApplyWithPositionIrrelavence(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phaseSingleProduct(phase1(), old(q.GetPhases()[i]))) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phaseSingleProduct(phasem1(), old(q.GetPhases()[i]))) && 
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] == old(q.GetSession()[q])
#   }
#   modifies q, p
# 
# method DeutschJozsaOracle(n : nat, p : qreg, q : qreg)
#   requires n > 0
#   requires typeof (q) is (n) $ had { forall i : nat | i < n :: q[i] == 1 }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   modifies q, p
# { 
#   q.PlusToCH();
#   var m := Pow2(n);
#   CrossMinus(n, m, q, p);
#   LemmaSmallMod(2, 4);
#   LemmaSmallMod(0, 4);
#   // This postcondition looks nice but the precondition in
#   // [ApplyWithPositionIrrelavance] is more useful because of [Parititon]  
#   assert typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phase1()) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phasem1()) &&
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m)
#   };
# }
# 
# // We need to bridge the position irrelavence property here 
# method ApplyWithPositionIrrelavence(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

     (forall i : nat | i < m :: q.GetPhases()[i] == phaseSingleProduct(phase1(), old(q.GetPhases()[i]))) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phaseSingleProduct(phasem1(), old(q.GetPhases()[i]))) && 
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] == old(q.GetSession()[q])
#   }
#   modifies q, p
# 
# method DeutschJozsaOracle(n : nat, p : qreg, q : qreg)
#   requires n > 0
#   requires typeof (q) is (n) $ had { forall i : nat | i < n :: q[i] == 1 }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   modifies q, p
# { 
#   q.PlusToCH();
#   var m := Pow2(n);
#   CrossMinus(n, m, q, p);
#   LemmaSmallMod(2, 4);
#   LemmaSmallMod(0, 4);
#   // This postcondition looks nice but the precondition in
#   // [ApplyWithPositionIrrelavance] is more useful because of [Parititon]  
#   assert typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phase1()) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phasem1()) &&
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m)
#   };
# }
# 
# // We need to bridge the position irrelavence property here 
# method ApplyWithPositionIrrelavence(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

     (forall i : nat | i < m :: q.GetPhases()[m + i] == phaseSingleProduct(phasem1(), old(q.GetPhases()[i]))) && 
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] == old(q.GetSession()[q])
#   }
#   modifies q, p
# 
# method DeutschJozsaOracle(n : nat, p : qreg, q : qreg)
#   requires n > 0
#   requires typeof (q) is (n) $ had { forall i : nat | i < n :: q[i] == 1 }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   modifies q, p
# { 
#   q.PlusToCH();
#   var m := Pow2(n);
#   CrossMinus(n, m, q, p);
#   LemmaSmallMod(2, 4);
#   LemmaSmallMod(0, 4);
#   // This postcondition looks nice but the precondition in
#   // [ApplyWithPositionIrrelavance] is more useful because of [Parititon]  
#   assert typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phase1()) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phasem1()) &&
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m)
#   };
# }
# 
# // We need to bridge the position irrelavence property here 
# method ApplyWithPositionIrrelavence(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] == old(q.GetSession()[q])
#   }
#   modifies q, p
# 
# method DeutschJozsaOracle(n : nat, p : qreg, q : qreg)
#   requires n > 0
#   requires typeof (q) is (n) $ had { forall i : nat | i < n :: q[i] == 1 }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   modifies q, p
# { 
#   q.PlusToCH();
#   var m := Pow2(n);
#   CrossMinus(n, m, q, p);
#   LemmaSmallMod(2, 4);
#   LemmaSmallMod(0, 4);
#   // This postcondition looks nice but the precondition in
#   // [ApplyWithPositionIrrelavance] is more useful because of [Parititon]  
#   assert typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phase1()) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phasem1()) &&
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m)
#   };
# }
# 
# // We need to bridge the position irrelavence property here 
# method ApplyWithPositionIrrelavence(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

   }
#   modifies q, p
# 
# method DeutschJozsaOracle(n : nat, p : qreg, q : qreg)
#   requires n > 0
#   requires typeof (q) is (n) $ had { forall i : nat | i < n :: q[i] == 1 }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   modifies q, p
# { 
#   q.PlusToCH();
#   var m := Pow2(n);
#   CrossMinus(n, m, q, p);
#   LemmaSmallMod(2, 4);
#   LemmaSmallMod(0, 4);
#   // This postcondition looks nice but the precondition in
#   // [ApplyWithPositionIrrelavance] is more useful because of [Parititon]  
#   assert typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phase1()) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phasem1()) &&
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m)
#   };
# }
# 
# // We need to bridge the position irrelavence property here 
# method ApplyWithPositionIrrelavence(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

   modifies q, p
# 
# method DeutschJozsaOracle(n : nat, p : qreg, q : qreg)
#   requires n > 0
#   requires typeof (q) is (n) $ had { forall i : nat | i < n :: q[i] == 1 }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   modifies q, p
# { 
#   q.PlusToCH();
#   var m := Pow2(n);
#   CrossMinus(n, m, q, p);
#   LemmaSmallMod(2, 4);
#   LemmaSmallMod(0, 4);
#   // This postcondition looks nice but the precondition in
#   // [ApplyWithPositionIrrelavance] is more useful because of [Parititon]  
#   assert typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phase1()) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phasem1()) &&
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m)
#   };
# }
# 
# // We need to bridge the position irrelavence property here 
# method ApplyWithPositionIrrelavence(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

 
# method DeutschJozsaOracle(n : nat, p : qreg, q : qreg)
#   requires n > 0
#   requires typeof (q) is (n) $ had { forall i : nat | i < n :: q[i] == 1 }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   modifies q, p
# { 
#   q.PlusToCH();
#   var m := Pow2(n);
#   CrossMinus(n, m, q, p);
#   LemmaSmallMod(2, 4);
#   LemmaSmallMod(0, 4);
#   // This postcondition looks nice but the precondition in
#   // [ApplyWithPositionIrrelavance] is more useful because of [Parititon]  
#   assert typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phase1()) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phasem1()) &&
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m)
#   };
# }
# 
# // We need to bridge the position irrelavence property here 
# method ApplyWithPositionIrrelavence(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

 method DeutschJozsaOracle(n : nat, p : qreg, q : qreg)
#   requires n > 0
#   requires typeof (q) is (n) $ had { forall i : nat | i < n :: q[i] == 1 }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   modifies q, p
# { 
#   q.PlusToCH();
#   var m := Pow2(n);
#   CrossMinus(n, m, q, p);
#   LemmaSmallMod(2, 4);
#   LemmaSmallMod(0, 4);
#   // This postcondition looks nice but the precondition in
#   // [ApplyWithPositionIrrelavance] is more useful because of [Parititon]  
#   assert typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phase1()) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phasem1()) &&
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m)
#   };
# }
# 
# // We need to bridge the position irrelavence property here 
# method ApplyWithPositionIrrelavence(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

   requires n > 0
#   requires typeof (q) is (n) $ had { forall i : nat | i < n :: q[i] == 1 }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   modifies q, p
# { 
#   q.PlusToCH();
#   var m := Pow2(n);
#   CrossMinus(n, m, q, p);
#   LemmaSmallMod(2, 4);
#   LemmaSmallMod(0, 4);
#   // This postcondition looks nice but the precondition in
#   // [ApplyWithPositionIrrelavance] is more useful because of [Parititon]  
#   assert typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phase1()) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phasem1()) &&
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m)
#   };
# }
# 
# // We need to bridge the position irrelavence property here 
# method ApplyWithPositionIrrelavence(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

   requires typeof (q) is (n) $ had { forall i : nat | i < n :: q[i] == 1 }
#   requires typeof (p) is (1) $ had { p[0] == -1 }
#   modifies q, p
# { 
#   q.PlusToCH();
#   var m := Pow2(n);
#   CrossMinus(n, m, q, p);
#   LemmaSmallMod(2, 4);
#   LemmaSmallMod(0, 4);
#   // This postcondition looks nice but the precondition in
#   // [ApplyWithPositionIrrelavance] is more useful because of [Parititon]  
#   assert typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phase1()) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phasem1()) &&
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m)
#   };
# }
# 
# // We need to bridge the position irrelavence property here 
# method ApplyWithPositionIrrelavence(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

   requires typeof (p) is (1) $ had { p[0] == -1 }
#   modifies q, p
# { 
#   q.PlusToCH();
#   var m := Pow2(n);
#   CrossMinus(n, m, q, p);
#   LemmaSmallMod(2, 4);
#   LemmaSmallMod(0, 4);
#   // This postcondition looks nice but the precondition in
#   // [ApplyWithPositionIrrelavance] is more useful because of [Parititon]  
#   assert typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phase1()) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phasem1()) &&
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m)
#   };
# }
# 
# // We need to bridge the position irrelavence property here 
# method ApplyWithPositionIrrelavence(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

   modifies q, p
# { 
#   q.PlusToCH();
#   var m := Pow2(n);
#   CrossMinus(n, m, q, p);
#   LemmaSmallMod(2, 4);
#   LemmaSmallMod(0, 4);
#   // This postcondition looks nice but the precondition in
#   // [ApplyWithPositionIrrelavance] is more useful because of [Parititon]  
#   assert typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phase1()) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phasem1()) &&
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m)
#   };
# }
# 
# // We need to bridge the position irrelavence property here 
# method ApplyWithPositionIrrelavence(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

 { 
#   q.PlusToCH();
#   var m := Pow2(n);
#   CrossMinus(n, m, q, p);
#   LemmaSmallMod(2, 4);
#   LemmaSmallMod(0, 4);
#   // This postcondition looks nice but the precondition in
#   // [ApplyWithPositionIrrelavance] is more useful because of [Parititon]  
#   assert typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phase1()) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phasem1()) &&
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m)
#   };
# }
# 
# // We need to bridge the position irrelavence property here 
# method ApplyWithPositionIrrelavence(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

   q.PlusToCH();
#   var m := Pow2(n);
#   CrossMinus(n, m, q, p);
#   LemmaSmallMod(2, 4);
#   LemmaSmallMod(0, 4);
#   // This postcondition looks nice but the precondition in
#   // [ApplyWithPositionIrrelavance] is more useful because of [Parititon]  
#   assert typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phase1()) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phasem1()) &&
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m)
#   };
# }
# 
# // We need to bridge the position irrelavence property here 
# method ApplyWithPositionIrrelavence(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

   var m := Pow2(n);
#   CrossMinus(n, m, q, p);
#   LemmaSmallMod(2, 4);
#   LemmaSmallMod(0, 4);
#   // This postcondition looks nice but the precondition in
#   // [ApplyWithPositionIrrelavance] is more useful because of [Parititon]  
#   assert typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phase1()) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phasem1()) &&
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m)
#   };
# }
# 
# // We need to bridge the position irrelavence property here 
# method ApplyWithPositionIrrelavence(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

   CrossMinus(n, m, q, p);
#   LemmaSmallMod(2, 4);
#   LemmaSmallMod(0, 4);
#   // This postcondition looks nice but the precondition in
#   // [ApplyWithPositionIrrelavance] is more useful because of [Parititon]  
#   assert typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phase1()) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phasem1()) &&
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m)
#   };
# }
# 
# // We need to bridge the position irrelavence property here 
# method ApplyWithPositionIrrelavence(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

   LemmaSmallMod(2, 4);
#   LemmaSmallMod(0, 4);
#   // This postcondition looks nice but the precondition in
#   // [ApplyWithPositionIrrelavance] is more useful because of [Parititon]  
#   assert typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phase1()) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phasem1()) &&
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m)
#   };
# }
# 
# // We need to bridge the position irrelavence property here 
# method ApplyWithPositionIrrelavence(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

   LemmaSmallMod(0, 4);
#   // This postcondition looks nice but the precondition in
#   // [ApplyWithPositionIrrelavance] is more useful because of [Parititon]  
#   assert typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phase1()) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phasem1()) &&
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m)
#   };
# }
# 
# // We need to bridge the position irrelavence property here 
# method ApplyWithPositionIrrelavence(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

   // This postcondition looks nice but the precondition in
#   // [ApplyWithPositionIrrelavance] is more useful because of [Parititon]  
#   assert typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phase1()) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phasem1()) &&
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m)
#   };
# }
# 
# // We need to bridge the position irrelavence property here 
# method ApplyWithPositionIrrelavence(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

   // [ApplyWithPositionIrrelavance] is more useful because of [Parititon]  
#   assert typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phase1()) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phasem1()) &&
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m)
#   };
# }
# 
# // We need to bridge the position irrelavence property here 
# method ApplyWithPositionIrrelavence(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

   assert typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phase1()) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phasem1()) &&
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m)
#   };
# }
# 
# // We need to bridge the position irrelavence property here 
# method ApplyWithPositionIrrelavence(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

     (forall i : nat | i < m :: p[i] == 0) && 
#     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phase1()) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phasem1()) &&
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m)
#   };
# }
# 
# // We need to bridge the position irrelavence property here 
# method ApplyWithPositionIrrelavence(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

     (forall i : nat | m <= i < 2 * m :: p[i] == 1) &&
#     (forall i : nat | i < m :: q.GetPhases()[i] == phase1()) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phasem1()) &&
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m)
#   };
# }
# 
# // We need to bridge the position irrelavence property here 
# method ApplyWithPositionIrrelavence(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

     (forall i : nat | i < m :: q.GetPhases()[i] == phase1()) &&
#     (forall i : nat | i < m :: q.GetPhases()[m + i] == phasem1()) &&
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m)
#   };
# }
# 
# // We need to bridge the position irrelavence property here 
# method ApplyWithPositionIrrelavence(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

     (forall i : nat | i < m :: q.GetPhases()[m + i] == phasem1()) &&
#     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m)
#   };
# }
# 
# // We need to bridge the position irrelavence property here 
# method ApplyWithPositionIrrelavence(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

     q.GetSession()[q][0..m] == q.GetSession()[q][m..2 * m] &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m)
#   };
# }
# 
# // We need to bridge the position irrelavence property here 
# method ApplyWithPositionIrrelavence(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

     (forall i : nat | i < 2 * m :: 0 <= q[i] < m)
#   };
# }
# 
# // We need to bridge the position irrelavence property here 
# method ApplyWithPositionIrrelavence(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

   };
# }
# 
# // We need to bridge the position irrelavence property here 
# method ApplyWithPositionIrrelavence(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

 }
# 
# // We need to bridge the position irrelavence property here 
# method ApplyWithPositionIrrelavence(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

 
# // We need to bridge the position irrelavence property here 
# method ApplyWithPositionIrrelavence(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

 // We need to bridge the position irrelavence property here 
# method ApplyWithPositionIrrelavence(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

 method ApplyWithPositionIrrelavence(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

   requires m == Pow2(n)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

     // Note the following, this is needed for [PartitionLeftSuchThat]
#     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

     exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

     )
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

     (forall i : nat | i < m :: q.GetSession()[q][2*i] == q.GetSession()[q][2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

     (forall i : nat | i < 2 * m :: 0 <= q[i] < m) &&
#     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

     // Note the following, this is needed for [PartitionLeftSuchThat]
#     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

     (exists g : nat | g < m :: (
#       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

       (forall i : nat | i < 2 * g :: f(q[i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

       (forall i : nat | 2 * g <= i < 2 * m :: f(q[i]) == 1)
#       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

       )) &&
#     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

     (forall i : nat | i < m :: 
#       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

       (f(q[2*i]) == 0 &&
#         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

         q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) ||
#       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

       (f(q[2*i]) == 1 &&
#         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

         q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()))
#   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

   }
#   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

   modifies p, q
# {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

 {
#   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

   var g : nat :| (
#       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

       g < m &&
#       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

       (forall i : nat | i < 2 * g :: f(q.GetSession()[q][i]) == 0) && 
#       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

       (forall i : nat | 2 * g <= i < 2 * m :: f(q.GetSession()[q][i]) == 1)
#     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

     );
# 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

 
#   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

   // This is necessary
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1());
# 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

 
#   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

   ghost var k := q.GetSession();
#   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

   ghost var ph := q.GetPhases();
# 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

 
#   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

   // the following one is needed??
#   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

   assert q.GetSession() == p.GetSession();
#   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

   // if f(x) with x 
#   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

   var stashedEq0 := q.PartitionLeftSuchThat(2*g, 1, f);
# 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

 
#   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

   // The following 2 is necesary!!
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

   assert (forall l | l in {p, q} :: 
#     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

     forall i : nat | i < (m - g) ::
#     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

     p.GetSession()[l][2*i] == k[l][2*(i+g)] && p.GetSession()[l][2*i+1] == k[l][2*(i+g)+1]);
#   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

   assert (forall i : nat | i < (m - g) ::
#     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

     p.GetPhases()[2*i] == ph[2*(i+g)] && p.GetPhases()[2*i+1] == ph[2*(i+g)+1]);
# 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

 
#   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

   ApplyWithPositionIrrelavenceInner(p, q, n, m - g, f);
# 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

 
# 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

 
#   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

   // interesting, i must set [k] to [p.GetSession()] or propose a hint with
#   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

   // [q.GetSession() == p.GetSession()] to get it work...
#   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

   // assert q.GetSession() == p.GetSession();
#   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

   k := p.GetSession();
# 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

 
#   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

   q.MergeLeft(stashedEq0);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

   assert (forall l | l in {p, q} :: 
#     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

     forall i : nat | g <= i < m ::
#     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

     p.GetSession()[l][2*i] == k[l][2*(i-g)] && p.GetSession()[l][2*i+1] == k[l][2*(i-g)+1]);
#   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

   assert (forall l | l in {p, q} :: 
#     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

     forall i : nat | 0 <= i < g ::
#     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

     p.GetSession()[l][2*i] == stashedEq0.c.1[l][2*i] && p.GetSession()[l][2*i+1] == stashedEq0.c.1[l][2*i+1]);
# 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

 
# }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

 }
# 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

 
# method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

 method ApplyWithPositionIrrelavenceInner(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

   requires m > 0;
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

     (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

     (forall i : nat | i < m :: p[2*i] == 0 && p[2*i+1] == 1) && 
#     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

     (forall i : nat | i < m :: q.GetPhases()[2*i] == phasem1() && q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

     (forall i : nat | i < m :: q[2*i] == q[2*i+1]) &&
#     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

     (forall i : nat | i < 2 * m :: 0 <= q[i] < Pow2(n)) &&
#     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

     (forall i : nat | i < 2 * m :: f(q[i]) == 1)
#   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

   }
#   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

   modifies p, q
# {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

 {
#   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

   // oh! i need to keep this [k] as an anchor? it seems that `old` frames are
#   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

   // somehow oblivious? Interesting!
#   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

   ghost var k := q.GetSession()[q];
# 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

 
#   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

   p *= cl(x => (x + 1) % 2);
# 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

 
#   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

   // the following two are needed; why?????
#   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

   assert (forall i : nat | i < m :: q.GetPhases()[2*i] == phase1() && q.GetPhases()[2*i+1] == phasem1()) by {
#     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

     assert p.GetPhases() == old(p.GetPhases());
#     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

     assert q.GetPhases() == old(q.GetPhases());
#   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

   }
# 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

 
#   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

   Alternate(p, q, n, m, f);
# }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

 }
# 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

 
# 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

 
# // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

 // Permutation method
# method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

 method Alternate(p : qreg, q : qreg, n : nat, m : nat, f : nat --> nat)
#   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

   requires forall i | 0 <= i < Pow2(n) :: f.requires(i)
#   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

   requires typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

     (forall i : nat | i < m :: 
#       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

       p[2*i] == 1 &&
#       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

       p[2*i+1] == 0 &&
#       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

       q.GetPhases()[2*i] == phase1() &&
#       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

       q.GetPhases()[2*i+1] == phasem1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

       f(p.GetSession()[q][i]) == 1)
#   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

   }
#   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

   ensures typeof (q, p) is exactly (n, 1) $ ch (2 * m) {
#     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

     (forall i : nat | i < m :: 
#       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

       p[2*i] == 0 && p[2*i+1] == 1 &&
#       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

       q[2*i] == old(q[2*i+1]) && 
#       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

       q[2*i+1] == old(q[2*i]) && 
#       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

       q.GetPhases()[2*i] == phasem1() &&
#       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

       q.GetPhases()[2*i+1] == phase1()) &&
#     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

     (forall i : nat | i < 2 * m :: 
#       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

       0 <= p.GetSession()[q][i] < Pow2(n) &&
#       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

       f(q.GetSession()[q][i]) == 1)
#   }
#   modifies p, q
# ;
# 
# 

   }
#   modifies p, q
# ;
# 
# 

   modifies p, q
# ;
# 
# 

 ;
# 
# 

 
# 

 
