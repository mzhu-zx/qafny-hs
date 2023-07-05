import opened QPrelude
import opened B2N
import opened Power2  
import opened Power
import opened DivMod

// Preparation
// method Shor0(a : nat, N : nat, n : nat) returns (x : qreg, y : qreg)
//   requires N >= 2 && n >= 2
//   ensures typeof(x) is (n) $ nor { forall i | 0 <= i < n :: x[i] == 0 }
//   ensures typeof(y) is (n) $ nor { forall i | 0 <= i < n :: y[i] == 0 }
// {
//   x := nor(n, _ => 0);
//   y := nor(n, _ => 0);
// }

// Preparation + Setup
// method Shor1_(a : nat, N : nat, n : nat) returns (x : qreg, y : qreg)
//   requires N >= 2
//   ensures typeof(x) is (n) $ had { forall i | 0 <= i < n :: x[i] == 1 }
//   ensures typeof(y) is exactly (n) $ ch(1) { y[0] == 1 }
//   ensures fresh(x) && fresh(y)
// {
//   x := nor(n, _ => 0);
//   y := nor(n, _ => 0);
//   x *= H;
//   // Cannot prove: we didn't give the constraints on [n]
//   LemmaB2NTailingZeros(y.m.b, 1); 
//   y *= NorToCH;
//   y *= cl(a => a + 1);
// }


// Preparation + Setup
// Fix the constraint of [n >= 2]
// method Shor1(a : nat, N : nat, n : nat) returns (x : qreg, y : qreg)
//   requires N >= 2 && n >= 2
//   ensures typeof(x) is (n) $ had { forall i | 0 <= i < n :: x[i] == 1 }
//   ensures typeof(y) is exactly (n) $ ch(1) { y[0] == 1 }
//   ensures fresh(x) && fresh(y)
//  {
//   x := nor(n, _ => 0);
//   y := nor(n, _ => 0);
//   x *= H;
//   LemmaB2NTailingZeros(y.m.b, 1);
//   y *= NorToCH;
//   y *= cl(a => a + 1);
// }

// // Preparation + Setup + Expoential
// method Shor2_(a : nat, N : nat, n : nat) returns (x : qreg, y : qreg)
//   requires N >= 2 && n >= 2
//   ensures typeof (y, x) is exactly (n, n) $ ch(Pow2(n)) {
//     forall k | 0 <= k < Pow2(n) :: y[k] == Pow(a, k) % N
//       &&
//     forall k | 0 <= k < Pow2(n) :: x[k] == k
//   }
// {
//   x := nor(n, _ => 0);
//   y := nor(n, _ => 0);
//   x *= H;
//   LemmaB2NTailingZeros(y.m.b, 1);
//   y *= NorToCH;
//   y *= cl(a => a + 1);
//   qfor (i := 0) in x becomes x' with y
//     invariant i == x.card
//     invariant typeof(x') is (N - i) $ had { // find a typo: [N] should be [n] 
//       forall k | 0 <= k < (N - i) :: x'[k] == 1
//     }
//     invariant typeof (y, x) is exactly (N, i) $ ch(Pow2(i)) {
//       forall k | 0 <= k < Pow2(n) :: y[k] == Pow(a, k) % N
//         &&
//       forall k | 0 <= k < Pow2(n) :: x[k] == k
//     }
//   {
//     y *= cl(v => (Pow(a, Pow2(i)) * v) % N);
//   }
// }


// Fix typo : [N] ==> [n]
// method Shor2__(a : nat, N : nat, n : nat) returns (x : qreg, y : qreg)
//   requires N >= 2 && n >= 2
//   ensures typeof (y, x) is exactly (n, n) $ ch(Pow2(n)) {
//     forall k | 0 <= k < Pow2(n) :: y[k] == Pow(a, k) % N
//       &&
//     forall k | 0 <= k < Pow2(n) :: x[k] == k
//   }
// {
//   x := nor(n, _ => 0);
//   y := nor(n, _ => 0);
//   x *= H;
//   LemmaB2NTailingZeros(y.m.b, 1);
//   y *= NorToCH;
//   y *= cl(a => a + 1);
//   reveal Pow2();                
//   qfor (i := 0) in x becomes x' with y
//     invariant i == x.card
//     invariant typeof(x') is (n - i) $ had {
//       forall k | 0 <= k < (n - i) :: x'[k] == 1
//     }
//     invariant typeof (y, x) is exactly (n, i) $ ch(Pow2(i)) {
//       forall k | 0 <= k < Pow2(i) :: y[k] == Pow(a, k) % N
//         &&
//       forall k | 0 <= k < Pow2(i) :: x[k] == k
//     }
//   {
//     y *= cl(v => (Pow(a, Pow2(i)) * v) % N);
//     // refine here!
//   }
// }


// // TOO MANY PROOF OBLIGATIONS, WE NEED TO SPLIT
// method Shor2___(a : nat, N : nat, n : nat, x : qreg, y : qreg) 
//   requires N >= 2 && n >= 2
//   requires typeof(x) is (n) $ had { forall i | 0 <= i < n :: x[i] == 1 }
//   requires typeof(y) is exactly (n) $ ch(1) { y[0] == 1 }
//   ensures typeof (y, x) is exactly (n, n) $ ch(Pow2(n)) {
//     forall k | 0 <= k < Pow2(n) :: y[k] == Pow(a, k) % N
//       &&
//     forall k | 0 <= k < Pow2(n) :: x[k] == k
//   }
//   modifies x, y
// {
//   reveal Pow2(); 
//   qfor (i := 0) in x becomes x' with y
//     invariant i == x.card
//     invariant typeof(x') is (n - i) $ had {
//       forall k | 0 <= k < (n - i) :: x'[k] == 1
//     }
//     invariant typeof (y, x) is exactly (n, i) $ ch(Pow2(i)) {
//       forall k | 0 <= k < Pow2(i) :: y[k] == Pow(a, k) % N
//         &&
//       forall k | 0 <= k < Pow2(i) :: x[k] == k
//     }
//   {
//     y *= cl(v => (Pow(a, Pow2(i)) * v) % N);
//   }
// }


// method Shor2(a : nat, N : nat, n : nat, x : qreg, y : qreg) 
//   requires N >= 2 && n >= 2
//   requires typeof(x) is (n) $ had { forall i | 0 <= i < n :: x[i] == 1 }
//   requires typeof(y) is exactly (n) $ ch(1) { y[0] == 1 }
//   ensures typeof (y, x) is exactly (n, n) $ ch(Pow2(n)) {
//     forall k | 0 <= k < Pow2(n) :: y[k] == Pow(a, k) % N
//       &&
//     forall k | 0 <= k < Pow2(n) :: x[k] == k
//   }
//   modifies x, y
// {
//   reveal Pow2(); 
//   // 0. Prove it's ok on entry
//   assert Pow(a, 0) % N == 1 by {
//     LemmaPow0(a);
//     LemmaSmallMod(1, N);
//   }
//   qfor (i := 0) in x becomes x' with y
//     invariant i == x.card
//     invariant typeof(x') is (n - i) $ had {
//       forall k | 0 <= k < (n - i) :: x'[k] == 1
//     }
//     invariant typeof (y, x) is exactly (n, i) $ ch(Pow2(i)) {
//       forall k | 0 <= k < Pow2(i) :: y[k] == Pow(a, k) % N
//         &&
//       forall k | 0 <= k < Pow2(i) :: x[k] == k
//     }
//   {
//     y *= cl(v => (Pow(a, Pow2(i)) * v) % N);
//   }
// }


// method ShorPreMeasurement(a : nat, N : nat, n : nat) returns (x : qreg, y : qreg)
//   requires N >= 2 && n >= 2
//   ensures typeof (y, x) is exactly (n, n) $ ch(Pow2(n)) {
//     forall k | 0 <= k < Pow2(n) :: y[k] == Pow(a, k) % N
//       &&
//     forall k | 0 <= k < Pow2(n) :: x[k] == k
//   }
//   ensures fresh(x) && fresh(y)
// {
//   x, y := Shor1(a, N, n);
//   Shor2(a, N, n, x, y);
// }
 
method ShorPostMeasurement(a : nat, N : nat, n : nat, x : qreg, y : qreg)
  requires N >= 2 && n >= 2
  requires typeof (y, x) is exactly (n, n) $ ch(Pow2(n)) {
    forall k | 0 <= k < Pow2(n) :: y[k] == Pow(a, k) % N
      &&
    forall k | 0 <= k < Pow2(n) :: x[k] == k
  }
  ensures exists r : nat :: exists t : nat :: typeof (x) is exactly (n) $ ch(x.m.dof) {
    forall k | 0 <= k < x.m.dof :: exists m : nat :: x[k] == r * m + t
  }
  modifies x, y;
{
  var base, idxmap, m', k;
  base, idxmap, m', k := y.Measure();
  assert typeof (x) is exactly (n) $ ch(x.m.dof) {
    forall k | 0 <= k < x.m.dof <= Pow2(n) / N :: (Pow(a, x[k]) % N) == base
  };
}