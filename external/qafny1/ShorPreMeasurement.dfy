import opened QPrelude
import opened B2N
import opened Power2  
import opened Power
import opened DivMod

// Preparation
// method Initialize(a : nat, N : nat, n : nat) returns (x : qreg, y : qreg)
//   requires N >= 2 && n >= 2
//   ensures typeof(x) is (n) $ nor { forall i | 0 <= i < n :: x[i] == 0 }
//   ensures typeof(y) is (n) $ nor { forall i | 0 <= i < n :: y[i] == 0 }
//   ensures fresh(x) && fresh(y)
// {
//   x := nor(n, _ => 0);
//   y := nor(n, _ => 0);
// }

// Preparation + Setup
// method Prepare_(a : nat, N : nat, n : nat) returns (x : qreg, y : qreg)
//   requires N >= 2
//   ensures typeof(x) is (n) $ had { forall i | 0 <= i < n :: x[i] == 1 }
//   ensures typeof(y) is exactly (n) $ ch(1) { y[0] == 1 }
//   ensures fresh(x) && fresh(y)
// {
//   x := nor(n, _ => 0);
//   y := nor(n, _ => 0);
//   x *= H;
//   LemmaB2NTailingZeros(y.m.b, 1); 
//   y *= NorToCH;
//   y *= cl(a => a + 1);
// }


// Preparation + Setup
// Fix the constraint of [n >= 2]
method Prepare(a : nat, N : nat, n : nat) returns (x : qreg, y : qreg)
  requires N >= 2 && n >= 2
  ensures typeof(x) is (n) $ had { forall i | 0 <= i < n :: x[i] == 1 }
  ensures typeof(y) is exactly (n) $ ch(1) { y[0] == 1 }
  ensures fresh(x) && fresh(y)
 {
  x := nor(n, _ => 0);
  y := nor(n, _ => 0);
  x *= H;
  LemmaB2NTailingZeros(y.m.b, 1);
  y *= NorToCH;
  y *= cl(a => a + 1);
}

// // Preparation + Setup + Expoential
// method ModExp_(a : nat, N : nat, n : nat) returns (x : qreg, y : qreg)
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
// method ModExp__(a : nat, N : nat, n : nat) returns (x : qreg, y : qreg)
//   requires N >= 2 && n >= 2
//   ensures typeo1f (y, x) is exactly (n, n) $ ch(Pow2(n)) {
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
// method ModExp___(a : nat, N : nat, n : nat, x : qreg, y : qreg) 
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


lemma LemmaPow0Mod(a : nat, N : nat) 
  requires N > 1
  ensures Pow(a, 0) % N == 1
{
  LemmaPow0(a);
  LemmaSmallMod(1, N);
}

method ModExp(a : nat, N : nat, n : nat, x : qreg, y : qreg) 
  requires N >= 2 && n >= 2
  requires typeof(x) is (n) $ had { forall i | 0 <= i < n :: x[i] == 1 }
  requires typeof(y) is exactly (n) $ ch(1) { y[0] == 1 }
  ensures typeof (y, x) is exactly (n, n) $ ch(Pow2(n)) {
    forall k | 0 <= k < Pow2(n) :: y[k] == Pow(a, k) % N
      &&
    forall k | 0 <= k < Pow2(n) :: x[k] == k
  }
  modifies x, y
{
  reveal Pow2(); 
  // 0. Prove it's ok on entry
  LemmaPow0Mod(a, N);
  qfor (i := 0) in x becomes x' with y
    invariant i == x.card
    invariant typeof(x') is (n - i) $ had {
      forall k | 0 <= k < (n - i) :: x'[k] == 1
    }
    invariant typeof (y, x) is exactly (n, i) $ ch(Pow2(i)) {
      forall k | 0 <= k < Pow2(i) :: y[k] == Pow(a, k) % N
        &&
      forall k | 0 <= k < Pow2(i) :: x[k] == k
    }
  {
    y *= cl(v => (Pow(a, Pow2(i)) * v) % N);
  }
}

method ShorPreMeasurement(a : nat, N : nat, n : nat) returns (x : qreg, y : qreg)
  requires N >= 2 && n >= 2
  ensures typeof (y, x) is exactly (n, n) $ ch(Pow2(n)) {
    forall k | 0 <= k < Pow2(n) :: y[k] == Pow(a, k) % N
      &&
    forall k | 0 <= k < Pow2(n) :: x[k] == k
  }
  ensures fresh(x) && fresh(y)
{
  x, y := Prepare(a, N, n);
  ModExp(a, N, n, x, y);
}
 
