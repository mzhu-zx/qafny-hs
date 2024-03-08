// TODO: We should prove the following two lemmas

function Pow2(n : nat) : nat {
  if n == 0 then
    1
  else
    n * Pow2(n-1)
}


predicate Balanced(f : nat --> nat, n : nat)
  requires n >= 1
  requires forall i | 0 <= i < Pow2(n) :: f.requires(i) 
  requires forall a | f.requires(a) :: f(a) == 0 || f(a) == 1
{
  var m := multiset(seq(Pow2(n), i requires 0 <= i < Pow2(n) => f(i)));
  0 in m && 1 in m && m[0] == m[1] == Pow2(n-1)
}

predicate Constant(f : nat --> nat, n : nat)
  requires n >= 1
  requires forall i | 0 <= i < Pow2(n) :: f.requires(i) 
  requires forall a | f.requires(a) :: f(a) == 0 || f(a) == 1
{
  var m := multiset(seq(Pow2(n), i requires 0 <= i < Pow2(n) => f(i)));
  (0 in m && m[0] == Pow2(n)) || (1 in m && m[1] == Pow2(n))
}

function fBalance(x : nat) : nat
  requires 0 <= x < Pow2(4)
{
  x % 2
}

lemma {:axiom} fBalanceIsBalance()
  ensures Balanced(fBalance, 4)


function fConstant(x : nat) : (r : nat)
  requires 0 <= x < Pow2(4)
  ensures r == 1
{
  1
}

lemma {:axiom} fConstantIsConstant()
  ensures Constant(fConstant, 4)
