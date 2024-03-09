include "../../../external/libraries/src/NonlinearArithmetic/Power2.dfy"

import opened Power2

// the domain of the function is [0 .. N]
predicate DataFunction(f : nat --> nat, N : nat, target : nat)
  requires N > 0
  requires forall i : nat | i < N :: f.requires(i)
  requires forall i : nat | i < N && i != target :: f(i) == 0
  requires target < N && f(target) == 1
