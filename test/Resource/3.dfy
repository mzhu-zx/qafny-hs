import opened DivMod
import opened Mul
import opened Power2
import opened Unity
method DeutschJozsa (n : nat)
{
  var q : nor := 1;
  var p : nor := 2;
  undefined Stmt : SApply (Session [Ran "q" (ENum 0) (ENum 1)]) EHad;
  undefined Stmt : SApply (Session [Ran "p" (ENum 0) (EVar "n")]) EHad;
}

method CrossMinus (n : nat, m : nat, q : nat, p : nat)
{
}

