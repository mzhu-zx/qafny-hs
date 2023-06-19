include "../../external//QPreludeUntyped.dfy"
include "../../external//libraries/src/Collections/Sequences/Seq.dfy"
include "../../external//libraries/src/NonlinearArithmetic/Power2.dfy"

// target Dafny version: 3.12.0
abstract module QafnyDefault {
import opened QPreludeUntyped
import opened Seq
import opened Power2

method For0 (n : nat)
  requires n > 0
{
  // Forward Declaration
  var p__seq__nat____6 : seq<nat>;
  var q__seq__nat____5 : seq<nat>;
  var q__seq__nat____4 : seq<nat>;
  var p__seq__nat____3 : seq<nat>;
  var q__seq__nat____2 : seq<nat>;
  var p__seq__nat____1 : seq<nat>;
  var q__seq__nat____0 : seq<nat>;
  
  // Method Definition
  q__seq__nat____0 := seq<nat>(n, _ => 0);
  p__seq__nat____1 := seq<nat>(n, _ => 0);
  // Cast TNor ==> THad
  q__seq__nat____2 := CastNorHad(q__seq__nat____0);
  // Cast TNor ==> TCH
  p__seq__nat____3 := CastNorCH10(p__seq__nat____1);
  q__seq__nat____4 := q__seq__nat____2;
  // Retype from Had to CH and initialize with 0
  q__seq__nat____5 := seq<nat>(|q__seq__nat____5|, _ => 0);
  for i := 0 to n
  {
    p__seq__nat____6 := p__seq__nat____3;
    {
      p__seq__nat____3 := Map(x => x + 1 % 2, p__seq__nat____3);
    }

    p__seq__nat____3 := p__seq__nat____3 + p__seq__nat____6;
    q__seq__nat____5 := q__seq__nat____5 + Map(x__lambda => x__lambda + Pow2(i), q__seq__nat____5);
  }

}

}
