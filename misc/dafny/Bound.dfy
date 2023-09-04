method TestBound(a : seq<nat>)
  requires |a| == 10 && forall i : nat | i < 10 :: a[i] == 0
{
  var b := a[0 .. 5];
  var c := b[1 .. 4];
  var d := c[0 .. 3];
  assert forall i : nat | 1 <= i < 2 :: d[i] == 0;
  // cannot prove
}

method TestBound_LessHints(a : seq<nat>)
  requires |a| == 10 && forall i : nat | i < 10 :: a[i] == 0
{
  var b := a[0 .. 5];
  assert forall i : nat | 0 <= i < 5 :: b[i] == 0;

  var c := b[1 .. 4];
  var d := c[0 .. 3];
  assert forall i : nat | 1 <= i < 2 :: d[i] == 0;
  // can prove
}

method TestBound_LessHints_MoreLayer(a : seq<nat>)
  requires |a| == 10 && forall i : nat | i < 10 :: a[i] == 0
{
  var b := a[0 .. 5];
  assert forall i : nat | 0 <= i < 5 :: b[i] == 0;

  var c := b[1 .. 4];
  var d := c[0 .. 3];
  var e := d[1 .. 2];
  assert (e[0] == 1);
  // cannot prove
}


method TestBound_MoreHints(a : seq<nat>)
  requires |a| == 10 && forall i : nat | i < 10 :: a[i] == 0
{
  var b := a[0 .. 5];
  assert forall i : nat | 0 <= i < 5 :: b[i] == 0;

  var c := b[1 .. 4];
  assert forall i : nat | 0 <= i < 3 :: c[i] == 0;

  var d := c[0 .. 3];
  assert forall i : nat | 1 <= i < 2 :: d[i] == 0;
  // can prove
}
