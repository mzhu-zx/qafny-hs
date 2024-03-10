method Assign() {
  var n := seq<nat>(4, _ => 2);
  var m := seq<nat>(4, _ => 1);
  n, m := m, n;
  assert n[0] == 1 && m[0] == 2;
}
