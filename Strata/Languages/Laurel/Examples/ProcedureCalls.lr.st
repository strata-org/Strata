
-- body is transparant despite having mutation
val fooReassign = procedure(): int {
  var x = 0;
  x = x + 1;
  assert x == 1;
  x = x + 1;
  x
}

val fooSingleAssign = procedure(): int {
  var x = 0
  var x2 = x + 1;
  var x3 = x2 + 1;
  x3
}

val proof = procedure() {
  assert fooReassign() == fooSingleAssign(); -- passes
}