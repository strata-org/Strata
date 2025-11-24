
val hasRequires = procedure(x: int): (r: int)
  requires x > 2
{
  assert x > 0; -- pass
  assert x > 3; -- fail
  x + 1
}

val fooProof = procedure() {
  var x = hasRequires(1) -- fail
  var y = hasRequires(3) -- pass
}

/-
Translation to B3:

val hasRequires = function(x: int): int requires x > 2
assume forall((x: int) -> var r = hasRequires(x); r = x + 1);

val hasRequires_BodyProof = proof() {
  var x: int;
  assume x > 2;
  var r = x + 1;
  assert r > 0; -- pass
  assert r > 3; -- fail
}

val fooProof = procedure() {
  var x = hasRequires(1) -- fail
  var y = hasRequires(3) -- pass
}
-/