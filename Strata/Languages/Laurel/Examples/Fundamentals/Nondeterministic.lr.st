/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
procedure nonDeterministic(x: int): (r: nondet int)
  ensures r > 0
{
  Math.abs(x) + 1
}

procedure fooProof() {
  var x = nonDeterministic(1)
  var y = nonDeterministic(1)
  assert x > 0; -- pass
  assert x == y; -- fail
}

/-
Translation to B3:

val nonDeterministic_Ensures = function(x: int, r: int): boolean
assume forall((x: int, r: int) -> nonDeterministic_Ensures(x, r) == r > 0);

val nonDeterministic_BodyProof = proof {
  ...
}

val fooProof_BodyProof = proof {
  var x: int;
  assume nonDeterministic_Ensures(1, x);
  var y: int;
  assume nonDeterministic_Ensures(1, y);
  assert x > 0; -- pass
  assert x == y; -- fail
}
-/

val nonDeterministicCaller = procedure(x: int): int
{
  nonDeterministic(x) -- error can not call non-deterministic procedure from deterministic one
}

val nonDeterminsticTransparant = procedure(x: int): nondet int
-- error, a non-deterministic procedure must have an ensures clause: its body must be opaque
{
  3
}