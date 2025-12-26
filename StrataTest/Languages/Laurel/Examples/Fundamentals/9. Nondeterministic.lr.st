/*
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
*/

/*
When a procedure is non-deterministic, 
every invocation might return a different result, even if the inputs are the same.
It's comparable to having an IO monad.
*/
nondet procedure nonDeterministic(x: int): (r: int)
  ensures r > 0
{
  assumed
}

procedure caller() {
  var x = nonDeterministic(1)
  assert x > 0; -- pass
  var y = nonDeterministic(1)
  assert x == y; -- fail
}

/*
Translation towards SMT:

function nonDeterministic_relation(x: int, r: int): boolean
// ensures axiom
axiom forall x, r: int ontrigger nonDeterministic_relation(x, r) :: r > 0

proof nonDeterministic_body {
  var x: int;
  var r := Math.abs(x) + 1
  assert nonDeterministic_relation(x, r);
}

proof caller_body {
  var x: int;
  assume nonDeterministic_relation(1, x);
  assert x > 0; // pass

  var y: int;
  assume nonDeterministic_relation(1, y);
  assert x == y; // fail
}
*/

nondet procedure nonDeterminsticTransparant(x: int): (r: int)
{
  nonDeterministic(x + 1)
}

/*
Translation towards SMT:

function nonDeterminsticTransparant_relation(x: int, r: int): boolean {
  nonDeterministic_relation(x + 1, r)
}
*/

procedure nonDeterministicCaller(x: int): int
{
  nonDeterministic(x) // error: can not call non-deterministic procedure from deterministic one
}