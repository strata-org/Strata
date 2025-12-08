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
  Math.abs(x) + 1
}

procedure caller() {
  var x = nonDeterministic(1)
  assert x > 0; -- pass
  var y = nonDeterministic(1)
  assert x == y; -- fail
}

/*
Translation towards SMT:

function nonDeterministic_ensures(x: int, r: int): boolean {
  r > 0
}

proof nonDeterministic_body {
  var x: int;
  var r := Math.abs(x) + 1
  assert nonDeterministic_ensures(x, r);
}

proof caller_body {
  var x: int;
  assume nonDeterministic_Ensures(1, x);
  assert x > 0; // pass

  var y: int;
  assume nonDeterministic_Ensures(1, y);
  assert x == y; // fail
}
*/

procedure nonDeterministicCaller(x: int): int
{
  nonDeterministic(x) // error: can not call non-deterministic procedure from deterministic one
}

nondet procedure nonDeterminsticTransparant(x: int): (r: int)
{
  nonDeterministic(x + 1)
}

/*
Translation towards SMT:

function nonDeterminsticTransparant_ensures(x: int, r: int): boolean {
  nonDeterministic_ensures(x + 1, r)
}
*/