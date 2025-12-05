/*
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
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
Translation to B3:

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
Translation to B3:

function nonDeterminsticTransparant_ensures(x: int, r: int): boolean {
  nonDeterministic_ensures(x + 1, r)
}
*/