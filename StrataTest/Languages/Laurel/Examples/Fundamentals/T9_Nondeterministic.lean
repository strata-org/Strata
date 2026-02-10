/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestDiagnostics
import StrataTest.Languages.Laurel.TestExamples

open StrataTest.Util
open Strata

namespace Laurel

def program := r"
nondet procedure nonDeterministic(x: int): (r: int)
  ensures r > 0
{
  assumed
}

procedure caller() {
  var x = nonDeterministic(1)
  assert x > 0;
  var y = nonDeterministic(1)
    assert x == y;
//  ^^^^^^^^^^^^^^ error: assertion does not hold
}

nondet procedure nonDeterminsticTransparant(x: int): (r: int)
{
  nonDeterministic(x + 1)
}

procedure nonDeterministicCaller(x: int): int
{
  nonDeterministic(x)
}
"

-- Not working yet
-- #eval! testInput "Nondeterministic" program processLaurelFile

/-
When a procedure is non-deterministic,
every invocation might return a different result, even if the inputs are the same.
It's comparable to having an IO monad.

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

function nonDeterminsticTransparant_relation(x: int, r: int): boolean {
  nonDeterministic_relation(x + 1, r)
}
-/
