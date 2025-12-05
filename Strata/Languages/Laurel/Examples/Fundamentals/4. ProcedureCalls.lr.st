/*
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
*/

procedure fooReassign(): int {
  var x = 0;
  x = x + 1;
  assert x == 1;
  x = x + 1;
  x
}

procedure fooSingleAssign(): int {
  var x = 0
  var x2 = x + 1;
  var x3 = x2 + 1;
  x3
}

procedure fooProof() {
  assert fooReassign() == fooSingleAssign(); // passes
}

/*
Translation towards SMT:

function fooReassign(): int {
  var x0 = 0;
  var x1 = x0 + 1;
  var x2 = x1 + 1;
  x2
}

proof fooReassign_body {
  var x = 0;
  x = x + 1;
  assert x == 1;
}

function fooSingleAssign(): int {
  var x = 0;
  var x2 = x + 1;
  var x3 = x2 + 1;
  x3
}

proof fooProof_body {
  assert fooReassign() == fooSingleAssign();
}
*/