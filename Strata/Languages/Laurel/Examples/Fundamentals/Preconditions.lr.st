/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
procedure hasRequires(x: int): (r: int)
  requires x > 2
{
  assert x > 0; -- pass
  assert x > 3; -- fail
  x + 1
}

procedure fooProof() {
  var x = hasRequires(1) -- fail
  var y = hasRequires(3) -- pass
}

/-
Translation to B3:

function hasRequires(x: int): int requires x > 2 {
  x + 1
}

proof hasRequires_BodyProof {
  var x: int;
  assume x > 2;
  var r = x + 1;
  assert r > 0; -- pass
  assert r > 3; -- fail
}

proof fooProof_BodyProof {
  var x = hasRequires(1) -- fail
  var y = hasRequires(3) -- pass
}
-/