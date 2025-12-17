/*
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
*/
procedure hasRequires(x: int): (r: int)
  requires assert 1 == 1; x > 2
{
  assert x > 0; // pass
  assert x > 3; // fail
  x + 1
}

procedure caller() {
  var x = hasRequires(1) // fail
  var y = hasRequires(3) // pass
}

/*
Translation towards SMT:

function hasRequires_requires(x: int): boolean {
  x > 2
}

function hasRequires(x: int): int {
  x + 1
}

proof hasRequires_requires {
  assert 1 == 1;
}

proof hasRequires_body {
  var x: int;
  assume hasRequires_requires();
  assert x > 0; // pass
  assert x > 3; // fail
}

proof caller_body {
  var hasRequires_arg1 := 1;
  assert hasRequires_ensures(hasRequires_arg1); // fail
  var x := hasRequires(hasRequires_arg1);

  var hasRequires_arg1_2 := 3;
  assert hasRequires_ensures(hasRequires_arg1_2); // pass
  var y: int := hasRequires(hasRequires_arg1_2);
}
*/