/*
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
*/
procedure foo(x: nat)
  decreases x, 1
{
  bar(x);
}

procedure bar(x: nat)
  decreases x, 0
{
  if x != 0 { foo(x-1); }
}

/*
Translation towards SMT:

proof foo_body {
  var x: nat;
  assert decreases([x, 1], [x, 0]);
}

proof bar_body {
  var x: nat;
  if (x != 0) {
    assert decreases([x, 0], [x - 1, 1]);
  }
}

*/