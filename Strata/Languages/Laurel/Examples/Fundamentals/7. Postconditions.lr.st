/*
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
*/
procedure opaqueBody(x: int): (r: int)
  ensures assert 1 == 1; r >= 0
{
  Math.abs(x)
}

procedure transparantBody(x: int): int
{
  Math.abs(x)
}

procedure caller() {
  assert transparantBody(-1) == 1; -- pass
  assert opaqueBody(-1) >= 0 -- pass
  assert opaqueBody(-1) == 1; -- error
}

/*
Translation towards SMT:

function opaqueBody_ensures(x: int, r: int): boolean {
  r >= 0
}

proof opaqueBody_ensures {
  assert 1 == 1; // pass
}

proof opaqueBody_body {
  var x: int;
  var r = Math.abs(x);
  assert r >= 0; // pass
}

function transparantBody(x: int): int {
  Math.abs(x)
}

proof caller_body {
  assert transparantBody(-1); // pass

  var r_1: int;
  assume opaqueBody_ensures(-1, r_1);
  assert r_1 >= 0; // pass

  var r_2: int;
  assume opaqueBody_ensures(-1, r_2);
  assert r_2 == 1; // error  
}
*/