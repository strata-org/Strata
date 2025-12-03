/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
procedure opaqueBody(x: int): (r: int)
  ensures assert 1 == 1; r >= 0
{
  Math.abs(x)
}

procedure transparantBody(x: int): int
{
  Math.abs(x)
}

procedure fooProof() {
  assert transparantBody(-1) == 1; -- pass
  assert opaqueBody(-1) >= 0 -- pass
  assert opaqueBody(-1) == 1; -- error
}

/-
Translation to B3:

function opaqueBody(x: int): int
assume forall((x: int) -> var r = opaqueBody(x); r >= 0);

proof opaqueBody_ContractProof() {
  assert 1 == 1; -- pass
}

proof opaqueBody_BodyProof() {
  var x: int;
  var r = Math.abs(x);
  assert r >= 0; -- pass
}

function transparantBody(x: int): int {
  Math.abs(x)
}

proof fooProof() {
  assert transparantBody(-1) == 1; -- pass
  assert opaqueBody(-1) >= 0 -- pass
  assert opaqueBody(-1) == 1; -- error  
}
-/