
val opaqueBody = procedure(x: int): (r: int)
  ensures assert 1 == 1; r >= 0
{
  Math.abs(x)
}

val transparantBody = procedure(x: int): int
{
  Math.abs(x)
}

val fooProof = procedure() {
  assert transparantBody(-1) == 1; -- pass
  assert opaqueBody(-1) >= 0 -- pass
  assert opaqueBody(-1) == 1; -- error
}

/-
Translation to B3:

val opaqueBody = function(x: int): int
assume forall((x: int) -> var r = opaqueBody(x); r >= 0);

val opaqueBody_ContractProof = proof() {
  assert 1 == 1; -- pass
}

val opaqueBody_BodyProof = proof() {
  var x: int;
  var r = Math.abs(x);
  assert r >= 0; -- pass
}

val transparantBody = function(x: int): int
assume forall((x: int) -> opaqueBody(x) == Math.abs(x));

var fooProof = proof() {
  assert transparantBody(-1) == 1; -- pass
  assert opaqueBody(-1) >= 0 -- pass
  assert opaqueBody(-1) == 1; -- error  
}
-/