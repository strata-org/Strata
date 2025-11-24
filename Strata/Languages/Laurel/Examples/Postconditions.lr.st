
val opaqueBody = procedure(x: int): int 
  ensures assert true; x >= 0
{
  Math.abs(x)
}

val transparantBody = procedure(x: int): int
{
  Math.abs(x)
}

val proof = procedure() {
  assert transparantBody(-1) == 1; -- pass
  assert opaqueBody(-1) >= 0 -- pass
  assert opaqueBody(-1) == 1; -- error
}

/-
Translation to B3:

val opaqueBody = function(x: int): int
assume forall((x: int) -> opaqueBody(x) > 0);

val transparantBody = function(x: int): int
assume forall((x: int) -> opaqueBody(x) == Math.abs(x));
-/