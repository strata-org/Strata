// {:smack}
// Regression test for __VERIFIER_assume `free ensures` synthesis.
// SMACK encodes C `assume(b)` as a call to `__VERIFIER_assume(b)`.
// BoogieToStrata under --smack injects `free ensures ($i0 != 0)`
// so callers may assume the constraint after the call.

type i32 = int;

procedure __VERIFIER_assume($i0: i32);

procedure main() returns ($r: i32)
{
  var x: i32;
  // After the call, x != 0 holds (via the synthesized free ensures).
  call __VERIFIER_assume(x);
  $r := 0;
  return;
}
