// {:smack}
// Regression test: when __VERIFIER_assume already carries a
// user-written ensures clause, the synthetic `free ensures (i0 != 0)`
// must be added ALONGSIDE the existing clause in a single merged spec
// block, not silently dropped. Structurally analogous to
// SmackAssertDuplicateSpec.bpl's "requires-already-present" case.

type i32 = int;

// __VERIFIER_assume with a pre-existing user-written `ensures` clause.
// The synthesis appends `free ensures (i0 != 0)` after the existing
// clause. The merged spec block must contain BOTH clauses.
procedure __VERIFIER_assume($i0: i32);
  ensures ($i0 > -1);

procedure main() returns ($r: i32)
{
  var x: i32;
  call __VERIFIER_assume(x);
  $r := 0;
  return;
}
