// {:smack}
// Regression test: assert_.<type> procedures must produce a single
// merged spec block, not duplicates, regardless of whether the input
// already has user-written specs.
//
// Two procedures exercise the two cases:
//   1. assert_.i32 has only an existing `ensures` — output must merge
//      the synthetic `requires (p.0 != 0)` with the existing ensures
//      into one spec block.
//   2. assert_.i32_with_req has an existing `requires (p.0 > -1)` —
//      output must contain BOTH requires clauses (the synthetic one
//      and the user-written one) in a single spec block, not drop the
//      synthetic one.

type i32 = int;

procedure assert_.i32(p.0: i32) returns ($r: i32);
  ensures ($r == 0);

procedure assert_.i32_with_req(p.0: i32) returns ($r: i32);
  requires (p.0 > -1);

procedure main() returns ($r: i32)
{
  // assert(true) -- should pass because p.0 != 0 holds for 1
  call $r := assert_.i32(1);
  // call assert_.i32_with_req(1) — both `1 != 0` and `1 > -1` hold
  call $r := assert_.i32_with_req(1);
  return;
}
