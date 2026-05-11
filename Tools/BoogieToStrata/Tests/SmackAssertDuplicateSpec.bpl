// Regression test: assert_.<type> procedure with an existing ensures clause
// should produce a single merged spec block, not two separate spec blocks.
// Bug: VisitProcedure emitted a second spec { requires ... } block in addition
// to the one already emitted by WriteProcedureHeader for existing ensures.

type i32 = int;

procedure assert_.i32(p.0: i32) returns ($r: i32);
  ensures ($r == 0);

procedure main() returns ($r: i32)
{
  // assert(true) -- should pass because p.0 != 0 holds for 1
  call $r := assert_.i32(1);
  return;
}
