// Minimal test case for SMACK assert_ pattern recognition.
// SMACK encodes C assert(expr) as a call to assert_.i32(cond).
// BoogieToStrata should recognize this pattern and emit:
//   assert (_i0 != 0);
// instead of an opaque procedure call.

type i32 = int;
type i1 = int;

procedure assert_.i32(p.0: i32) returns ($r: i32);

procedure main() returns ($r: i32)
{
  var $i0: i32;
  $i0 := 1;
  call $r := assert_.i32($i0);
  $r := 0;
  return;
}
