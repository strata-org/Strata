// Test case: sanitization collision in BoogieToStrata.
//
// SanitizeNameForStrata replaces '.', '$', '@', '#', '^' with '_'.
// This means distinct Boogie identifiers can map to the same Strata name:
//   $add.i32  →  _add_i32
//   $add_i32  →  _add_i32   (collision!)
//
// The rename mechanism should detect this and disambiguate.

type i32 = int;

function {:inline} $add.i32(i1: i32, i2: i32) returns (i32) { i1 + i2 }
function {:inline} $add_i32(i1: i32, i2: i32) returns (i32) { i1 + i2 }

procedure main() returns (r: i32)
ensures r == 5;
{
  var a: i32;
  var b: i32;
  a := $add.i32(2, 3);
  b := $add_i32(2, 3);
  assert a == 5;
  assert b == 5;
  r := a;
}
