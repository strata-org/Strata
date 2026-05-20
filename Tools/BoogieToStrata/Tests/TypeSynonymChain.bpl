// Regression test for multi-level type synonym resolution.
// dealiasTypeExpr must recurse through: ref → i64 → int
// Without recursive resolution, comparison and arithmetic on `ref`
// trigger a panic because the type stays as a synonym instead of
// resolving to the base `int` type.

type i64 = int;
type ref = i64;

procedure main() returns (r: ref)
ensures r >= 0;
{
  var a: ref;
  var b: ref;
  a := 3;
  b := a + 4;
  assert b == 7;
  assert a <= b;
  r := b;
}
