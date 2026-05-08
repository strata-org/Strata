// Test case: parameter names that shadow type synonym names.
// BoogieToStrata produces output that the Strata parser rejects because
// the parameter name 'i1' conflicts with the type synonym 'i1'.

type i1 = int;
type i32 = int;

function {:inline} $add.i1(i1: i1, i2: i1) returns (i1) { i1 + i2 }

function {:inline} $eq.i1(i1: i1, i2: i1) returns (i1) {
  if i1 == i2 then 1 else 0
}

procedure main() returns (r: i32)
ensures r == 0;
{
  var x: i1;
  var y: i1;
  x := 1;
  y := $add.i1(x, x);
  assert y == 2;
  r := 0;
}
