program Core;

// An example for common subexpression elimination (the
// `commonSubexprElim` phase of the default pipeline).
//
// `y` is built by four steps of `y := y * y + y`, so after symbolic
// evaluation it is one large term shared by every statement that mentions
// it. Each of the 10 branches below splits the path: the branch assumes a
// fact about `y`, checks `r == y` and leaves the block, and the other path
// continues to the next branch. Symbolic evaluation therefore nests a block
// per branch, and every resulting path repeats `y`. Every goal is discharged
// without a solver.
//
// The timing test StrataTestExtra/Transform/CommonSubexprElimScaling.lean
// verifies this program with 400 branches and bounds the time CSE takes.

procedure Dispatch(x : int, out y : int, out r : int)
spec {
  ensures [r_is_y]: r == y;
}
{
  y := x;
  y := int.add(int.mul(y, y), y);
  y := int.add(int.mul(y, y), y);
  y := int.add(int.mul(y, y), y);
  y := int.add(int.mul(y, y), y);
  done: {
    if (x == 0) { assume [a0]: int.ge(int.add(y, 0), 0); r := y; assert [b0]: r == y; exit done; }
    if (x == 1) { assume [a1]: int.ge(int.add(y, 1), 0); r := y; assert [b1]: r == y; exit done; }
    if (x == 2) { assume [a2]: int.ge(int.add(y, 2), 0); r := y; assert [b2]: r == y; exit done; }
    if (x == 3) { assume [a3]: int.ge(int.add(y, 3), 0); r := y; assert [b3]: r == y; exit done; }
    if (x == 4) { assume [a4]: int.ge(int.add(y, 4), 0); r := y; assert [b4]: r == y; exit done; }
    if (x == 5) { assume [a5]: int.ge(int.add(y, 5), 0); r := y; assert [b5]: r == y; exit done; }
    if (x == 6) { assume [a6]: int.ge(int.add(y, 6), 0); r := y; assert [b6]: r == y; exit done; }
    if (x == 7) { assume [a7]: int.ge(int.add(y, 7), 0); r := y; assert [b7]: r == y; exit done; }
    if (x == 8) { assume [a8]: int.ge(int.add(y, 8), 0); r := y; assert [b8]: r == y; exit done; }
    if (x == 9) { assume [a9]: int.ge(int.add(y, 9), 0); r := y; assert [b9]: r == y; exit done; }
    r := y;
  }
};
