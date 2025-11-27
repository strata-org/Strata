/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
procedure nesting(a: int): int
  requires a > 0 && a < 100
  returns
{
  var b = a + 2;
  if (b > 2) {
      var c = b + 3;
      if (c > 3) {
          return c + 4;
      }
      var d = c + 5;
      return d + 6;
  }
  var e = b + 1;
  e
}

procedure nestedImpureCalls(): int {
    var x = 0;
    var y = 0;
    if ((x = x + 1) == (y = x)) {
        return;
    }
    assert false;
}