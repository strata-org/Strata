/*
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
*/



procedure nestedImpureStatements(x: int): int {
  var y := 0;
  var z := x;


  if ((z := z + 1) == (y == z)) {
    assert y == x + 1;
    1
  } else {
    assert false;
    3
  }
}

procedure assertLocallyImpureCode()
{
  assert 3 != 0; // pass
}

/*
Translation towards SMT:

function nestedImpureStatements(): int {
  var x := 0;
  var y := 0;
  x := x + 1;
  var t1 := x;
  y := x;
  var t2 := x;
  if (t1 == t2) {
    1
  } else {
    2
  }
}

*/