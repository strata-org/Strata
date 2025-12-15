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
    assert y == x + 1;
//  ^^^^^^^^^^^^^^^^^ error: could not prove assertion
    2
  }
}

procedure assertLocallyImpureCode()
{
    assert nestedImpureStatements(1) == 3; // fail
//  ^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^ error: could not prove assertion
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