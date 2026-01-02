/*
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
*/

procedure nestedImpureStatements(): int {
  var x = 0;
  var y = 0;
  if ((x = x + 1) == (y = x)) {
    1
  } else {
    2
  }
}

procedure assertLocallyImpureCode()
{
  assert nestedImpureStatements() != 0; // pass
}

/*
Translation towards SMT:

function nestedImpureStatements(): int {
  var x = 0;
  var y = 0;
  x = x + 1;
  var t1 = x;
  y = x;
  var t2 = x;
  if (t1 == t2) {
    1
  } else {
    2
  }
}

*/