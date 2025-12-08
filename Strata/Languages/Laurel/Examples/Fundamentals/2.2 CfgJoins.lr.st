/*
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
*/
procedure guards(a: int): int
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

/*
Translation towards SMT:

function guards(a: int): int {
  var b = a + 2;
  if (b > 2) {

  }
}

*/