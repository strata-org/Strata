/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
function nesting(a: int): int
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

composite Counter {
  var value: int
}

int nestedImpureCalls(counter: Counter) {
    if (add(counter, 1) == 1) {
        var x = add(counter, add(counter, 2));
        return x;
    }
    return add(counter, 3);
}

method add(counter: Counter, amount: int): int {
  counter.value = counter.value + amount
}