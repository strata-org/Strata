/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.Verifier

---------------------------------------------------------------------
namespace Strata

def gaussPgm :=
#strata
program Core;

procedure sum(n : int) returns (s : int)
spec {
  requires (n >= 0);
  ensures (s == ((n * (n + 1)) / 2));
}
{
  var i : int;
  i := 0;
  s := 0;
  while (i < n)
    invariant 0 <= i
    invariant i <= n
    invariant s == (i * (i + 1)) / 2
  {
    i := (i + 1);
    s := (s + i);
  }
};
#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: sum_post_sum_ensures_1_calls_Int.SafeDiv_0
Property: assert
Assumptions:
sum_requires_0: $__n0 >= 0
Obligation:
true

Label: loop_invariant_calls_Int.SafeDiv_0
Property: assert
Assumptions:
sum_requires_0: $__n2 >= 0
Obligation:
true

Label: entry_invariant_0
Property: assert
Assumptions:
<label_ite_cond_true: (~Int.Lt i n)>: 0 < $__n2
sum_requires_0: $__n2 >= 0
Obligation:
true && 0 <= $__n2 && true

Label: arbitrary_iter_maintain_invariant_0
Property: assert
Assumptions:
<label_ite_cond_true: (~Int.Lt i n)>: 0 < $__n2
assume_guard_0: $__i5 < $__n2
assume_invariant_0: 0 <= $__i5 && $__i5 <= $__n2 && $__s6 == $__i5 * ($__i5 + 1) / 2
sum_requires_0: $__n2 >= 0
Obligation:
0 <= $__i5 + 1 && $__i5 + 1 <= $__n2 && $__s6 + ($__i5 + 1) == ($__i5 + 1) * ($__i5 + 1 + 1) / 2

Label: sum_ensures_1
Property: assert
Assumptions:
sum_requires_0: $__n2 >= 0
<label_ite_cond_true: (~Int.Lt i n)>: if 0 < $__n2 then (0 < $__n2) else true
assume_guard_0: if 0 < $__n2 then ($__i5 < $__n2) else true
assume_invariant_0: if 0 < $__n2 then (0 <= $__i5 && $__i5 <= $__n2 && $__s6 == $__i5 * ($__i5 + 1) / 2) else true
not_guard_0: if 0 < $__n2 then !($__i7 < $__n2) else true
invariant_0: if 0 < $__n2 then (0 <= $__i7 && $__i7 <= $__n2 && $__s8 == $__i7 * ($__i7 + 1) / 2) else true
<label_ite_cond_false: !(~Int.Lt i n)>: if if 0 < $__n2 then false else true then if 0 < $__n2 then false else true else true
Obligation:
if 0 < $__n2 then $__s8 else 0 == $__n2 * ($__n2 + 1) / 2

---
info:
Obligation: sum_post_sum_ensures_1_calls_Int.SafeDiv_0
Property: assert
Result: ✅ pass

Obligation: loop_invariant_calls_Int.SafeDiv_0
Property: assert
Result: ✅ pass

Obligation: entry_invariant_0
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_0
Property: assert
Result: ✅ pass

Obligation: sum_ensures_1
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify gaussPgm

def nestedPgm :=
#strata
program Core;

const top : int;
axiom [top100]: top == 100;

procedure nested(n : int) returns (s : int)
spec {
  requires [n_pos]: n > 0;
  requires [n_lt_top]: n < top;
} {
  var x: int;
  var y: int;
  x := 0;
  while (x < n)
    invariant x >= 0
    invariant x <= n
    invariant n < top
  {
    y := 0;
    while (y < x)
      invariant y >= 0
      invariant y <= x
    {
      y := y + 1;
    }
    x := x + 1;
  }
};
#end

/--
info:
Obligation: entry_invariant_0
Property: assert
Result: ✅ pass

Obligation: entry_invariant_1
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_1
Property: assert
Result: ✅ pass

Obligation: arbitrary_iter_maintain_invariant_0
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify nestedPgm (options := .quiet)
