/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/


import Strata.Languages.Core.Verifier

---------------------------------------------------------------------
open Strata

private def mapPgm :=
#strata
program Core;

procedure first(x : int) returns (r : int)
spec { ensures [post]: (r >= 0); }
{
  body: {
    if (x < 0) { r := 0 - x; exit body; }
    r := x;
    exit body;
  }
};

procedure second() returns ()
  { assert [a]: true; };
#end

/--
info: [Strata.Core] Type checking succeeded.


VCs:
Label: post
Property: assert
Assumptions:
<label_ite_cond_true: (~Int.Lt x #0)>: $__x0 < 0
Obligation:
0 - $__x0 >= 0

Label: a
Property: assert
Obligation:
true

Label: post
Property: assert
Assumptions:
<label_ite_cond_false: !(~Int.Lt x #0)>: if $__x0 < 0 then false else true
Obligation:
$__x0 >= 0

Label: a
Property: assert
Obligation:
true

---
info:
Obligation: post
Property: assert
Result: ✅ pass

Obligation: a
Property: assert
Result: ✅ pass

Obligation: post
Property: assert
Result: ✅ pass

Obligation: a
Property: assert
Result: ✅ pass
-/
#guard_msgs in
#eval verify mapPgm
