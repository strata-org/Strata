/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Increment/decrement (`++`/`--`) is only lowered for `int` and int-based
constrained types (e.g. `nat`). Applying it to `bv`, `real`, or `float64`
is rejected during resolution with a clear Laurel diagnostic (and a source
range), rather than leaking a raw Core unification error from a later pass.

This file also pins the positive case: `++`/`--` on an int-based constrained
type verifies end-to-end.
-/

import StrataTest.Util.TestLaurel

open StrataTest.Util
open Strata

/-! ## Rejected: `++`/`--` on unsupported element types -/

#guard_msgs (drop info) in
#eval testLaurelResolution <|
#strata
program Laurel;
procedure incrBv(y: bv 32) opaque {
  var x: bv 32 := y;
  x++
//^^^ error: only supported on 'int' and int-based constrained types
};
procedure decrReal() opaque {
  var r: real := 1.0;
  r--
//^^^ error: only supported on 'int' and int-based constrained types
};
procedure incrFloat(g: float64) opaque {
  var f: float64 := g;
  f++
//^^^ error: only supported on 'int' and int-based constrained types
};
#end

/-! ## Accepted: `++`/`--` on an int-based constrained type (e.g. `nat`) -/

#guard_msgs (drop info) in
#eval testLaurel <|
#strata
program Laurel;
constrained nat = v: int where v >= 0 witness 0
procedure incrNat() opaque {
  var n: nat := 0;
  n++;
  assert n == 1
};
#end
