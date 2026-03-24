/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestDiagnostics
import StrataTest.Languages.Laurel.TestExamples

open StrataTest.Util
open Strata

namespace Strata.Laurel

def program := r#"
// abs returns the absolute value of x.
// The invokeOn trigger fires whenever abs(x) appears in the SMT context,
// automatically instantiating the axiom: abs(x) >= 0.
function abs(x: int): int {
  if x >= 0 then x else -x
};

procedure abs_nonneg(x: int)
  invokeOn abs(x)
  ensures abs(x) >= 0;

// The axiom fires because abs(n) appears in the goal.
procedure useAbsAxiom(n: int) {
  assert abs(n) >= 0
};

// The axiom fires for a concrete expression too.
procedure useAbsAxiomConcrete() {
  assert abs(-5) >= 0
};

// Without the axiom, a false claim about abs should fail.
procedure wrongAbsClaim(n: int) {
  assert abs(n) < 0
//^^^^^^^^^^^^^^^^^ error: assertion does not hold
};

// double_abs: abs(abs(x)) == abs(x).
// The invokeOn trigger is abs(abs(x)), so the axiom fires when that
// exact pattern appears, giving us abs(abs(x)) >= 0 for free.
procedure abs_abs_nonneg(x: int)
  invokeOn abs(abs(x))
  ensures abs(abs(x)) >= 0;

procedure useAbsAbsAxiom(n: int) {
  assert abs(abs(n)) >= 0
};

// A procedure with multiple parameters: invokeOn fires on max(a, b).
function max(a: int, b: int): int {
  if a >= b then a else b
};

procedure max_ge_left(a: int, b: int)
  invokeOn max(a, b)
  ensures max(a, b) >= a;

procedure max_ge_right(a: int, b: int)
  invokeOn max(a, b)
  ensures max(a, b) >= b;

// Both axioms fire because max(x, y) appears in the goal.
procedure useMaxAxioms(x: int, y: int) {
  assert max(x, y) >= x;
  assert max(x, y) >= y
};

// A wrong claim about max should fail even with the axiom.
procedure wrongMaxClaim(x: int, y: int) {
  assert max(x, y) == x
//^^^^^^^^^^^^^^^^^^^^^ error: assertion does not hold
};
"#

#guard_msgs (drop info, error) in
#eval testInputWithOffset "InvokeOn" program 14 processLaurelFile

end Strata.Laurel
