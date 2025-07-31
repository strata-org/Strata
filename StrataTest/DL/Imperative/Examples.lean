/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.DL.Imperative.Verify

---------------------------------------------------------------------
namespace Strata

---------------------------------------------------------------------
def testProgram1 : Environment :=
#strata
program ArithPrograms;
  init x : num := 0;
  x := 1;
  havoc x;
  assert [x_eq_1]: (x == 1); // error
#end

/--
info: Wrote problem to vcs/x_eq_1.smt2.


Obligation x_eq_1: could not be proved!

Result: failed
Counterexample: (($__x0, Num), 0)
---
info:
Obligation: x_eq_1
Result: failed
Counterexample: (($__x0, Num), 0)
-/
#guard_msgs in
#eval Strata.ArithPrograms.verify "cvc5" testProgram1

---------------------------------------------------------------------

def testProgram2 : Environment :=
#strata
program ArithPrograms;
  init x : num := 0;
  x := 1;
  init y : num := 0;
  assert [x_eq_y]: (x == (y + 1 * 1));
#end

/--
info:
Obligation x_eq_y proved via evaluation!

---
info:
-/
#guard_msgs in
#eval Strata.ArithPrograms.verify "cvc5" testProgram2

---------------------------------------------------------------------

def testProgram3 : Environment :=
#strata
program ArithPrograms;
  var x : num;
  var b : bool;
  b := (2 * x == x + x);
  assert [double_x_lemma]: (b);
#end

/--
info: Wrote problem to vcs/double_x_lemma.smt2.
---
info:
Obligation: double_x_lemma
Result: verified
-/
#guard_msgs in
#eval Strata.ArithPrograms.verify "cvc5" testProgram3

---------------------------------------------------------------------
