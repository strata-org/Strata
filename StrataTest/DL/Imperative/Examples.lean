/-
  Copyright Strata Contributors

  Licensed under the Apache License, Version 2.0 (the "License");
  you may not use this file except in compliance with the License.
  You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

  Unless required by applicable law or agreed to in writing, software
  distributed under the License is distributed on an "AS IS" BASIS,
  WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
  See the License for the specific language governing permissions and
  limitations under the License.
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
  assert [double_x_lemma]: (2 * x == x + x);
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
