/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Laurel.Grammar.LaurelParser
import Strata.Languages.Laurel.Translator

namespace Laurel

open Laurel.Parser

def testAssertFalse : IO Unit := do
  let content <- IO.FS.readFile "Strata/Languages/Laurel/Examples/Fundamentals/AssertFalse.lr.st"

  match parseProgram content with
  | Except.error err =>
    IO.println s!"Parse failed: {err}"
  | Except.ok prog =>
    IO.println "Parse succeeded"
    let results <- verify "cvc5" prog
    IO.println s!"{results}"

/--
info: Parse succeeded
[Strata.Boogie] Type checking succeeded.


VCs:
Label: assert
Assumptions:


Proof Obligation:
#true

Label: assert
Assumptions:


Proof Obligation:
#false

Label: assert
Assumptions:


Proof Obligation:
#false

Label: assert
Assumptions:
(assume, #false)

Proof Obligation:
#true

Wrote problem to vcs/assert.smt2.


Obligation assert: could not be proved!

Result: failed
CEx: ⏎

Evaluated program:
(procedure foo :  () → ())
modifies: []
preconditions: ⏎
postconditions: ⏎
body: assert [assert] #true
assert [assert] #false
assert [assert] #false

(procedure bar :  () → ())
modifies: []
preconditions: ⏎
postconditions: ⏎
body: assume [assume] #false
assert [assert] #true

Wrote problem to vcs/assert.smt2.


Obligation assert: could not be proved!

Result: failed
CEx: ⏎

Evaluated program:
(procedure foo :  () → ())
modifies: []
preconditions: ⏎
postconditions: ⏎
body: assert [assert] #true
assert [assert] #false
assert [assert] #false

(procedure bar :  () → ())
modifies: []
preconditions: ⏎
postconditions: ⏎
body: assume [assume] #false
assert [assert] #true


Obligation: assert
Result: verified

Obligation: assert
Result: failed
CEx: ⏎

Obligation: assert
Result: failed
CEx: ⏎

Obligation: assert
Result: verified
-/
#guard_msgs in
#eval! testAssertFalse

end Laurel
