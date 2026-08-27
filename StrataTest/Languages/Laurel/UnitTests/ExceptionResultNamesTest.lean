/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module

/-
Pins the shared names of the injected exception-result datatype against the
definition itself.

`EliminateExceptions` builds the `Result` encoding of a throwing procedure's two
outcomes, and `ModifiesClauses` consumes it — guarding the normal frame with
`Result..isGood($result)` and the exceptional one with `Result..isBad($result)`.
Both reach it through the shared names in `LaurelAST` (`exnResultDatatypeName`
and friends), while the datatype itself is DDM source in
`CoreDefinitionsForLaurel`. Nothing in the type system ties those two together —
every spelling is just a `String` — so renaming a constructor in the definition
without mirroring it in the shared names would desync the passes with no build
failure at all. `resultDefinitionsMatchSharedNames` compares them, including the
tester and destructor names resolution derives from the datatype, and the guard
below fails the build when they drift.

The golden that follows it pins the concrete strings the datatype actually declares.
The boolean guard is what fails the build; the golden is what tells you *which* name
moved, since a rename that updates only one of the two sites would otherwise report
nothing beyond "guard failed".

The check lives here rather than beside the definition because evaluating it runs
the DDM parser, whose IR is not available to the interpreter while the `Strata`
library is still being compiled.
-/

meta import Strata.Languages.Laurel.CoreDefinitionsForLaurel

meta section

open Strata.Laurel

#guard resultDefinitionsMatchSharedNames

/-- info: datatype: Result
constructors: Good, Bad
fields: value, err
testers: Result..isGood, Result..isBad
destructors: Result..value, Result..err -/
#guard_msgs in
#eval resultDefinitionNames.forM fun (entry : String × String) =>
  IO.println s!"{entry.fst}: {entry.snd}"

end
