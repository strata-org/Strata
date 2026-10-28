/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Resolving an already resolved program again rebuilds the same model: it allocates no ids and
binds every id to the same kind of node, with no new diagnostics. The pipeline relies on this
to skip the re-resolve after a pass that leaves the program as it was last resolved
(`runLaurelPasses`). Each case declares one kind of name whose id resolution does not write
back itself, so it would be allocated afresh by every resolution unless kept elsewhere.
-/

import StrataLaurel.Tests.Util.TestLaurel
import StrataLaurel.Implementation.Resolution

open Strata

namespace Strata.Laurel

/-- Each id with the kind of node it is bound to, in id order. -/
private def bindings (m : SemanticModel) : List (Nat × String) :=
  (m.refToDef.toList.map fun (id, node) => (id, s!"{repr node.kind}")).mergeSort (·.1 <= ·.1)

/-- How many ids a second resolution of `src` allocates, whether it binds them as the first
    did, and how many errors each reports. -/
private def report (name src : String) : IO Unit := do
  let parsed ← (Strata.parseLaurelText "<reresolution-ids-test>" src : IO LaurelProgram)
  let first := resolve parsed
  let second := resolve first.program (some first.model)
  let same := bindings second.model == bindings first.model
  IO.println s!"{name}: {second.model.nextId - first.model.nextId} new ids, \
    same bindings: {same}, errors: {first.errors.size}, {second.errors.size}"

/--
info: datatype tester and type parameter: 0 new ids, same bindings: true, errors: 0, 0
alias type parameters: 0 new ids, same bindings: true, errors: 0, 0
opaque type parameter: 0 new ids, same bindings: true, errors: 0, 0
throws binder: 0 new ids, same bindings: true, errors: 0, 0
-/
#guard_msgs in
#eval do
  report "datatype tester and type parameter" r"
datatype Opt<T> { None(), Some(v: T) }
"
  report "alias type parameters" r"
type Pair<A, B> = TotalMap A B
"
  report "opaque type parameter" r"
opaque Bag<T>
"
  report "throws binder" r"
composite Exception {}
procedure p() throws (e: Exception) opaque
  throwsOn true { ensures e is Exception };
"

end Strata.Laurel
