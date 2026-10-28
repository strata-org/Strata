/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public meta import Strata.Languages.Core

meta section

public section

namespace Core.RemoveIrrelevantDatatypes.TestUtils

/-- Print how many of `pgms` the verifier reports on identically with and
    without `removeIrrelevantDatatypes`, then each one that differs. Each
    program runs with axiom pruning off and with directed axiom pruning, which
    drops axioms and so lets the flag drop the datatypes only they use. A
    query that leaves out a datatype it uses makes the solver reject an unknown
    sort, so its result differs. -/
def sameWithFlag (pgms : List StrataDDM.Program) : IO Unit := do
  let mut same := 0
  for (pgm, i) in pgms.zipIdx do
    let mut agrees := true
    for mode in [.Off, .Directed] do
      let base := { Core.VerifyOptions.quiet with
        removeIrrelevantAxioms := mode }
      let off ← Strata.Core.verify pgm (options := base)
      let on ← Strata.Core.verify pgm (options :=
        { base with removeIrrelevantDatatypes := true })
      if toString off != toString on then
        agrees := false
        IO.println s!"program {i} differs:\n{off}\n{on}"
    if agrees then same := same + 1
  IO.println s!"{same} of {pgms.length} the same"

end Core.RemoveIrrelevantDatatypes.TestUtils

end -- public section
end
