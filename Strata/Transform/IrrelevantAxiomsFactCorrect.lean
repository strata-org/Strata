/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.IrrelevantAxiomsProps
public import Strata.Languages.Core.ProgramFactProps

/-! # The facts `removeIrrelevantAxioms` keeps

Key results:

* `irrelevantAxioms_keeps` — the phase keeps every fact but `noLambdas`, which it does not
  claim: it drops only declarations other than procedures. -/

namespace Core

public section

/-- **`removeIrrelevantAxioms` keeps every fact but `noLambdas`.** -/
theorem irrelevantAxioms_keeps {functions : List String} {f : ProgramFact}
    (hl : f ≠ .noLambdas) {p p' : Program}
    {s s' : Transform.CoreTransformState} {b : Bool}
    (hrun : (irrelevantAxiomsTransform functions p).run s = (.ok (b, p'), s'))
    (hp : f.holds p) : f.holds p' :=
  let ⟨hprocs, hsub⟩ := irrelevantAxiomsTransform_run hrun
  ProgramFact.holds_of_procs_eq_of_subset hl hprocs hsub hp

end -- public section

end Core
