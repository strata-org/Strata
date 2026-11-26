/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.RecursiveFunctionAxiomsProps
public import Strata.Languages.Core.ProgramFactProps
import Strata.Languages.Core.ProgramProps

/-! # The facts `recursiveAxioms` keeps

Key results:

* `recursiveAxioms_keeps` — the phase keeps every fact that reads only procedures,
  `noPrecondsFromFuncs` and `noPolymorphicFunctions`; its contract rests on it. -/

namespace Core

public section

open Transform

/-- **`recursiveAxioms` keeps every fact that reads only procedures, `noPrecondsFromFuncs` and
    `noPolymorphicFunctions`.** -/
theorem recursiveAxioms_keeps {options : VerifyOptions} {f : ProgramFact}
    (hf : f.readsOnlyProcedures = true ∨ f = .noPrecondsFromFuncs ∨ f = .noPolymorphicFunctions)
    {p p' : Program} {s s' : CoreTransformState} {b : Bool}
    (hrun : (RecursiveAxioms.run options p).run s = (.ok (b, p'), s')) (hp : f.holds p) :
    f.holds p' := by
  obtain ⟨hprocs, hfuncs⟩ := recursiveAxioms_run hrun
  rcases hf with hf | rfl | rfl
  · exact ProgramFact.holds_of_procs_eq hf hprocs hp
  · simp only [ProgramFact.holds, Program.noFuncPreconditions_eq_funcsAll] at hp ⊢
    exact Program.funcsAll_of_funcs (hfuncs _ fun _ _ => rfl) hp
  · simp only [ProgramFact.holds, Program.noPolymorphicFunctions_eq_funcsAll] at hp ⊢
    exact Program.funcsAll_of_funcs (hfuncs _ fun _ _ => rfl) hp

end -- public section

end Core
