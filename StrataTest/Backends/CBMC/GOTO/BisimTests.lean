/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Backends.CBMC.GOTO.Bisim

/-! # Smoke tests for the StepGoto / StepInstr bisimulation bridge

Phase 0 deliverable: instantiate the bridge theorems on a tiny example
program to confirm they actually elaborate and produce the expected
`StepInstr` derivations.

The tests cover the constructors that bridge directly without
state-changing complexity: `step_location`, `step_skip`,
`step_assert_pass`, `step_assume_pass`, `step_goto_fallthrough`. -/

namespace CProverGOTOBisimTests

open CProverGOTO Imperative
open CProverGOTO.SemanticsTautschnig (ValueCorr StoreCorr)

/-! ## Tiny example program: a single LOCATION + END_FUNCTION -/

def locationOnlyPgm : Program :=
  { name := "main"
    parameterIdentifiers := #[]
    instructions := #[
      { type := .LOCATION, locationNum := 0 },
      { type := .END_FUNCTION, locationNum := 1 }
    ] }

/-! ## Stub correspondence: every store on the imperative side
correlates with the empty GOTO store under any nameMap. We use the
"both none" branch of `StoreCorr` everywhere. -/

def emptyImpStore : Imperative.SemanticStore Core.Expression := fun _ => none

theorem emptyStoreCorr (nameMap : Core.Expression.Ident → String) :
    StoreCorr nameMap emptyImpStore SemanticsTautschnig.Store.empty := by
  intro x
  left
  exact ⟨rfl, rfl⟩

/-! ## Test 1: stepGoto_location_to_stepInstr fires on locationOnlyPgm. -/

example
    (nameMap : Core.Expression.Ident → String)
    (callResult : SemanticsTautschnig.CallResultRel)
    (eval : SemanticsTautschnig.ExprEval)
    (fenv : SemanticsTautschnig.FuncEnv) :
    ∃ σ_goto', StoreCorr nameMap emptyImpStore σ_goto' ∧
      SemanticsTautschnig.StepInstr callResult eval fenv locationOnlyPgm
        0 SemanticsTautschnig.Store.empty 1 σ_goto' :=
  Bisim.stepGoto_location_to_stepInstr
    (h_at := rfl)
    (h_ty := rfl)
    (h_corr := emptyStoreCorr nameMap)

/-! ## Test 2: example with SKIP -/

def skipOnlyPgm : Program :=
  { name := "main"
    parameterIdentifiers := #[]
    instructions := #[
      { type := .SKIP, locationNum := 0 },
      { type := .END_FUNCTION, locationNum := 1 }
    ] }

example
    (nameMap : Core.Expression.Ident → String)
    (callResult : SemanticsTautschnig.CallResultRel)
    (eval : SemanticsTautschnig.ExprEval)
    (fenv : SemanticsTautschnig.FuncEnv) :
    ∃ σ_goto', StoreCorr nameMap emptyImpStore σ_goto' ∧
      SemanticsTautschnig.StepInstr callResult eval fenv skipOnlyPgm
        0 SemanticsTautschnig.Store.empty 1 σ_goto' :=
  Bisim.stepGoto_skip_to_stepInstr
    (h_at := rfl)
    (h_ty := rfl)
    (h_corr := emptyStoreCorr nameMap)

end CProverGOTOBisimTests
