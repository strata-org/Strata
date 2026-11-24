/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Lean
public import Strata.Init

/-! # Shared proof automation for the counterexample-lifting layer

Key tactic: `cel_rr`. -/

/-- `simp only` with the given lemmas and the `ReplayM` run equations of `emit`/`choose`. -/
syntax "cel_rr" (" [" Lean.Parser.Tactic.simpLemma,* "]")? : tactic
set_option hygiene false in
macro_rules
  | `(tactic| cel_rr [$ls,*]) =>
    `(tactic| simp only [$ls,*, InterpEffects.emit, InterpEffects.choose, seqRight_eq_bind,
      replayM_run_read_bind, replayM_run_get_bind, replayM_run_modify_bind, replayM_run_pure,
      replayM_run_throw])
  | `(tactic| cel_rr) => `(tactic| cel_rr [seqRight_eq_bind])
