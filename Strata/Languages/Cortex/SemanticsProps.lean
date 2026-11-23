/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Cortex.Semantics

/-! # Properties of the Cortex relational semantics

## Key theorems

- `EvalIRCmd.factory_eq`: a command keeps the factory.
- `StepCortex.factory_eq`: a step keeps the factory, for a command relation that keeps it.
- `StepCortex.terminal_no_step`, `StepCortex.raised_no_step`: `terminal` and `raised`
  configurations have no step.
- `StepCortex.control_deterministic`: the control steps (fetch, jumps, `finish`, `close`)
  are deterministic.
- `StepCortex.imp`: the step relation is monotone in its command relation.
-/

namespace Cortex.Sem

open Imperative

public section

/-- A call keeps the factory of the caller's environment. -/
private theorem CallProc.factory_eq {Γ s lhs n args md s' o evs}
    (h : CallProc Γ s lhs n args md s' o evs) : s'.env.factory = s.env.factory := by
  cases h <;> rfl

/-- A Cortex command keeps the factory of the environment. -/
theorem EvalIRCmd.factory_eq {Γ s c s' o evs} (h : EvalIRCmd Γ s c s' o evs) :
    s'.env.factory = s.env.factory := by
  cases h with
  | call h => exact h.factory_eq
  | virtualCall _ _ h => exact h.factory_eq
  | _ => rfl

/-- A step keeps the factory of the configuration's environment, when every command step
keeps it. -/
theorem StepCortex.factory_eq {Γ EvalCmd c evs c'}
    (hE : ∀ s c s' o evs, EvalCmd s c s' o evs → s'.env.factory = s.env.factory)
    (h : StepCortex Γ EvalCmd c evs c') : c'.getEnv.factory = c.getEnv.factory := by
  cases h with
  | cmd_normal h | cmd_uncaught_throws h | cmd_uncaught_nothrows h => exact hE _ _ _ _ _ h
  | cmd_caught h => exact (hE _ _ _ _ _ h :)
  | _ => rfl

/-- A terminal configuration has no step. -/
theorem StepCortex.terminal_no_step {Γ EvalCmd ρ evs c'} :
    ¬ StepCortex Γ EvalCmd (.terminal ρ) evs c' := nofun

/-- A raised configuration has no step: it is the result of a body that ended with an
exception, which the calling procedure consumes, not a configuration the step relation
advances. -/
theorem StepCortex.raised_no_step {Γ EvalCmd s v evs c'} :
    ¬ StepCortex Γ EvalCmd (.raised s v) evs c' := nofun

/-- A configuration whose next step is a control step: not inside a block with a
command left. -/
@[expose] def CConfig.IsControl : CConfig → Prop
  | .inBlock _ _ (_ :: _) _ _ => False
  | _ => True

/-- The control steps are deterministic: from a configuration with no command left to
run, two steps emit the same events and reach the same configuration. -/
theorem StepCortex.control_deterministic {Γ EvalCmd c evs₁ c₁ evs₂ c₂}
    (hc : c.IsControl) (h₁ : StepCortex Γ EvalCmd c evs₁ c₁)
    (h₂ : StepCortex Γ EvalCmd c evs₂ c₂) : evs₁ = evs₂ ∧ c₁ = c₂ := by
  have hne := HasBool.ttVal_ne_ffVal (P := Core.Expression) c.getEnv.factory
  cases h₁ <;> cases h₂ <;> simp_all [CConfig.IsControl, CConfig.getEnv]

/-- The step relation is monotone in the command relation. -/
theorem StepCortex.imp {Γ} {E₁ E₂ : CState → IRCmd → CState → COutcome → List CEvent → Prop}
    (hE : ∀ s c s' o evs, E₁ s c s' o evs → E₂ s c s' o evs) {c evs c'}
    (h : StepCortex Γ E₁ c evs c') : StepCortex Γ E₂ c evs c' := by
  cases h with
  | fetch h => exact .fetch h
  | cmd_normal h => exact .cmd_normal (hE _ _ _ _ _ h)
  | cmd_caught h h1 h2 => exact .cmd_caught (hE _ _ _ _ _ h) h1 h2
  | cmd_uncaught_throws h h1 h2 h3 => exact .cmd_uncaught_throws (hE _ _ _ _ _ h) h1 h2 h3
  | cmd_uncaught_nothrows h h1 h2 h3 => exact .cmd_uncaught_nothrows (hE _ _ _ _ _ h) h1 h2 h3
  | goto_true h => exact .goto_true h
  | goto_false h => exact .goto_false h
  | finish => exact .finish
  | close => exact .close

end -- public section

end Cortex.Sem
