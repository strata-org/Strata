/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.ConfigWF
import all Strata.Languages.Core.ConfigWF
import Strata.Languages.Core.InterpreterReplayTactics

/-! # Properties of the Core configuration well-formedness conditions

Lemmas about the definitions of `Core/ConfigWF.lean`.

Key theorems:
* `StoreClosed.update`, `StoreClosed.empty`: closed stores are preserved by closed updates, and
  the empty store is closed.
* `cfgWF_stmts`, `cfgWF_stmt`, `CfgWF.getEnv`: a configuration's well-formedness and that of its
  active environment.
* `cfgWF_wrapSeqs`, `cfgWF_unseqs`: wrapping a configuration in sequence contexts, and expanding
  its sequence towers, keep and reflect its well-formedness. -/

namespace Core
open Imperative
public section

/-- A closed store stays closed after an update with a closed value. -/
theorem StoreClosed.update {σ : RStore Expression} (h : StoreClosed σ)
    (x : Expression.Ident) {v : Expression.Expr} (hv : Lambda.LExpr.LExpr.getVars v = []) :
    StoreClosed (RStore.update σ x v) := by grind [StoreClosed, RStore.update]

/-- The empty store is closed. -/
theorem StoreClosed.empty : StoreClosed (fun _ => none) := nofun

/-- A top-level configuration is well-formed exactly when its environment is. -/
@[simp] theorem cfgWF_stmts {CmdT : Type} (ss : List (Stmt Expression CmdT))
    (ρ : Imperative.IEnv Expression) : CfgWF (.stmts ss ρ) ↔ EnvWF ρ := .rfl

/-- A single-statement configuration is well-formed exactly when its environment is. -/
@[simp] theorem cfgWF_stmt {CmdT : Type} (s : Stmt Expression CmdT)
    (ρ : Imperative.IEnv Expression) : CfgWF (.stmt s ρ) ↔ EnvWF ρ := .rfl

/-- The active environment of a well-formed configuration is well-formed. -/
theorem CfgWF.getEnv {CmdT : Type} :
    ∀ {c : IConfig Expression CmdT}, CfgWF c → EnvWF c.getEnv := by
  intro c
  induction c <;> simp_all!

/-- A configuration under `k` sequence contexts with no remaining statements is well-formed
    (`CfgWF`) exactly when the configuration itself is. -/
theorem cfgWF_wrapSeqs {CmdT : Type} (c : IConfig Expression CmdT) (k : Nat) :
    CfgWF (c.wrapSeqs k) ↔ CfgWF c := by
  induction k <;> simp_all [IConfig.wrapSeqs, CfgWF]

/-- Expanding the sequence towers of a configuration (`IConfig.unseqs`) keeps it well-formed
    (`CfgWF`), and reflects it. -/
theorem cfgWF_unseqs {CmdT : Type} (c : IConfig Expression CmdT) : CfgWF c.unseqs ↔ CfgWF c := by
  induction c <;> simp_all [IConfig.unseqs, CfgWF, cfgWF_wrapSeqs]

end
end Core
