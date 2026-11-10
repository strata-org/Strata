/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.InterpreterKleene
public import Strata.DL.Imperative.InterpreterConfigProps
import all Strata.DL.Imperative.InterpreterKleene
import all Strata.DL.Imperative.InterpreterConfig
import all Strata.DL.Imperative.KleeneStmtSemantics

/-! # Properties of `IKleeneConfig`

* `IKleeneConfig.getEnv_abs`, `IKleeneConfig.lvl_abs`, `IKleeneConfig.levelCmd?_abs` and the
  `abs_eq_*` inversions: accessors and shapes commute with `abs`;
* `StepKleeneE.lvl_defines`: a reference Kleene step grows the level store only by the names of
  the command it runs at that level, so the frame `ScopeFrame.record` records for it stays exact
  (`ScopeFrame.record_exact`). It is stated here and not in `KleeneSemanticsProps.lean`
  because its statement reads the interpreter's accessors `KleeneConfig.lvl` and
  `KleeneConfig.levelCmd?` and the interpreter hypothesis `CmdDefsSound`, as its structured
  counterpart `StepStmtE.lvl_defines` in `InterpreterConfigProps.lean` does. -/

namespace Imperative

public section

variable {P : PureExpr} [InterpLang P] {CmdT : Type}

/-- A configuration's leaf environment is that of the configuration it stands for. -/
@[simp] theorem IKleeneConfig.getEnv_abs [DecidableEq P.Ident] (c : IKleeneConfig P CmdT) :
    (c.abs F).getEnv = (c.getEnv.abs F) := by
  induction c <;> simp_all [IKleeneConfig.abs, IKleeneConfig.getEnv, KleeneConfig.getEnv]

/-- A configuration's leaf store is that of the configuration it stands for. -/
@[simp] theorem IKleeneConfig.getStore_abs [DecidableEq P.Ident] (c : IKleeneConfig P CmdT) :
    (c.abs F).getStore = InterpLang.absStore F c.getEnv.store.get := by
  induction c <;>
    simp_all [IKleeneConfig.abs, IKleeneConfig.getEnv, KleeneConfig.getStore, IEnv.abs]

/-- A configuration's level store is that of the configuration it stands for. -/
@[simp] theorem IKleeneConfig.lvl_abs [DecidableEq P.Ident] (c : IKleeneConfig P CmdT) :
    (c.abs F).lvl = InterpLang.absStore F c.lvl := by
  induction c <;> simp_all [IKleeneConfig.abs, IKleeneConfig.lvl, KleeneConfig.lvl, IEnv.abs]

/-- A configuration's level command is that of the configuration it stands for. -/
@[simp] theorem IKleeneConfig.levelCmd?_abs [DecidableEq P.Ident] (c : IKleeneConfig P CmdT) :
    (c.abs F).levelCmd? = c.levelCmd? := by
  induction c with
  | stmt s _ => cases s <;> rfl
  | seq _ _ ih => exact ih
  | _ => rfl

/-- A configuration stands for a terminal configuration exactly when it is that configuration. -/
@[simp] theorem IKleeneConfig.abs_eq_terminal [DecidableEq P.Ident] (c : IKleeneConfig P CmdT)
    (e : Env P) :
    (c.abs F) = .terminal e ↔ ∃ ie, c = .terminal ie ∧ (ie.abs F) = e := by
  cases c <;> simp [IKleeneConfig.abs]

/-- A configuration stands for a statement configuration exactly when it is that
    configuration. -/
@[simp] theorem IKleeneConfig.abs_eq_stmt [DecidableEq P.Ident] (c : IKleeneConfig P CmdT)
    (s : KleeneStmt P CmdT) (e : Env P) :
    (c.abs F) = .stmt s e ↔ ∃ ie, c = .stmt s ie ∧ (ie.abs F) = e := by
  cases c <;> simp [IKleeneConfig.abs, and_assoc]

/-- A configuration stands for a sequence context exactly when it is a sequence context whose
    inner configuration stands for the inner one. -/
theorem IKleeneConfig.abs_eq_seq [DecidableEq P.Ident] (c : IKleeneConfig P CmdT)
    (i : KleeneConfig P CmdT) (s : KleeneStmt P CmdT) :
    (c.abs F) = .seq i s ↔ ∃ ci, c = .seq ci s ∧ (ci.abs F) = i := by
  cases c <;> simp [IKleeneConfig.abs, and_assoc, and_comm]

/-- A configuration stands for a block context exactly when it is a block context whose frame
    has that parent store and whose inner configuration stands for the inner one. -/
theorem IKleeneConfig.abs_eq_block [DecidableEq P.Ident] (c : IKleeneConfig P CmdT)
    (σ : SemanticStore P) (i : KleeneConfig P CmdT) :
    (c.abs F) = .block σ i ↔ ∃ fr ci, c = .block fr ci ∧ InterpLang.absStore F fr.parent.get = σ ∧
        (ci.abs F) = i := by
  cases c <;> simp [IKleeneConfig.abs, and_assoc]


omit [InterpLang P] in
/-- A reference Kleene step from `c` to `c'` defines at `c`'s level only names of the command it
    runs at that level: every name `c'`'s level store defines is defined in `c`'s, or listed by
    `CmdDefs.defs` of `c`'s level command. -/
theorem StepKleeneE.lvl_defines [CmdDefs P CmdT] [HasBool P] [HasBoolOps P] {EventT : Type _}
    {EvalCmd : EvalCmdParamE P CmdT EventT} (hdefs : CmdDefsSound EvalCmd)
    {c c' : KleeneConfig P CmdT} {evs : List EventT} (h : StepKleeneE P EvalCmd c evs c') :
    ∀ x, (c'.lvl x).isSome →
      (c.lvl x).isSome ∨ ∃ cmd, c.levelCmd? = some cmd ∧ x ∈ CmdDefs.defs (P := P) cmd := by
  induction h with
  | step_cmd hc => exact fun x hx => (hdefs _ _ _ _ _ hc x hx).imp_right fun h => ⟨_, rfl, h⟩
  | step_seq_inner _ ih => exact ih
  | step_block_body _ _ => exact fun _ hx => .inl hx
  | _ =>
    exact fun _ hx => .inl (by simp_all [KleeneConfig.lvl, projectStore, Option.isSome_iff_ne_none])

end -- public section

end Imperative
