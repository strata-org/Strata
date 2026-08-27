/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.CFGSemantics
public import Strata.DL.Imperative.StmtSemanticsProps
import all Strata.DL.Imperative.Cmd

public section

namespace Imperative

/-! # CFG small-step semantics: properties

Property lemmas about `StepCFG`/`StepCFGStar` and the `EvalCmds` command-replay
bridge, kept separate from any single transform's correctness proof so they can
be reused by any CFG client.

Key theorems:
  * `StepCFG.deterministic` — one-step determinism of `StepCFG`.
  * `StepDetCFGStar_trans` — transitivity of the deterministic-CFG multi-step run.
  * `EvalCmds_prefix_to_StepCFG_chain` / `EvalCmds_to_StepCFG_chain` — lift an
    `EvalCmds` command-replay into a `StepCFG` chain.
  * `EvalCmd_under_agreement` / `EvalCmds_under_agreement` — command evaluation is
    preserved under `StoreAgreement`.
  * `agreement_helper_unchanged_at_x_multi` — agreement is unchanged off the
    written variables across a command list.
  * `single_cmd_eval` — single-command evaluation into a one-step CFG run.
  * `run_block_goto` — run a deterministic block from `.atBlock` to the selected
    successor of a `condGoto` (the `Bool` index selects the branch).
  * `run_block_finish` — run a deterministic block to its `finish` terminal.
    (Reusable CFG-simulation building blocks consumed by the S2U proof.) -/

/-- `StepCFG` is deterministic: from a single source config, at most one target
    is reachable in one step.  The `fac` index (fixed across the relation) pins
    each `condGoto` condition to one value, so `goto_true` and `goto_false` cannot
    both fire; `fetch`/`finish` are structurally functional and `step_cmd` inherits
    determinism from `EvalCmd` (`hcmd`).  This machine-checks the determinism the
    `StepCFG` docstring claims, guarding against a later constructor addition
    silently reintroducing nondeterminism. -/
theorem StepCFG.deterministic
    {l CmdT : Type} [BEq l] {P : PureExpr} {EvalCmd : EvalCmdParam P CmdT}
    {extendFactory : ExtendFactory P} {fac : P.Factory}
    [HasBool P] [HasBoolOps P] [HasVal P] [HasFvars P]
    {cfg : CFG l (DetBlock l CmdT P)} {s t₁ t₂ : CFGConfig l CmdT P}
    (hcmd : ∀ σ c σ₁ f₁ σ₂ f₂,
      EvalCmd fac σ c σ₁ f₁ → EvalCmd fac σ c σ₂ f₂ → σ₁ = σ₂ ∧ f₁ = f₂)
    (h₁ : StepCFG P EvalCmd extendFactory fac cfg s t₁)
    (h₂ : StepCFG P EvalCmd extendFactory fac cfg s t₂) :
    t₁ = t₂ := by
  cases h₁ <;> cases h₂ <;> first | rfl | skip
  case fetch.fetch hlk₁ _ hlk₂ =>
    -- `List.lookup` is functional: the two fetched blocks agree.
    obtain rfl : _ = _ := Option.some.inj (hlk₁.symm.trans hlk₂); rfl
  case step_cmd.step_cmd he₁ _ _ he₂ =>
    -- `EvalCmd` is deterministic (`hcmd`): resulting store and flag are unique.
    obtain ⟨hσ, hf⟩ := hcmd _ _ _ _ _ _ he₁ he₂; rw [hσ, hf]
  case goto_true.goto_false htt _ _ _ _ hff =>
    -- `fac` pins the condition, so `tt = ff` — impossible.
    exact absurd (htt.symm.trans hff) (by simp [HasBool.tt_is_not_ff])
  case goto_false.goto_true hff _ _ _ _ htt =>
    exact absurd (htt.symm.trans hff) (by simp [HasBool.tt_is_not_ff])

/-- Store-agreement transport through a `.block`-step projection, tolerant of
factory restoration: the outer env's factory field may be restored to any parent
factory `f` (as it is by `step_block_done`/`step_block_exit_match` in mainline),
since store agreement only depends on the store field.  Given a record-update
equality showing the outer store is the projection of the inner store, and an
agreement between the inner store and a CFG store, derive agreement between the
outer store and the CFG store. -/
theorem storeAgreement_through_projectStore' {P : PureExpr}
    {σ_parent : SemanticStore P} {ρ_inner ρ_blk : Env P} {f : P.Factory}
    {σ_cfg : SemanticStore P}
    (h_ρ_blk_eq : ρ_blk = { ρ_inner with store := projectStore σ_parent ρ_inner.store, factory := f })
    (h_agree_body : StoreAgreement ρ_inner.store σ_cfg) :
    StoreAgreement ρ_blk.store σ_cfg := by
  have h_store : ρ_blk.store = projectStore σ_parent ρ_inner.store := by rw [h_ρ_blk_eq]
  rw [h_store]
  exact StoreAgreement.trans (StoreAgreement.of_projectStore _ _) h_agree_body

/-- Prefix bridge: lift an `EvalCmds` derivation for a *prefix* `pre` into a chain
of `StepCFG.step_cmd` steps inside `.inBlock t (pre ++ suf) ...`, consuming exactly
`pre` and leaving the suffix `suf` residual.  The step rule consumes the head
command regardless of what follows, so the same chain that runs a standalone
`pre` runs it as the leading commands of `pre ++ suf`. -/
theorem EvalCmds_prefix_to_StepCFG_chain {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    {extendFactory : ExtendFactory P}
    {cfg : CFG String (DetBlock String (Cmd P) P)}
    {δ : P.Factory} {σ σ' : SemanticStore P}
    {pre suf : List (Cmd P)} {f : Bool}
    (h_cmds : EvalCmds P (EvalCmd P) δ σ pre σ' f) :
    ∀ (t : String) (tr : DetTransferCmd String P) (f_base : Bool),
      StepCFGStar P (EvalCmd P) extendFactory δ cfg
        (.inBlock t (pre ++ suf) tr σ f_base)
        (.inBlock t suf tr σ' (f_base || f)) := by
  induction h_cmds with
  | eval_cmds_none =>
    intro t tr f_base
    rw [Bool.or_false]
    exact ReflTrans.refl _
  | eval_cmds_some hcmd hcmds ih =>
    rename_i δ' σ_in c σ_mid failed cs_t σ_out f_t
    intro t tr f_base
    have h1 : StepCFG (l := String) (CmdT := Cmd P) P (EvalCmd P) extendFactory δ cfg
        (.inBlock t ((c :: cs_t) ++ suf) tr σ_in f_base)
        (.inBlock t (cs_t ++ suf) tr σ_mid (f_base || failed)) :=
      StepCFG.step_cmd (extendFactory := extendFactory) hcmd
    have h2 := ih t tr (f_base || failed)
    have h_or :
        ((f_base || failed) || f_t) = (f_base || (failed || f_t)) :=
      Bool.or_assoc _ _ _
    rw [h_or] at h2
    exact ReflTrans.step _ _ _ h1 h2

/-- Bridge: lift an `EvalCmds` derivation for the command list `cs` into a
chain of `StepCFG.step_cmd` steps inside `.inBlock`, threading the residual
list and accumulating failure on the right via `||`. -/
theorem EvalCmds_to_StepCFG_chain {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    {extendFactory : ExtendFactory P}
    {cfg : CFG String (DetBlock String (Cmd P) P)}
    {δ : P.Factory} {σ σ' : SemanticStore P}
    {cs : List (Cmd P)} {f : Bool}
    (h_cmds : EvalCmds P (EvalCmd P) δ σ cs σ' f) :
    ∀ (t : String) (tr : DetTransferCmd String P) (f_base : Bool),
      StepCFGStar P (EvalCmd P) extendFactory δ cfg
        (.inBlock t cs tr σ f_base)
        (.inBlock t [] tr σ' (f_base || f)) := by
  intro t tr f_base
  simpa using
    EvalCmds_prefix_to_StepCFG_chain (extendFactory := extendFactory) (cfg := cfg)
      (suf := []) h_cmds t tr f_base

theorem EvalCmds_snoc {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    (δ : P.Factory) (σ σ' σ'' : SemanticStore P)
    (cs : List (Cmd P)) (c : Cmd P) (f₁ f₂ : Bool)
    (h₁ : EvalCmds P (EvalCmd P) δ σ cs σ' f₁)
    (h₂ : EvalCmd P δ σ' c σ'' f₂) :
    EvalCmds P (EvalCmd P) δ σ (cs ++ [c]) σ'' (f₁ || f₂) := by
  induction cs generalizing σ f₁ with
  | nil =>
    cases h₁
    simp
    have : f₂ = (f₂ || false) := by simp
    rw [this]
    exact EvalCmds.eval_cmds_some h₂ EvalCmds.eval_cmds_none
  | cons c' cs' ih =>
    cases h₁ with
    | eval_cmds_some hcmd hrest =>
      simp only [List.cons_append]
      rw [Bool.or_assoc]
      exact EvalCmds.eval_cmds_some hcmd (ih _ _ hrest)

theorem EvalCmds_inv {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    (δ : P.Factory) (σ σ' : SemanticStore P) (f : Bool)
    (h : EvalCmds P (EvalCmd P) δ σ [] σ' f) :
    σ = σ' ∧ f = false := by
  cases h;
  exact ⟨ rfl, rfl ⟩

/-- Single-command agreement-preservation. -/
theorem EvalCmd_under_agreement {P : PureExpr}
    [HasFvar P] [HasFvars P] [HasBoolOps P] [DecidableEq P.Ident]
    (δ : P.Factory) (σ_struct₀ σ_cfg₀ : SemanticStore P)
    (c : Cmd P) (σ_struct₁ : SemanticStore P) (failed : Bool)
    (h_agree : StoreAgreement σ_struct₀ σ_cfg₀)
    (h_eval : EvalCmd P δ σ_struct₀ c σ_struct₁ failed)
    (h_wf_def : WellFormedSemanticEvalMono δ)
    (h_fresh : ∀ x ∈ Cmd.definedVars c, σ_cfg₀ x = none) :
    ∃ σ_cfg₁, EvalCmd P δ σ_cfg₀ c σ_cfg₁ failed
            ∧ StoreAgreement σ_struct₁ σ_cfg₁ := by
  cases h_eval with
  | eval_init heval hinit hwfvar =>
    -- Constructor: EvalCmd δ σ_struct₀ (.init x ty (.det e) md) σ_struct₁ false
    -- rename_i introduces in order: ty, md, x, v, e
    rename_i ty md e v x
    -- Need δ σ_cfg₀ e = some v. Use congr + agreement on e's vars.
    have h_eval_cfg : P.eval δ σ_cfg₀ e = .some v :=
      h_wf_def e v σ_struct₀ σ_cfg₀
        (storeAgreement_supplies_mono_premise σ_struct₀ σ_cfg₀ h_agree) heval
    -- Witness σ_cfg₁
    let σ_cfg₁ : SemanticStore P := fun y => if y = x then some v else σ_cfg₀ y
    have h_x_fresh : σ_cfg₀ x = none := by
      apply h_fresh x
      have h_dv_eq : Cmd.definedVars (Cmd.init x ty (ExprOrNondet.det e) md) = [x] := by
        with_unfolding_all rfl
      rw [h_dv_eq]
      exact List.mem_cons_self
    have h_cfg_x : σ_cfg₁ x = some v := by
      show (if x = x then some v else σ_cfg₀ x) = some v
      simp
    have h_cfg_other : ∀ y, x ≠ y → σ_cfg₁ y = σ_cfg₀ y := by
      intro y hxy
      show (if y = x then some v else σ_cfg₀ y) = σ_cfg₀ y
      have hne : ¬ (y = x) := fun h => hxy h.symm
      rw [if_neg hne]
    have h_init_cfg : InitState P σ_cfg₀ x v σ_cfg₁ :=
      InitState.init h_x_fresh h_cfg_x h_cfg_other
    refine ⟨σ_cfg₁, EvalCmd.eval_init h_eval_cfg h_init_cfg hwfvar, ?_⟩
    -- StoreAgreement σ_struct₁ σ_cfg₁
    intro y h_def_y
    cases hinit with
    | init h_xn h_xv h_other =>
      by_cases hyx : y = x
      · subst hyx
        rw [h_xv, h_cfg_x]
      · have h_struct_y : σ_struct₁ y = σ_struct₀ y := h_other y (fun h => hyx h.symm)
        have h_cfg_y : σ_cfg₁ y = σ_cfg₀ y := h_cfg_other y (fun h => hyx h.symm)
        rw [h_struct_y, h_cfg_y]
        have h_def_y' : isDefined σ_struct₀ [y] := by
          intro w hw
          rw [List.mem_singleton] at hw
          rw [hw]
          have h_y_def_in_σ' : (σ_struct₁ y).isSome = true :=
            h_def_y y (List.mem_singleton.mpr rfl)
          exact h_struct_y ▸ h_y_def_in_σ'
        exact h_agree y h_def_y'
  | eval_init_unconstrained hinit hval hwfvar =>
    rename_i ty md x v
    let σ_cfg₁ : SemanticStore P := fun y => if y = x then some v else σ_cfg₀ y
    have h_x_fresh : σ_cfg₀ x = none := by
      apply h_fresh x
      have h_dv_eq : Cmd.definedVars (Cmd.init x ty ExprOrNondet.nondet md) = [x] := by
        with_unfolding_all rfl
      rw [h_dv_eq]
      exact List.mem_cons_self
    have h_cfg_x : σ_cfg₁ x = some v := by
      show (if x = x then some v else σ_cfg₀ x) = some v
      simp
    have h_cfg_other : ∀ y, x ≠ y → σ_cfg₁ y = σ_cfg₀ y := by
      intro y hxy
      show (if y = x then some v else σ_cfg₀ y) = σ_cfg₀ y
      have hne : ¬ (y = x) := fun h => hxy h.symm
      rw [if_neg hne]
    have h_init_cfg : InitState P σ_cfg₀ x v σ_cfg₁ :=
      InitState.init h_x_fresh h_cfg_x h_cfg_other
    refine ⟨σ_cfg₁, EvalCmd.eval_init_unconstrained h_init_cfg hval hwfvar, ?_⟩
    intro y h_def_y
    cases hinit with
    | init h_xn h_xv h_other =>
      by_cases hyx : y = x
      · subst hyx
        rw [h_xv, h_cfg_x]
      · have h_struct_y : σ_struct₁ y = σ_struct₀ y := h_other y (fun h => hyx h.symm)
        have h_cfg_y : σ_cfg₁ y = σ_cfg₀ y := h_cfg_other y (fun h => hyx h.symm)
        rw [h_struct_y, h_cfg_y]
        have h_def_y' : isDefined σ_struct₀ [y] := by
          intro w hw
          rw [List.mem_singleton] at hw
          rw [hw]
          have h_y_def_in_σ' : (σ_struct₁ y).isSome = true :=
            h_def_y y (List.mem_singleton.mpr rfl)
          exact h_struct_y ▸ h_y_def_in_σ'
        exact h_agree y h_def_y'
  | eval_set heval hupdate hwfvar =>
    rename_i md e v x
    have h_eval_cfg : P.eval δ σ_cfg₀ e = .some v :=
      h_wf_def e v σ_struct₀ σ_cfg₀
        (storeAgreement_supplies_mono_premise σ_struct₀ σ_cfg₀ h_agree) heval
    cases hupdate with
    | update h_xv' h_xv h_other =>
      rename_i v'
      have h_x_def_struct : isDefined σ_struct₀ [x] := by
        intro y hy
        rw [List.mem_singleton] at hy
        rw [hy, h_xv']
        rfl
      have h_cfg_x_old : σ_cfg₀ x = some v' := by
        have h_eq : σ_struct₀ x = σ_cfg₀ x := h_agree x h_x_def_struct
        rw [← h_eq]; exact h_xv'
      let σ_cfg₁ : SemanticStore P := fun y => if y = x then some v else σ_cfg₀ y
      have h_cfg_x_new : σ_cfg₁ x = some v := by
        show (if x = x then some v else σ_cfg₀ x) = some v
        simp
      have h_cfg_other : ∀ y, x ≠ y → σ_cfg₁ y = σ_cfg₀ y := by
        intro y hxy
        show (if y = x then some v else σ_cfg₀ y) = σ_cfg₀ y
        have hne : ¬ (y = x) := fun h => hxy h.symm
        rw [if_neg hne]
      have h_upd : UpdateState P σ_cfg₀ x v σ_cfg₁ :=
        UpdateState.update h_cfg_x_old h_cfg_x_new h_cfg_other
      refine ⟨σ_cfg₁, EvalCmd.eval_set h_eval_cfg h_upd hwfvar, ?_⟩
      intro y h_def_y
      by_cases hyx : y = x
      · subst hyx
        rw [h_xv, h_cfg_x_new]
      · have h_struct_y : σ_struct₁ y = σ_struct₀ y := h_other y (fun h => hyx h.symm)
        have h_cfg_y : σ_cfg₁ y = σ_cfg₀ y := h_cfg_other y (fun h => hyx h.symm)
        rw [h_struct_y, h_cfg_y]
        have h_def_y' : isDefined σ_struct₀ [y] := by
          intro w hw
          rw [List.mem_singleton] at hw
          rw [hw]
          have h_y_def_in_σ' : (σ_struct₁ y).isSome = true :=
            h_def_y y (List.mem_singleton.mpr rfl)
          exact h_struct_y ▸ h_y_def_in_σ'
        exact h_agree y h_def_y'
  | eval_set_nondet hupdate hval hwfvar =>
    rename_i md x v
    cases hupdate with
    | update h_xv' h_xv h_other =>
      rename_i v'
      have h_x_def_struct : isDefined σ_struct₀ [x] := by
        intro y hy
        rw [List.mem_singleton] at hy
        rw [hy, h_xv']
        rfl
      have h_cfg_x_old : σ_cfg₀ x = some v' := by
        have h_eq : σ_struct₀ x = σ_cfg₀ x := h_agree x h_x_def_struct
        rw [← h_eq]; exact h_xv'
      let σ_cfg₁ : SemanticStore P := fun y => if y = x then some v else σ_cfg₀ y
      have h_cfg_x_new : σ_cfg₁ x = some v := by
        show (if x = x then some v else σ_cfg₀ x) = some v
        simp
      have h_cfg_other : ∀ y, x ≠ y → σ_cfg₁ y = σ_cfg₀ y := by
        intro y hxy
        show (if y = x then some v else σ_cfg₀ y) = σ_cfg₀ y
        have hne : ¬ (y = x) := fun h => hxy h.symm
        rw [if_neg hne]
      have h_upd : UpdateState P σ_cfg₀ x v σ_cfg₁ :=
        UpdateState.update h_cfg_x_old h_cfg_x_new h_cfg_other
      refine ⟨σ_cfg₁, EvalCmd.eval_set_nondet h_upd hval hwfvar, ?_⟩
      intro y h_def_y
      by_cases hyx : y = x
      · subst hyx
        rw [h_xv, h_cfg_x_new]
      · have h_struct_y : σ_struct₁ y = σ_struct₀ y := h_other y (fun h => hyx h.symm)
        have h_cfg_y : σ_cfg₁ y = σ_cfg₀ y := h_cfg_other y (fun h => hyx h.symm)
        rw [h_struct_y, h_cfg_y]
        have h_def_y' : isDefined σ_struct₀ [y] := by
          intro w hw
          rw [List.mem_singleton] at hw
          rw [hw]
          have h_y_def_in_σ' : (σ_struct₁ y).isSome = true :=
            h_def_y y (List.mem_singleton.mpr rfl)
          exact h_struct_y ▸ h_y_def_in_σ'
        exact h_agree y h_def_y'
  | eval_assert_pass hcond hwfb =>
    rename_i l md e
    have h_eval_cfg : P.eval δ σ_cfg₀ e = .some HasBool.tt :=
      h_wf_def e HasBool.tt σ_struct₀ σ_cfg₀
        (storeAgreement_supplies_mono_premise σ_struct₀ σ_cfg₀ h_agree) hcond
    exact ⟨σ_cfg₀, EvalCmd.eval_assert_pass h_eval_cfg hwfb, h_agree⟩
  | eval_assert_fail hcond hwfb =>
    rename_i l md e
    have h_eval_cfg : P.eval δ σ_cfg₀ e = .some HasBool.ff :=
      h_wf_def e HasBool.ff σ_struct₀ σ_cfg₀
        (storeAgreement_supplies_mono_premise σ_struct₀ σ_cfg₀ h_agree) hcond
    exact ⟨σ_cfg₀, EvalCmd.eval_assert_fail h_eval_cfg hwfb, h_agree⟩
  | eval_assume hcond hwfb =>
    rename_i l md e
    have h_eval_cfg : P.eval δ σ_cfg₀ e = .some HasBool.tt :=
      h_wf_def e HasBool.tt σ_struct₀ σ_cfg₀
        (storeAgreement_supplies_mono_premise σ_struct₀ σ_cfg₀ h_agree) hcond
    exact ⟨σ_cfg₀, EvalCmd.eval_assume h_eval_cfg hwfb, h_agree⟩
  | eval_cover hwfb =>
    exact ⟨σ_cfg₀, EvalCmd.eval_cover hwfb, h_agree⟩

/-- A helper: if `EvalCmd c σ σ' f` succeeds and `x` is not in `c`'s definedVars
(so `c` does not init x), and `σ x = none`, then `σ' x = none`.  This holds because
`c` either doesn't touch x, or modifies x via `set` (which requires `σ x = some _`,
contradicting `σ x = none`). -/
theorem agreement_helper_unchanged_at_x {P : PureExpr}
    [HasFvar P] [HasFvars P] [HasBoolOps P] [DecidableEq P.Ident]
    {δ : P.Factory} {σ σ' : SemanticStore P} {c : Cmd P} {failed : Bool}
    {x : P.Ident}
    (h_eval : EvalCmd P δ σ c σ' failed)
    (h_x_not_def : x ∉ Cmd.definedVars c)
    (h_σ_x : σ x = none) :
    σ' x = none := by
  cases h_eval with
  | eval_init heval hinit hwfvar =>
    cases hinit with
    | init h_xn h_xv h_other =>
      -- After cases on hinit, anonymous vars (from EvalCmd's eval_init constructor):
      -- `x✝² : P.Ty`, `x✝¹ : MetaData`, `x✝ : P.Ident`, `v✝ e✝ : P.Expr`.
      rename_i ty md e v x_init
      have h_x_ne : x_init ≠ x := by
        intro h_eq
        apply h_x_not_def
        show x ∈ Cmd.definedVars (Cmd.init x_init ty (ExprOrNondet.det e) md)
        have h_dv :
            Cmd.definedVars (Cmd.init x_init ty (ExprOrNondet.det e) md) = [x_init] := by
          with_unfolding_all rfl
        rw [h_dv, h_eq]
        exact List.mem_cons_self
      rw [h_other x h_x_ne]; exact h_σ_x
  | eval_init_unconstrained hinit hval hwfvar =>
    cases hinit with
    | init h_xn h_xv h_other =>
      rename_i ty md x_init v
      have h_x_ne : x_init ≠ x := by
        intro h_eq
        apply h_x_not_def
        show x ∈ Cmd.definedVars (Cmd.init x_init ty ExprOrNondet.nondet md)
        have h_dv :
            Cmd.definedVars (Cmd.init x_init ty ExprOrNondet.nondet md) = [x_init] := by
          with_unfolding_all rfl
        rw [h_dv, h_eq]
        exact List.mem_cons_self
      rw [h_other x h_x_ne]; exact h_σ_x
  | eval_set heval hupdate hwfvar =>
    cases hupdate with
    | update h_xv' h_xv h_other =>
      rename_i md e v x_set v'
      by_cases h_eq : x_set = x
      · subst h_eq
        rw [h_σ_x] at h_xv'
        cases h_xv'
      · rw [h_other x h_eq]; exact h_σ_x
  | eval_set_nondet hupdate hval hwfvar =>
    cases hupdate with
    | update h_xv' h_xv h_other =>
      rename_i md x_set v v'
      by_cases h_eq : x_set = x
      · subst h_eq
        rw [h_σ_x] at h_xv'
        cases h_xv'
      · rw [h_other x h_eq]; exact h_σ_x
  | eval_assert_pass _ _ => exact h_σ_x
  | eval_assert_fail _ _ => exact h_σ_x
  | eval_assume _ _ => exact h_σ_x
  | eval_cover _ => exact h_σ_x

/-- Multi-command extension of `agreement_helper_unchanged_at_x`: if `EvalCmds`
takes σ to σ' over a list `cmds`, and `x` is not in `cmds.definedVars`, and
`σ x = none`, then `σ' x = none`. By induction on `EvalCmds`. -/
theorem agreement_helper_unchanged_at_x_multi {P : PureExpr}
    [HasFvar P] [HasFvars P] [HasBoolOps P] [DecidableEq P.Ident]
    {δ : P.Factory} {σ σ' : SemanticStore P} {cmds : List (Cmd P)} {failed : Bool}
    {x : P.Ident}
    (h_eval : EvalCmds P (EvalCmd P) δ σ cmds σ' failed)
    (h_x_not_def : x ∉ Cmds.definedVars cmds)
    (h_σ_x : σ x = none) :
    σ' x = none := by
  induction h_eval with
  | eval_cmds_none => exact h_σ_x
  | eval_cmds_some hcmd hrest ih =>
    rename_i σ_a c σ_b _ cs σ_c _
    -- σ_a x = none, want σ_c x = none
    -- step 1: σ_b x = none from single-cmd helper
    have h_x_not_in_head : x ∉ Cmd.definedVars c := by
      intro h_x_in_head
      apply h_x_not_def
      rw [Cmds.definedVars_cons]
      exact List.mem_append_left _ h_x_in_head
    have h_σ_b_x : σ_b x = none :=
      agreement_helper_unchanged_at_x hcmd h_x_not_in_head h_σ_x
    -- step 2: σ_c x = none from inductive hypothesis on rest
    have h_x_not_in_tail : x ∉ Cmds.definedVars cs := by
      intro h_x_in_tail
      apply h_x_not_def
      rw [Cmds.definedVars_cons]
      exact List.mem_append_right _ h_x_in_tail
    exact ih h_x_not_in_tail h_σ_b_x

/-- Multi-command agreement-preservation, by induction on `cs`. -/
theorem EvalCmds_under_agreement {P : PureExpr}
    [HasFvar P] [HasFvars P] [HasBoolOps P] [DecidableEq P.Ident]
    (δ : P.Factory)
    (cs : List (Cmd P))
    (h_wf_def : WellFormedSemanticEvalMono δ) :
    ∀ (σ_struct₀ σ_cfg₀ σ_struct₁ : SemanticStore P) (failed : Bool),
      StoreAgreement σ_struct₀ σ_cfg₀ →
      EvalCmds P (EvalCmd P) δ σ_struct₀ cs σ_struct₁ failed →
      (∀ x ∈ Cmds.definedVars cs, σ_cfg₀ x = none) →
      (Cmds.definedVars cs).Nodup →
      ∃ σ_cfg₁, EvalCmds P (EvalCmd P) δ σ_cfg₀ cs σ_cfg₁ failed
              ∧ StoreAgreement σ_struct₁ σ_cfg₁ := by
  induction cs with
  | nil =>
    intro σ_struct₀ σ_cfg₀ σ_struct₁ failed h_agree h_eval _ _
    cases h_eval
    exact ⟨σ_cfg₀, EvalCmds.eval_cmds_none, h_agree⟩
  | cons c cs ih =>
    intro σ_struct₀ σ_cfg₀ σ_struct₁ failed h_agree h_eval h_fresh h_unique
    cases h_eval with
    | eval_cmds_some hcmd hrest =>
      rename_i σ_mid f f'
      have h_fresh_head : ∀ x ∈ Cmd.definedVars c, σ_cfg₀ x = none := by
        intro x hx
        have hx' : x ∈ Cmds.definedVars (c :: cs) := by
          rw [Cmds.definedVars_cons]
          exact List.mem_append_left _ hx
        exact h_fresh x hx'
      have h_fresh_tail_init : ∀ x ∈ Cmds.definedVars cs, σ_cfg₀ x = none := by
        intro x hx
        have hx' : x ∈ Cmds.definedVars (c :: cs) := by
          rw [Cmds.definedVars_cons]
          exact List.mem_append_right _ hx
        exact h_fresh x hx'
      -- Apply EvalCmd_under_agreement to head cmd c.
      have ⟨σ_cfg_mid, h_cmd_cfg, h_agree_mid⟩ :=
        EvalCmd_under_agreement δ σ_struct₀ σ_cfg₀ c σ_mid f h_agree hcmd h_wf_def
          h_fresh_head
      -- Now we need σ_cfg_mid to satisfy the freshness for the tail cs.
      have h_fresh_tail : ∀ x ∈ Cmds.definedVars cs, σ_cfg_mid x = none := by
        intro x hx
        have h_x_not_in_head : x ∉ Cmd.definedVars c := by
          intro h_x_in_head
          have h_nodup_split :
              ∀ a ∈ Cmd.definedVars c, ∀ b ∈ Cmds.definedVars cs, a ≠ b := by
            have h_unique' : (Cmds.definedVars (c :: cs)).Nodup := h_unique
            rw [Cmds.definedVars_cons] at h_unique'
            exact (List.nodup_append.mp h_unique').2.2
          exact h_nodup_split x h_x_in_head x hx rfl
        have h_cfg₀_x : σ_cfg₀ x = none := h_fresh_tail_init x hx
        exact agreement_helper_unchanged_at_x h_cmd_cfg h_x_not_in_head h_cfg₀_x
      have h_unique_tail : (Cmds.definedVars cs).Nodup := by
        have : (Cmds.definedVars (c :: cs)).Nodup := h_unique
        rw [Cmds.definedVars_cons] at this
        exact (List.nodup_append.mp this).2.1
      have ⟨σ_cfg_end, h_rest_cfg, h_agree_end⟩ :=
        ih σ_mid σ_cfg_mid σ_struct₁ f' h_agree_mid hrest h_fresh_tail
          h_unique_tail
      exact ⟨σ_cfg_end, EvalCmds.eval_cmds_some h_cmd_cfg h_rest_cfg, h_agree_end⟩

theorem single_cmd_eval {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    (extendFactory : ExtendFactory P)
    (c : Cmd P) (ρ₀ ρ₁ : Env P)
    (h : StepStmtStar P (EvalCmd P) extendFactory
      (.stmts [.cmd c] ρ₀) (.terminal ρ₁)) :
    ∃ σ' failed, EvalCmd P ρ₀.factory ρ₀.store c σ' failed ∧
      ρ₁.store = σ' ∧ ρ₁.factory = ρ₀.factory ∧
      ρ₁.hasFailure = (ρ₀.hasFailure || failed) := by
  cases h with
  | step _ _ _ hstep1 hrest1 =>
    cases hstep1 with
    | step_stmts_cons =>
      have ⟨ρ_mid, h_inner, h_tail⟩ := seq_reaches_terminal P (EvalCmd P) extendFactory hrest1
      have h_eq := stmts_nil_terminal (EvalCmd P) extendFactory _ _ h_tail
      subst h_eq
      cases h_inner with
      | step _ _ _ hstep2 hrest2 =>
        cases hstep2 with
        | step_cmd heval =>
          cases hrest2 with
          | refl => exact ⟨_, _, heval, rfl, rfl, rfl⟩
          | step _ _ _ hstep3 _ => exact absurd hstep3 (by intro h; cases h)

/-- Transitivity of the deterministic-CFG multi-step run. -/
theorem StepDetCFGStar_trans {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    {extendFactory : ExtendFactory P}
    {fac : P.Factory}
    {cfg : CFG String (DetBlock String (Cmd P) P)}
    {a b c : CFGConfig String (Cmd P) P}
    (h₁ : StepDetCFGStar extendFactory fac cfg a b)
    (h₂ : StepDetCFGStar extendFactory fac cfg b c) :
    StepDetCFGStar extendFactory fac cfg a c :=
  ReflTrans_Transitive _ _ _ _ h₁ h₂

/-- Run a deterministic block from `.atBlock t` to the selected successor of a
`condGoto`: fetch + chain + goto.  The `Bool` `b` selects the branch — the true
branch (target `tlbl`) when `b = true`, the false branch (target `elbl`) when
`b = false` — mirroring how the condition evaluates to `if b then tt else ff`. -/
theorem run_block_goto {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    {extendFactory : ExtendFactory P}
    {cfg : CFG String (DetBlock String (Cmd P) P)}
    {δ : P.Factory} {σ σ' : SemanticStore P}
    {cs : List (Cmd P)} {c : P.Expr} {tlbl elbl : String} {md : MetaData P}
    {f_base f : Bool} {t : String} {b : Bool}
    (h_lkp : List.lookup t cfg.blocks = .some ⟨cs, .condGoto c tlbl elbl md⟩)
    (h_cmds : EvalCmds P (EvalCmd P) δ σ cs σ' f)
    (h_cond : P.eval δ σ' c = .some (if b then HasBool.tt else HasBool.ff))
    (hwfb : WellFormedSemanticEvalBool δ)
    (hwfcongr : WellFormedSemanticEvalExprCongr δ) :
    StepCFGStar P (EvalCmd P) extendFactory δ cfg
      (.atBlock t σ f_base)
      (.atBlock (if b then tlbl else elbl) σ' (f_base || f)) := by
  have h_fetch : StepCFG (l := String) (CmdT := Cmd P) P (EvalCmd P) extendFactory δ cfg
      (.atBlock t σ f_base)
      (.inBlock t cs (.condGoto c tlbl elbl md) σ f_base) :=
    StepCFG.fetch (extendFactory := extendFactory) h_lkp
  have h_chain := EvalCmds_to_StepCFG_chain (extendFactory := extendFactory)
                    (cfg := cfg) h_cmds t (.condGoto c tlbl elbl md) f_base
  have h_goto : StepCFG (l := String) (CmdT := Cmd P) P (EvalCmd P) extendFactory δ cfg
      (.inBlock t [] (.condGoto c tlbl elbl md) σ' (f_base || f))
      (.atBlock (if b then tlbl else elbl) σ' (f_base || f)) := by
    cases b with
    | true => exact StepCFG.goto_true (extendFactory := extendFactory) h_cond hwfb hwfcongr
    | false => exact StepCFG.goto_false (extendFactory := extendFactory) h_cond hwfb hwfcongr
  exact ReflTrans.step _ _ _ h_fetch
    (ReflTrans_Transitive _ _ _ _ h_chain
      (ReflTrans.step _ _ _ h_goto (ReflTrans.refl _)))

/-- Run a deterministic block from `.atBlock t` to `.terminal`: fetch + chain
+ finish. -/
theorem run_block_finish {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    {extendFactory : ExtendFactory P}
    {cfg : CFG String (DetBlock String (Cmd P) P)}
    {δ : P.Factory} {σ σ' : SemanticStore P}
    {cs : List (Cmd P)} {md : MetaData P}
    {f_base f : Bool} {t : String}
    (h_lkp : List.lookup t cfg.blocks = .some ⟨cs, .finish md⟩)
    (h_cmds : EvalCmds P (EvalCmd P) δ σ cs σ' f) :
    StepCFGStar P (EvalCmd P) extendFactory δ cfg
      (.atBlock t σ f_base)
      (.terminal σ' (f_base || f)) := by
  have h_fetch : StepCFG (l := String) (CmdT := Cmd P) P (EvalCmd P) extendFactory δ cfg
      (.atBlock t σ f_base)
      (.inBlock t cs (.finish md) σ f_base) :=
    StepCFG.fetch (extendFactory := extendFactory) h_lkp
  have h_chain := EvalCmds_to_StepCFG_chain (extendFactory := extendFactory)
                    (cfg := cfg) h_cmds t (.finish md) f_base
  have h_finish : StepCFG (l := String) (CmdT := Cmd P) P (EvalCmd P) extendFactory δ cfg
      (.inBlock t [] (.finish md) σ' (f_base || f))
      (.terminal σ' (f_base || f)) :=
    StepCFG.finish (extendFactory := extendFactory)
  exact ReflTrans.step _ _ _ h_fetch
    (ReflTrans_Transitive _ _ _ _ h_chain
      (ReflTrans.step _ _ _ h_finish (ReflTrans.refl _)))

end Imperative
