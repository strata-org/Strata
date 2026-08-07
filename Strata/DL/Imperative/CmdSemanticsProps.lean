/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.CmdSemantics
import all Strata.DL.Imperative.CmdSemantics
import all Strata.DL.Imperative.Cmd
public import Strata.DL.Imperative.Stmt
import all Strata.DL.Util.ListUtils

---------------------------------------------------------------------

namespace Imperative

/-! # Metatheory of command evaluation (`EvalCmd`)

Store-agreement, definedness, and none-preservation results for the single-command
evaluation relation `EvalCmd`. Key results:

- Store-substitution and definedness plumbing (`isDefined`/`isNotDefined` cons/app,
  `substStores`/`substDefined`/`invStores` symmetry, `InitState`/`UpdateState`
  definedness and uniqueness).
- `storeAgreement_storeWith`: a `SemanticStore.update` at a source-undefined slot
  preserves `StoreAgreement`.
- `EvalCmd_preserves_isSome`: a command never undefines an already-defined slot.
- None-preservation: `InitState_preserves_none`, `UpdateState_preserves_none`,
  `evalCmd_preserves_none`, and `evalCmd_preserves_none_of_not_def` (a command
  preserves a `none` slot it neither defines nor modifies).
-/

public section

section

variable (P : PureExpr)

theorem isDefinedCons :
  isDefined σ [v] →
  isDefined σ vs2 →
  isDefined σ (v :: vs2) := by
  intros Hd1 Hd2
  simp [isDefined] at *
  simp [Option.isSome] at *
  split <;> simp_all

theorem isDefinedApp :
  isDefined σ vs1 →
  isDefined σ vs2 →
  isDefined σ (vs1 ++ vs2) := by
  intros Hd1 Hd2
  simp [isDefined] at *
  intros id Hin
  simp [Option.isSome] at *
  cases Hin with
  | inl Hin =>
    split <;> simp
    specialize Hd1 id Hin; simp_all
  | inr Hin =>
    split <;> simp
    specialize Hd2 id Hin; simp_all

theorem isDefinedCons' :
  isDefined σ (h :: t) →
  isDefined σ [h] ∧ isDefined σ t := by simp [isDefined] at *

theorem isDefinedApp' :
  isDefined σ (t1 ++ t2) →
  isDefined σ t1 ∧ isDefined σ t2 := by
  intros Hd
  simp [isDefined] at *
  apply And.intro
  . intros x Hin
    apply Hd; left; assumption
  . intros x Hin
    apply Hd; right; assumption

theorem isNotDefinedCons :
  isNotDefined σ [v] →
  isNotDefined σ vs2 →
  isNotDefined σ (v :: vs2) := by
  intros Hd1 Hd2
  simp [isNotDefined] at *
  simp_all

theorem isNotDefinedApp :
  isNotDefined σ vs1 →
  isNotDefined σ vs2 →
  isNotDefined σ (vs1 ++ vs2) := by
  intros Hd1 Hd2
  simp [isNotDefined] at *
  intros id Hin
  cases Hin with
  | inl Hin =>
    specialize Hd1 id Hin; simp_all
  | inr Hin =>
    specialize Hd2 id Hin; simp_all

theorem isNotDefinedCons' :
  isNotDefined σ (h :: t) →
  isNotDefined σ [h] ∧ isNotDefined σ t := by simp [isNotDefined] at *

theorem isNotDefinedApp' :
  isNotDefined σ (t1 ++ t2) →
  isNotDefined σ t1 ∧ isNotDefined σ t2 := by
  intros Hd
  simp [isNotDefined] at *
  apply And.intro
  . intros x Hin
    apply Hd; left; assumption
  . intros x Hin
    apply Hd; right; assumption

/-! ### Store Substitution Properties -/

theorem substSwapId (substs : List (P.Ident × P.Ident)) :
  (substSwap (substSwap substs)) = substs := by
  simp [substSwap]

theorem substStoresFlip :
  substStores σ₁ σ₂ substs →
  substStores σ₂ σ₁ (substSwap substs) := by
  intros Hsub
  simp [substStores, substSwap] at *
  intros k1 k2 x2 x1 Hin Heq1 Heq2
  simp_all
  apply Eq.symm
  apply Hsub
  exact Hin

theorem substStoresFlip' :
  substStores σ₂ σ₁ (substSwap substs) →
  substStores σ₁ σ₂ substs := by
  intros Hsub
  have Hsub' := substStoresFlip Hsub
  simp [substSwapId] at Hsub'
  exact Hsub'

theorem substDefinedFlip :
  substDefined σ₁ σ₂ substs →
  substDefined σ₂ σ₁ (substSwap substs) := by
  intros Hsub
  simp [substDefined, substSwap] at *
  intros k1 k2 x2 x1 Hin Heq1 Heq2
  simp_all
  exact And.comm.mp (Hsub k2 k1 Hin)

theorem substDefinedFlip' :
  substDefined σ₂ σ₁ (substSwap substs) →
  substDefined σ₁ σ₂ substs := by
  intros Hsub
  have Hsub' := substDefinedFlip Hsub
  simp [substSwapId] at Hsub'
  exact Hsub'

theorem invStoresComm :
  invStores σ₁ σ₂ ks →
  invStores σ₂ σ₁ ks := by
  intros Hinv
  simp [invStores] at *
  apply substStoresFlip'
  simp [substSwap]
  assumption

theorem invStoresExceptComm :
  invStoresExcept σ₁ σ₂ ks →
  invStoresExcept σ₂ σ₁ ks := by
  intros Hinv ks' Hdisj
  simp [invStoresExcept] at *
  exact invStoresComm (Hinv ks' Hdisj)

end section

theorem InitStateDefCons
  {P : PureExpr} {σ σ' : SemanticStore P}
  {vs : List P.Ident} {e : P.Expr} {v : P.Ident} :
  isDefined σ vs →
  InitState P σ v e σ' →
  isDefined σ' (v::vs) := by
  intros Hdef Heval
  cases Heval with
  | init Hold HH Hsome =>
  simp [isDefined, HH] at *
  intros v' Hv'
  have Heq: ¬ v = v' :=by
    false_or_by_contra; rename_i Heq
    specialize Hdef v' Hv'
    simp_all
  specialize Hsome v' Heq
  specialize Hdef v'
  simp_all

theorem InitStateDefMonotone
  {P : PureExpr} {σ σ' : SemanticStore P}
  {vs : List P.Ident} {e : P.Expr} {v : P.Ident} :
  isDefined σ vs →
  InitState P σ v e σ' →
  isDefined σ' vs := by
  intros Hdef Heval
  exact (isDefinedCons' (InitStateDefCons Hdef Heval)).right

theorem UpdateStateDef
  {P : PureExpr} {σ σ' : SemanticStore P}
  {e : P.Expr} {v : P.Ident} :
  UpdateState P σ v e σ' →
  isDefined σ [v] ∧ isDefined σ' [v] := by
  intro Heval
  cases Heval with
  | update Hold HH Hsome =>
  simp_all [isDefined]

theorem UpdateStateDefMonotone
  {P : PureExpr} {σ σ' : SemanticStore P}
  {vs : List P.Ident} {e : P.Expr} {v : P.Ident} :
  isDefined σ vs →
  UpdateState P σ v e σ' →
  isDefined σ' vs := by
  intros Hdef Heval
  cases Heval with
  | update Hold HH Hsome =>
  simp [isDefined] at *
  intros v' Hv'
  by_cases Heq: (v = v')
  case pos =>
    simp [Option.isSome]
    simp [Heq] at *
    split <;> simp_all
  case neg =>
    specialize Hsome v' Heq
    specialize Hdef v'
    simp [Hsome]
    exact Hdef Hv'

theorem UpdateStateUniqueResult
  {P : PureExpr} {σ σ' σ'': SemanticStore P}
  {e : P.Expr} {v : P.Ident} :
  UpdateState P σ v e σ' →
  UpdateState P σ v e σ'' →
  σ' = σ'' := by
  intro Hu1 Hu2
  cases Hu1; cases Hu2
  rename_i Hfa1 _ _ _ Hfa2 _
  ext v' e'
  by_cases h: v' = v
  simp_all
  rw[eq_comm] at h
  specialize Hfa1 v' h
  specialize Hfa2 v' h
  simp_all

theorem InitStateUniqueResult
  {P : PureExpr} {σ σ' σ'': SemanticStore P}
  {e : P.Expr} {v : P.Ident} :
  InitState P σ v e σ' →
  InitState P σ v e σ'' →
  σ' = σ'' := by
  intro Hu1 Hu2
  cases Hu1; cases Hu2
  rename_i Hfa1 _ _ Hfa2 _
  ext v' e'
  by_cases h: v' = v
  simp_all
  rw[eq_comm] at h
  specialize Hfa1 v' h
  specialize Hfa2 v' h
  simp_all

/-! ### Assert / set commutation -/

theorem eval_assert_store_cst
  [HasFvar P] [HasBool P] [HasBoolOps P] [HasOps P]:
  EvalCmd P fac σ (.assert l e md) σ' f → σ = σ' := by
  intros Heval; cases Heval with
  | eval_assert_pass _ => rfl
  | eval_assert_fail _ => rfl

theorem UpdateStateComm {P: PureExpr} {x1 x2: P.Ident} {σ σ' σ'' σ1 σ2: SemanticStore P} {v1 v2: P.Expr}
  [DecidableEq P.Ident]:
  ¬ x1 = x2 →
  UpdateState P σ x1 v1 σ1 →
  UpdateState P σ1 x2 v2 σ' →
  UpdateState P σ x2 v2 σ2 →
  UpdateState P σ2 x1 v1 σ'' →
  σ' = σ'' := by
  intro Hneq Hu1 Hu2 Hu3 Hu4
  cases Hu1; cases Hu2; cases Hu3; cases Hu4
  ext i e
  rename_i Hfa1 _ _ _ Hfa2 _ _ _ Hfa3 _ _ _ Hfa4 _
  simp at Hfa1 Hfa2 Hfa3 Hfa4
  rw[Eq.comm] at Hneq
  by_cases Heq1: x1 = i
  simp_all
  by_cases Heq2: x2 = i
  rw[Eq.comm] at Hneq
  specialize Hfa4 x2 Hneq
  simp_all
  specialize Hfa1 i Heq1
  specialize Hfa2 i Heq2
  specialize Hfa3 i Heq2
  specialize Hfa4 i Heq1
  simp_all

theorem UpdateState_InitStateComm {P: PureExpr} {x1 x2: P.Ident} {σ σ' σ'' σ1 σ2: SemanticStore P} {v1 v2: P.Expr}
  [DecidableEq P.Ident]:
  ¬ x1 = x2 →
  UpdateState P σ x1 v1 σ1 →
  InitState P σ1 x2 v2 σ' →
  InitState P σ x2 v2 σ2 →
  UpdateState P σ2 x1 v1 σ'' →
  σ' = σ'' := by
  intro Hneq Hu1 Hu2 Hu3 Hu4
  cases Hu1; cases Hu2; cases Hu3; cases Hu4
  ext i e
  rename_i Hfa1 _ _ Hfa2 _ _ Hfa3 _ _ _ Hfa4 _
  simp at Hfa1 Hfa2 Hfa3 Hfa4
  rw[Eq.comm] at Hneq
  by_cases Heq1: x1 = i
  simp_all
  by_cases Heq2: x2 = i
  rw[Eq.comm] at Hneq
  specialize Hfa4 x2 Hneq
  simp_all
  specialize Hfa1 i Heq1
  specialize Hfa2 i Heq2
  specialize Hfa3 i Heq2
  specialize Hfa4 i Heq1
  simp_all

theorem semantic_eval_eq_of_eval_cmd_set_unrelated_var
  [HasVarsImp P (Cmd P)] [HasFvar P] [HasBool P] [HasBoolOps P] [HasFvars P] [HasOps P]:
  WellFormedSemanticEvalExprCongr (P := P) fac →
  WellFormedStore σ fac →
  WellFormedStore σ' fac →
  ¬ v ∈ HasFvars.getFvars e →
  EvalCmd P fac σ (Cmd.set v (.det e') md) σ' f →
  P.eval fac σ e = P.eval fac σ' e := by
  intro Hwf Hwfs Hwfs' Hnin Heval
  unfold WellFormedSemanticEvalExprCongr at Hwf
  specialize Hwf e σ σ' Hwfs Hwfs'
  have: ∀ (v : P.Ident), v ∈ HasFvars.getFvars e → σ v = σ' v := by
    cases Heval
    rename_i Hu
    cases Hu
    rename_i Hfa _
    intro v' Hv'
    ext e'
    by_cases Hc: ¬ v = v'
    specialize Hfa v' Hc
    simp_all
    simp_all
  exact Hwf this

theorem eval_cmd_set_comm'
  [HasVarsImp P (List (Stmt P (Cmd P)))] [HasVarsImp P (Cmd P)]
  [HasFvar P] [HasBool P] [HasBoolOps P] [HasOps P] [DecidableEq P.Ident] :
  ¬ x1 = x2 →
  P.eval fac σ v1 = P.eval fac σ2 v1 →
  P.eval fac σ v2 = P.eval fac σ1 v2 →
  EvalCmd P fac σ (Cmd.set x1 (.det v1) md1) σ1 f1 →
  EvalCmd P fac σ1 (Cmd.set x2 (.det v2) md2) σ' f2 →
  EvalCmd P fac σ (Cmd.set x2 (.det v2) md2') σ2 f3 →
  EvalCmd P fac σ2 (Cmd.set x1 (.det v1) md1') σ'' f4 →
  σ' = σ'' := by
  intro Hneq Heq1 Heq2 Hs1 Hs2 Hs3 Hs4
  cases Hs1 with | eval_set _ Hu1 _ =>
  cases Hs2 with | eval_set _ Hu2 _ =>
  cases Hs3 with | eval_set _ Hu3 _ =>
  cases Hs4 with | eval_set _ Hu4 _ =>
  simp_all
  exact UpdateStateComm Hneq Hu1 Hu2 Hu3 Hu4

theorem eval_cmd_set_comm
  [HasVarsImp P (List (Stmt P (Cmd P)))] [HasVarsImp P (Cmd P)]
  [HasFvar P] [HasBool P] [HasBoolOps P] [HasFvars P] [HasOps P] [DecidableEq P.Ident]:
  WellFormedSemanticEvalExprCongr (P := P) fac →
  WellFormedStore σ fac →
  WellFormedStore σ1 fac →
  WellFormedStore σ2 fac →
  ¬ x1 = x2 →
  ¬ x1 ∈ HasFvars.getFvars v2 →
  ¬ x2 ∈ HasFvars.getFvars v1 →
  EvalCmd P fac σ (Cmd.set x1 (.det v1) md1) σ1 f1 →
  EvalCmd P fac σ1 (Cmd.set x2 (.det v2) md2) σ' f2 →
  EvalCmd P fac σ (Cmd.set x2 (.det v2) md2') σ2 f3 →
  EvalCmd P fac σ2 (Cmd.set x1 (.det v1) md1') σ'' f4 →
  σ' = σ'' := by
  intro Hwf Hwfs Hwfs1 Hwfs2 Hneq Hnin1 Hnin2 Hs1 Hs2 Hs3 Hs4
  have Heval2 := semantic_eval_eq_of_eval_cmd_set_unrelated_var Hwf Hwfs Hwfs1 Hnin1 Hs1
  have Heval1 := semantic_eval_eq_of_eval_cmd_set_unrelated_var Hwf Hwfs Hwfs2 Hnin2 Hs3
  exact eval_cmd_set_comm' Hneq Heval1 Heval2 Hs1 Hs2 Hs3 Hs4

/-- A `SemanticStore.update` at a slot the source store leaves undefined preserves
`StoreAgreement` with the source: the only changed slot is `ident`, which the
source store does not define (one-directionality of `StoreAgreement`). -/
theorem storeAgreement_storeWith {P : PureExpr} [DecidableEq P.Ident]
    (σ_src σ_tgt : SemanticStore P) (ident : P.Ident) (b : P.Expr)
    (h_agree : StoreAgreement σ_src σ_tgt)
    (h_src_none : σ_src ident = none) :
    StoreAgreement σ_src (SemanticStore.update σ_tgt ident b) := by
  intro x h_def
  have h_x_def : (σ_src x).isSome = true := h_def x (List.mem_singleton.mpr rfl)
  have h_ne : x ≠ ident := by
    rintro rfl; rw [h_src_none] at h_x_def; exact absurd h_x_def (by simp)
  rw [h_agree x h_def]
  simp [SemanticStore.update, h_ne]

/-- A single `EvalCmd` never undefines a slot: any `y` that was `isSome` stays
`isSome` (`init`/`set` only assign `some`; `assert`/`assume`/`cover` keep the
store). -/
theorem EvalCmd_preserves_isSome {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P] [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    {δ : P.Factory} {σ σ' : SemanticStore P} {c : Cmd P} {haf : Bool}
    (h : EvalCmd P δ σ c σ' haf)
    {y : P.Ident} (h_some : (σ y).isSome = true) :
    (σ' y).isSome = true := by
  cases h with
  | @eval_init _ _ _ _ _ _ x _ _ hinit _ =>
    cases hinit with
    | init _ h_xv h_other =>
      by_cases hxy : x = y
      · subst hxy; rw [h_xv]; rfl
      · rw [h_other y hxy]; exact h_some
  | @eval_init_unconstrained _ _ _ x _ _ _ hinit _ _ =>
    cases hinit with
    | init _ h_xv h_other =>
      by_cases hxy : x = y
      · subst hxy; rw [h_xv]; rfl
      · rw [h_other y hxy]; exact h_some
  | @eval_set _ _ _ _ _ x _ _ hupd _ =>
    cases hupd with
    | update _ h_xv h_other =>
      by_cases hxy : x = y
      · subst hxy; rw [h_xv]; rfl
      · rw [h_other y hxy]; exact h_some
  | @eval_set_nondet _ _ x _ _ _ hupd _ _ =>
    cases hupd with
    | update _ h_xv h_other =>
      by_cases hxy : x = y
      · subst hxy; rw [h_xv]; rfl
      · rw [h_other y hxy]; exact h_some
  | eval_assert_pass _ _ => exact h_some
  | eval_assert_fail _ _ => exact h_some
  | eval_assume _ _ => exact h_some
  | eval_cover _ => exact h_some

/-- `InitState` leaves every slot other than its target unchanged. -/
theorem InitState_preserves_none {P : PureExpr} {σ σ' : SemanticStore P}
    {x : P.Ident} {v : P.Expr} {y : P.Ident}
    (h_is : InitState P σ x v σ') (h_ne : x ≠ y) :
    σ' y = σ y := by
  cases h_is with
  | init _ _ h_other => exact h_other y h_ne

/-- `UpdateState` cannot newly-define a `none` slot: `set`/`havoc` requires the
target already defined, so a `none` slot is left `none`. -/
theorem UpdateState_preserves_none {P : PureExpr} {σ σ' : SemanticStore P}
    {x : P.Ident} {v : P.Expr} {y : P.Ident}
    (h_us : UpdateState P σ x v σ') (h_none : σ y = none) :
    σ' y = none := by
  cases h_us with
  | update h_was _ h_other =>
    by_cases hxy : x = y
    · subst hxy; rw [h_none] at h_was; exact absurd h_was (by simp)
    · rw [h_other y hxy]; exact h_none

/-- A single `EvalCmd` whose command neither defines nor modifies `y` preserves
a `none` slot at `y`. -/
theorem evalCmd_preserves_none {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P]
    [HasVarsPure P P.Expr]
    {f : P.Factory} {σ σ' : SemanticStore P} {c : Cmd P} {haf : Bool}
    (h : EvalCmd P f σ c σ' haf)
    {y : P.Ident}
    (h_none : σ y = none)
    (h_not_def : y ∉ Cmd.definedVars c)
    (h_not_mod : y ∉ Cmd.modifiedVars c) :
    σ' y = none := by
  cases h with
  | @eval_init _ _ _ _ _ _ x _ _ hinit _ =>
    have h_ne : x ≠ y := by
      intro h_eq; apply h_not_def
      rw [h_eq]; with_unfolding_all exact List.mem_singleton.mpr rfl
    cases hinit with
    | init _ _ h_other => rw [h_other y h_ne]; exact h_none
  | @eval_init_unconstrained _ _ _ x _ _ _ hinit _ _ =>
    have h_ne : x ≠ y := by
      intro h_eq; apply h_not_def
      rw [h_eq]; with_unfolding_all exact List.mem_singleton.mpr rfl
    cases hinit with
    | init _ _ h_other => rw [h_other y h_ne]; exact h_none
  | @eval_set _ _ _ _ _ x _ _ hupd _ =>
    have h_ne : x ≠ y := by
      intro h_eq; apply h_not_mod
      rw [h_eq]; with_unfolding_all exact List.mem_singleton.mpr rfl
    cases hupd with
    | update _ _ h_other => rw [h_other y h_ne]; exact h_none
  | @eval_set_nondet _ _ x _ _ _ hupd _ _ =>
    have h_ne : x ≠ y := by
      intro h_eq; apply h_not_mod
      rw [h_eq]; with_unfolding_all exact List.mem_singleton.mpr rfl
    cases hupd with
    | update _ _ h_other => rw [h_other y h_ne]; exact h_none
  | eval_assert_pass _ _ => exact h_none
  | eval_assert_fail _ _ => exact h_none
  | eval_assume _ _ => exact h_none
  | eval_cover _ => exact h_none

/-- A single command preserves a `none` slot `y` that the command does not
`init`/`set` as its target. -/
theorem evalCmd_preserves_none_of_not_def {P : PureExpr}
    [HasFvar P] [HasFvars P] [HasBoolOps P] [HasVarsPure P P.Expr] [DecidableEq P.Ident]
    {f : P.Factory} {σ σ' : SemanticStore P} {c : Cmd P} {hf : Bool} {y : P.Ident}
    (h_eval : EvalCmd P f σ c σ' hf)
    (h_none : σ y = none)
    (h_not_def : y ∉ Cmd.definedVars c) :
    σ' y = none := by
  simp only [Cmd.definedVars] at h_not_def
  cases h_eval with
  | eval_init _ h_is _ =>
    rw [InitState_preserves_none h_is (fun h => h_not_def (h ▸ List.mem_singleton.mpr rfl))]
    exact h_none
  | eval_init_unconstrained h_is _ _ =>
    rw [InitState_preserves_none h_is (fun h => h_not_def (h ▸ List.mem_singleton.mpr rfl))]
    exact h_none
  | eval_set _ h_us _ => exact UpdateState_preserves_none h_us h_none
  | eval_set_nondet h_us _ _ => exact UpdateState_preserves_none h_us h_none
  | eval_assert_pass _ _ => exact h_none
  | eval_assert_fail _ _ => exact h_none
  | eval_assume _ _ => exact h_none
  | eval_cover _ => exact h_none

end -- public section
