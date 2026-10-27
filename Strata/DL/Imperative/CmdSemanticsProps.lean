/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.CmdSemantics
import all Strata.DL.Imperative.CmdSemantics
public import Strata.DL.Imperative.StoreRelationsProps
import all Strata.DL.Imperative.Cmd
public import Strata.DL.Imperative.Stmt
import all Strata.Util.ListUtils
import all Strata.Util.ListUtilsProps
import Strata.DL.Util.Nodup

---------------------------------------------------------------------

namespace Imperative

/-! # Metatheory of command evaluation (`EvalCmd`)

Store-agreement, definedness, and none-preservation results for the single-command
evaluation relation `EvalCmd`. Key results:

- Store-substitution and definedness plumbing (`isDefined`/`isNotDefined` cons/app,
  `substStores`/`substDefined`/`invStores` symmetry, `InitState`/`UpdateState`
  definedness and uniqueness).
- `EvalCmd_preserves_isSome`: a command never undefines an already-defined slot.
- Exact-value framing: `evalCmd_preserves_eq_of_not_written` preserves the value
  of a slot the command neither defines nor modifies.
- None-preservation: `InitState_preserves_none`, `UpdateState_preserves_none`,
  `evalCmd_preserves_none`, and `evalCmd_preserves_none_of_not_def` (a command
  preserves a `none` slot it neither defines nor modifies).
- `evalCmd_definedVars_isSome`: the converse — a command defines every slot it
  declares.  Together with the previous item this pins the store domain exactly.
- `evalCmd_storeWellDefined`: a command leaves a store that holds only values,
  given that it started from one.  The command-level half of
  `Imperative.Config.storeWellDefined_star_of`.
- Event-trace store preservation: `evalCmdE_preserves_none_of_not_def`,
  `evalCmdE_preserves_isSome`, `evalCmdE_definedVars_isSome`, and
  `evalCmdE_storeWellDefined` provide the corresponding domain and value
  guarantees for `EvalCmdE`.
- `EvalCmdE.emitted_eq`: event-producing command evaluation emits exactly the
  trace determined by the command and input snapshot.
- `EvalCmd.toEvalCmdE`: every failure-flag command execution has an
  event-producing execution with the same resulting store and the exact trace
  selected by `Cmd.emittedEvents`; the converse is intentionally unavailable
  for unconditional event assertions and assumptions.
- List-level store relations (`EvalExpressions`, `ReadValues`, `UpdateStates`,
  `InitStates`): lengths (`ReadValuesLength`, `InitStatesLength`,
  `UpdateStatesLength`), uniqueness (`ReadValuesInjective`, `InitStatesInjective`),
  definedness (`InitStatesNotDefined`, `InitStatesNodup`, `InitStatesDefined`,
  `UpdateStatesDefined`, `isDefinedReadValues`, `ReadValuesIsDefined`), framing of
  reads and stored values (`InitStatesReadValuesMonotone`,
  `UpdateStatesReadValuesMonotone`, `InitStatesSomeMonotone`,
  `UpdateStatesSomeMonotone`), reads after writes (`InitStatesReadValues`,
  `UpdateStatesReadValues`), store substitutions (`substStoresInitsInv`,
  `substStoresUpdatesInv`, `ReadValuesSubstStores`), agreement outside written
  keys (`InvStoresExceptUpdateStates`, `InvStoresExceptInitStates`), and
  `initStates_preserves_wf`: initializing slots with values preserves store
  well-formedness.
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

/-- `InitState` never undefines a slot: its target becomes `some`, others are
unchanged. -/
theorem InitState_preserves_isSome {P : PureExpr} {σ σ' : SemanticStore P}
    {x : P.Ident} {v : P.Expr} {y : P.Ident}
    (h : InitState P σ x v σ') (h_some : (σ y).isSome = true) :
    (σ' y).isSome = true := by
  cases h with
  | init _ h_xv h_other =>
    by_cases hxy : x = y
    · subst hxy; rw [h_xv]; rfl
    · rw [h_other y hxy]; exact h_some

/-- `UpdateState` never undefines a slot. -/
theorem UpdateState_preserves_isSome {P : PureExpr} {σ σ' : SemanticStore P}
    {x : P.Ident} {v : P.Expr} {y : P.Ident}
    (h : UpdateState P σ x v σ') (h_some : (σ y).isSome = true) :
    (σ' y).isSome = true := by
  cases h with
  | update _ h_xv h_other =>
    by_cases hxy : x = y
    · subst hxy; rw [h_xv]; rfl
    · rw [h_other y hxy]; exact h_some

/-- A single `EvalCmd` never undefines a slot: any `y` that was `isSome` stays
`isSome` (`init`/`set` only assign `some`; `assert`/`assume`/`cover` keep the
store). -/
theorem EvalCmd_preserves_isSome {P : PureExpr} [HasFvar P] [HasFvars P] [HasBoolOps P] [DecidableEq P.Ident]
    {δ : P.Factory} {σ σ' : SemanticStore P} {c : Cmd P} {haf : Bool}
    (h : EvalCmd P δ σ c σ' haf)
    {y : P.Ident} (h_some : (σ y).isSome = true) :
    (σ' y).isSome = true := by
  cases h with
  | eval_init _ hinit _ _ =>
    exact InitState_preserves_isSome hinit h_some
  | eval_init_unconstrained hinit _ _ =>
    exact InitState_preserves_isSome hinit h_some
  | eval_set _ hupd _ _ =>
    exact UpdateState_preserves_isSome hupd h_some
  | eval_set_nondet hupd _ _ =>
    exact UpdateState_preserves_isSome hupd h_some
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
    {f : P.Factory} {σ σ' : SemanticStore P} {c : Cmd P} {haf : Bool}
    (h : EvalCmd P f σ c σ' haf)
    {y : P.Ident}
    (h_none : σ y = none)
    (h_not_def : y ∉ Cmd.definedVars c)
    (h_not_mod : y ∉ Cmd.modifiedVars c) :
    σ' y = none := by
  cases h with
  | eval_init _ hinit _ _ =>
    cases hinit with
    | init _ _ h_other =>
      rw [h_other y (by
        intro h
        subst h
        exact h_not_def (by simp [Cmd.definedVars]))]
      exact h_none
  | eval_init_unconstrained hinit _ _ =>
    cases hinit with
    | init _ _ h_other =>
      rw [h_other y (by
        intro h
        subst h
        exact h_not_def (by simp [Cmd.definedVars]))]
      exact h_none
  | eval_set _ hupd _ _ =>
    exact UpdateState_preserves_none hupd h_none
  | eval_set_nondet hupd _ _ =>
    exact UpdateState_preserves_none hupd h_none
  | eval_assert_pass _ _ => exact h_none
  | eval_assert_fail _ _ => exact h_none
  | eval_assume _ _ => exact h_none
  | eval_cover _ => exact h_none

/-- **Exact-value frame.**  A single `EvalCmd` whose command neither defines nor
modifies `y` preserves the *exact* value at `y`: `σ' y = σ y`.  This is the
value-level companion of `evalCmd_preserves_none`/`EvalCmd_preserves_isSome`. -/
theorem evalCmd_preserves_eq_of_not_written {P : PureExpr}
    [HasFvar P] [HasFvars P] [HasBoolOps P]
    {f : P.Factory} {σ σ' : SemanticStore P} {c : Cmd P} {haf : Bool}
    (h : EvalCmd P f σ c σ' haf)
    {y : P.Ident}
    (h_not_def : y ∉ Cmd.definedVars c)
    (h_not_mod : y ∉ Cmd.modifiedVars c) :
    σ' y = σ y := by
  cases h with
  | eval_init _ hinit _ _ =>
    cases hinit with
    | init _ _ h_other =>
      exact h_other y (by intro heq; subst heq; exact h_not_def (by simp [Cmd.definedVars]))
  | eval_init_unconstrained hinit _ _ =>
    cases hinit with
    | init _ _ h_other =>
      exact h_other y (by intro heq; subst heq; exact h_not_def (by simp [Cmd.definedVars]))
  | eval_set _ hupd _ _ =>
    cases hupd with
    | update _ _ h_other =>
      exact h_other y (by intro heq; subst heq; exact h_not_mod (by simp [Cmd.modifiedVars]))
  | eval_set_nondet hupd _ _ =>
    cases hupd with
    | update _ _ h_other =>
      exact h_other y (by intro heq; subst heq; exact h_not_mod (by simp [Cmd.modifiedVars]))
  | eval_assert_pass _ _ => rfl
  | eval_assert_fail _ _ => rfl
  | eval_assume _ _ => rfl
  | eval_cover _ => rfl

/-- `InitState` writes `some v`, so the slot cannot come back `none`. -/
private theorem initState_isSome {P : PureExpr}
    {σ σ' : SemanticStore P} {x : P.Ident} {v : P.Expr}
    (h : InitState P σ x v σ') : (σ' x).isSome = true := by
  cases h with
  | init _ h_some _ => rw [h_some]; simp

/-- **Declarations take effect.**  A command that declares `y` leaves `y` defined in the
    resulting store.  Only `init` declares variables. -/
theorem evalCmd_definedVars_isSome {P : PureExpr}
    [HasFvar P] [HasBool P] [HasBoolOps P]
    {f : P.Factory} {σ σ' : SemanticStore P} {c : Cmd P} {hf : Bool} {y : P.Ident}
    (h_eval : EvalCmd P f σ c σ' hf)
    (h_def : y ∈ Cmd.definedVars c) :
    (σ' y).isSome = true := by
  cases h_eval with
  | eval_init _ h_init _ =>
    simp only [Cmd.definedVars, List.mem_singleton] at h_def
    subst h_def; exact initState_isSome h_init
  | eval_init_unconstrained h_init _ _ =>
    simp only [Cmd.definedVars, List.mem_singleton] at h_def
    subst h_def; exact initState_isSome h_init
  | eval_set _ _ _ => simp only [Cmd.definedVars, List.not_mem_nil] at h_def
  | eval_set_nondet _ _ _ => simp only [Cmd.definedVars, List.not_mem_nil] at h_def
  | eval_assert_pass _ _ => simp only [Cmd.definedVars, List.not_mem_nil] at h_def
  | eval_assert_fail _ _ => simp only [Cmd.definedVars, List.not_mem_nil] at h_def
  | eval_assume _ _ => simp only [Cmd.definedVars, List.not_mem_nil] at h_def
  | eval_cover _ => simp only [Cmd.definedVars, List.not_mem_nil] at h_def

/-- A single command preserves a `none` slot `y` that the command does not
`init`/`set` as its target. -/
theorem evalCmd_preserves_none_of_not_def {P : PureExpr}
    [HasFvar P] [HasFvars P] [HasBoolOps P] [DecidableEq P.Ident]
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

/-- Event-trace analogue of `evalCmd_preserves_none_of_not_def`: an `EvalCmdE`
step preserves a `none` slot `y` it does not `init`/`set`.  `assert`/`assume`/
`cover` leave the store unchanged; `init`/`set` change only their target. -/
theorem evalCmdE_preserves_none_of_not_def {P : PureExpr}
    [HasFvar P] [HasFvars P] [HasBool P] [HasBoolOps P] [DecidableEq P.Ident]
    {f : P.Factory} {σ σ' : SemanticStore P} {c : Cmd P} {emitted : Trace P} {y : P.Ident}
    (h_eval : EvalCmdE P f σ c σ' emitted)
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
  | eval_assert => exact h_none
  | eval_assume => exact h_none
  | eval_cover => exact h_none

/-- Event-trace analogue of `EvalCmd_preserves_isSome`: an `EvalCmdE` step never
undefines a slot.  `init`/`set` only assign `some`; `assert`/`assume`/`cover`
keep the store. -/
theorem evalCmdE_preserves_isSome {P : PureExpr} [HasFvar P] [HasBool P]
    {f : P.Factory} {σ σ' : SemanticStore P} {c : Cmd P} {emitted : Trace P} {y : P.Ident}
    (h_eval : EvalCmdE P f σ c σ' emitted)
    (h_some : (σ y).isSome = true) :
    (σ' y).isSome = true := by
  cases h_eval with
  | eval_init _ hinit _ => exact InitState_preserves_isSome hinit h_some
  | eval_init_unconstrained hinit _ _ =>
    exact InitState_preserves_isSome hinit h_some
  | eval_set _ hupd _ => exact UpdateState_preserves_isSome hupd h_some
  | eval_set_nondet hupd _ _ =>
    exact UpdateState_preserves_isSome hupd h_some
  | eval_assert => exact h_some
  | eval_assume => exact h_some
  | eval_cover => exact h_some

/-- Event-trace analogue of `evalCmd_definedVars_isSome`: a command that declares
`y` leaves it defined.  Only `init` declares variables. -/
theorem evalCmdE_definedVars_isSome {P : PureExpr} [HasFvar P] [HasBool P]
    {f : P.Factory} {σ σ' : SemanticStore P} {c : Cmd P} {emitted : Trace P} {y : P.Ident}
    (h_eval : EvalCmdE P f σ c σ' emitted)
    (h_def : y ∈ Cmd.definedVars c) :
    (σ' y).isSome = true := by
  cases h_eval with
  | eval_init _ h_init _ =>
    simp only [Cmd.definedVars, List.mem_singleton] at h_def
    subst h_def; exact initState_isSome h_init
  | eval_init_unconstrained h_init _ _ =>
    simp only [Cmd.definedVars, List.mem_singleton] at h_def
    subst h_def; exact initState_isSome h_init
  | eval_set _ _ _ => simp only [Cmd.definedVars, List.not_mem_nil] at h_def
  | eval_set_nondet _ _ _ => simp only [Cmd.definedVars, List.not_mem_nil] at h_def
  | eval_assert => simp only [Cmd.definedVars, List.not_mem_nil] at h_def
  | eval_assume => simp only [Cmd.definedVars, List.not_mem_nil] at h_def
  | eval_cover => simp only [Cmd.definedVars, List.not_mem_nil] at h_def

/-- **A command leaves the store holding only values.**  Every writing rule supplies
    value-hood for what it writes, and the rest do not touch the store. -/
theorem evalCmd_storeWellDefined {P : PureExpr} [HasFvar P] [HasBool P] [HasBoolOps P]
    [LawfulHasVal P]
    {f : P.Factory} {σ σ' : SemanticStore P} {c : Cmd P} {fl : Bool}
    (hval : WellFormedSemanticEvalVal (P := P) f)
    (h : EvalCmd P f σ c σ' fl) (hsv : WellFormedStore σ f) :
    WellFormedStore σ' f := by
  -- `InitState` and `UpdateState` differ only in what they require of the old
  -- store, so one helper covers all four writing rules.
  have hwrite : ∀ (x : P.Ident) (v : P.Expr), HasVal.value f v →
      σ' x = some v → (∀ y, x ≠ y → σ' y = σ y) → WellFormedStore σ' f := by
    intro x v hv hx hoth z w hz
    by_cases hzx : x = z
    · subst hzx; rw [hx] at hz; cases hz; exact hv
    · rw [hoth z hzx] at hz; exact hsv z w hz
  cases h with
  | eval_init heval hinit _ =>
    cases hinit with
    | init _ hx hoth => exact hwrite _ _ (hval.outputsAreValues _ _ σ hsv heval) hx hoth
  | eval_init_unconstrained hinit hv _ =>
    cases hinit with
    | init _ hx hoth =>
      exact hwrite _ _ (LawfulHasVal.valueOfTy_isVal _ _ _ hv) hx hoth
  | eval_set heval hup _ =>
    cases hup with
    | update _ hx hoth => exact hwrite _ _ (hval.outputsAreValues _ _ σ hsv heval) hx hoth
  | eval_set_nondet hup htyped _ =>
    obtain ⟨_, _, _, _, hv⟩ := htyped
    cases hup with
    | update _ hx hoth =>
      exact hwrite _ _ (LawfulHasVal.valueOfTy_isVal _ _ _ hv) hx hoth
  | eval_assert_pass _ _ => exact hsv
  | eval_assert_fail _ _ => exact hsv
  | eval_assume _ _ => exact hsv
  | eval_cover _ => exact hsv

/-- Event-trace analogue of `evalCmd_storeWellDefined`: an `EvalCmdE` step leaves
a store that holds only values.  `assert`/`assume`/`cover` keep the store;
`init`/`set` write a value. -/
theorem evalCmdE_storeWellDefined {P : PureExpr} [HasFvar P] [HasBool P] [HasBoolOps P]
    [LawfulHasVal P]
    {f : P.Factory} {σ σ' : SemanticStore P} {c : Cmd P} {emitted : Trace P}
    (hval : WellFormedSemanticEvalVal (P := P) f)
    (h : EvalCmdE P f σ c σ' emitted) (hsv : WellFormedStore σ f) :
    WellFormedStore σ' f := by
  have hwrite : ∀ (x : P.Ident) (v : P.Expr), HasVal.value f v →
      σ' x = some v → (∀ y, x ≠ y → σ' y = σ y) → WellFormedStore σ' f := by
    intro x v hv hx hoth z w hz
    by_cases hzx : x = z
    · subst hzx; rw [hx] at hz; cases hz; exact hv
    · rw [hoth z hzx] at hz; exact hsv z w hz
  cases h with
  | eval_init heval hinit _ =>
    cases hinit with
    | init _ hx hoth => exact hwrite _ _ (hval.outputsAreValues _ _ σ hsv heval) hx hoth
  | eval_init_unconstrained hinit hv _ =>
    cases hinit with
    | init _ hx hoth =>
      exact hwrite _ _ (LawfulHasVal.valueOfTy_isVal _ _ _ hv) hx hoth
  | eval_set heval hup _ =>
    cases hup with
    | update _ hx hoth => exact hwrite _ _ (hval.outputsAreValues _ _ σ hsv heval) hx hoth
  | eval_set_nondet hup htyped _ =>
    obtain ⟨_, _, _, _, hv⟩ := htyped
    cases hup with
    | update _ hx hoth =>
      exact hwrite _ _ (LawfulHasVal.valueOfTy_isVal _ _ _ hv) hx hoth
  | eval_assert => exact hsv
  | eval_assume => exact hsv
  | eval_cover => exact hsv
/-- Event-producing command evaluation emits exactly the trace selected by the
command and its input snapshot. -/
theorem EvalCmdE.emitted_eq {P : PureExpr} [HasFvar P] [HasBool P]
    {f : P.Factory} {σ σ' : SemanticStore P} {c : Cmd P} {emitted : Trace P}
    (h : EvalCmdE P f σ c σ' emitted) :
    emitted = Cmd.emittedEvents P c f σ := by
  cases h <;> rfl

/-- Forgetting the failure result of an existing command execution yields an
event-producing execution with the same resulting store and exactly the trace
selected by `Cmd.emittedEvents` from the command and its input snapshot.

The converse does not hold in general because `EvalCmdE` treats assertions and
assumptions as unconditional observations, while `EvalCmd` requires the partial
evaluator to reduce them to a Boolean. -/
theorem EvalCmd.toEvalCmdE {P : PureExpr} [HasFvar P] [HasBool P] [HasBoolOps P]
    {f : P.Factory} {σ σ' : SemanticStore P} {c : Cmd P} {failed : Bool}
    (h : EvalCmd P f σ c σ' failed) :
    EvalCmdE P f σ c σ' (Cmd.emittedEvents P c f σ) := by
  cases h with
  | eval_init heval hinit htyped hvar => exact .eval_init heval hinit htyped hvar
  | eval_init_unconstrained hinit hval hvar =>
      exact .eval_init_unconstrained hinit hval hvar
  | eval_set heval hupdate htyped hvar => exact .eval_set heval hupdate htyped hvar
  | eval_set_nondet hupdate hval hvar => exact .eval_set_nondet hupdate hval hvar
  | eval_assert_pass _ _ => exact .eval_assert
  | eval_assert_fail _ _ => exact .eval_assert
  | eval_assume _ _ => exact .eval_assume
  | eval_cover _ => exact .eval_cover

/-! ## List-level store relations

Properties of `EvalExpressions`, `ReadValues`, `UpdateStates` and `InitStates`,
with the single-slot `UpdateState` / `InitState` facts they rest on.
-/

/-- Initializing distinct store slots with values preserves store well-formedness. -/
theorem initStates_preserves_wf {P : PureExpr} [HasVal P] {fac : P.Factory} :
    ∀ {ids : List P.Ident} {vals : List P.Expr} {σ σ' : SemanticStore P},
      InitStates σ ids vals σ' →
      WellFormedStore σ fac →
      (∀ v ∈ vals, HasVal.value fac v) →
      WellFormedStore σ' fac := by
  intro ids vals σ σ' h
  induction h with
  | init_none => exact fun hσ _ => hσ
  | @init_some σ0 x v σ1 xs vs σ2 hinit hrest ih =>
    intro hσ hvals
    refine ih ?_ (fun w hw => hvals w (List.mem_cons_of_mem _ hw))
    intro w vw hw
    cases hinit with
    | init _hxnone hxv hxoth =>
      by_cases hwx : w = x
      · subst hwx
        rw [hxv] at hw
        obtain rfl := Option.some.inj hw
        exact hvals _ List.mem_cons_self
      · rw [hxoth w (Ne.symm hwx)] at hw
        exact hσ w vw hw

/-- Initializing no slots leaves the store unchanged. -/
theorem InitStatesEmpty :
  @InitStates P σ [] [] σ' → σ = σ' := by
  intros H; cases H <;> simp

/-- Updating no slots leaves the store unchanged. -/
theorem UpdateStatesEmpty :
  @UpdateStates P σ [] [] σ' → σ = σ' := by
  intros H; cases H <;> simp

/-- Updating one slot keeps every undefined key undefined. -/
theorem UpdateStateNotDefMonotone
  {P : PureExpr} {σ σ' : SemanticStore P}
  {vs : List P.Ident} {e : P.Expr} {v : P.Ident} :
  isNotDefined σ vs →
  UpdateState P σ v e σ' →
  isNotDefined σ' vs := by
  intros Hdef Heval
  cases Heval with
  | update Hold HH Hsome =>
  simp only [isNotDefined, ne_eq] at *
  intros v' Hv'
  by_cases Heq: (v = v')
  case pos =>
    simp_all
  case neg =>
    specialize Hsome v' Heq
    specialize Hdef v'
    simp only [Hsome]
    exact Hdef Hv'

/-- Updating a list of slots keeps every undefined key undefined. -/
theorem UpdateStatesNotDefMonotone
  {P : PureExpr} {σ σ' : SemanticStore P}
  {vs : List P.Ident} {es' : List P.Expr} {vs' : List P.Ident} :
  isNotDefined σ vs →
  UpdateStates σ vs' es' σ' →
  isNotDefined σ' vs := by
  intros Hdef Heval
  induction Heval with
  | update_none => assumption
  | update_some Hup Hups ih =>
  intros v Hv
  apply ih
  exact UpdateStateNotDefMonotone Hdef Hup
  assumption

/-- A key undefined after updating one slot was undefined before. -/
theorem UpdateStateNotDefMonotone'
  {P : PureExpr} {σ σ' : SemanticStore P}
  {vs : List P.Ident} {e : P.Expr} {v : P.Ident} :
  isNotDefined σ' vs →
  UpdateState P σ v e σ' →
  isNotDefined σ vs := by
  intros Hdef Heval
  cases Heval with
  | update Hold HH Hsome =>
  simp only [isNotDefined, ne_eq] at *
  intros v' Hv'
  by_cases Heq: (v = v')
  case pos =>
    simp_all
  case neg =>
    specialize Hsome v' Heq
    specialize Hdef v'
    simp only [← Hsome]
    exact Hdef Hv'

/-- A key undefined after updating a list of slots was undefined before. -/
theorem UpdateStatesNotDefMonotone'
  {P : PureExpr} {σ σ' : SemanticStore P}
  {vs : List P.Ident} {es' : List P.Expr} {vs' : List P.Ident} :
  isNotDefined σ' vs →
  UpdateStates σ vs' es' σ' →
  isNotDefined σ vs := by
  intros Hdef Heval
  induction Heval with
  | update_none => assumption
  | update_some Hup Hups ih =>
  intros v Hv
  apply UpdateStateNotDefMonotone' (ih Hdef) Hup
  exact Hv

/-- The updated slot is defined after the update. -/
theorem UpdateStateDefined
  {P : PureExpr} {σ σ' : SemanticStore P} {e : P.Expr} {v : P.Ident} :
  @UpdateState P σ v e σ' →
  isDefined σ' [v] := by
  intros Hup
  cases Hup with
  | update Hold Hsome Hall =>
  simp [isDefined, Option.isSome, Hsome]

/-- The updated slot is defined before the update. -/
theorem UpdateStateDefined'
  {P : PureExpr} {σ σ' : SemanticStore P} {e : P.Expr} {v : P.Ident} :
  @UpdateState P σ v e σ' →
  isDefined σ [v] := by
  intros Hup
  cases Hup with
  | update Hold Hsome Hall =>
  simp only [isDefined, List.mem_cons, List.not_mem_nil, or_false, Option.isSome, forall_eq]
  split <;> simp_all

/-- Updating a list of slots keeps every defined key defined. -/
theorem UpdateStatesDefMonotone
  {P : PureExpr} {σ σ' : SemanticStore P}
  {vs : List P.Ident} {es' : List P.Expr} {vs' : List P.Ident} :
  isDefined σ vs →
  UpdateStates σ vs' es' σ' →
  isDefined σ' vs := by
  intros Hdef Heval
  induction Heval with
  | update_none => assumption
  | update_some Hup Hups ih =>
  intros v Hv
  apply ih
  exact UpdateStateDefMonotone Hdef Hup
  assumption

/-- A key defined after updating one slot was defined before. -/
theorem UpdateStateDefMonotone'
  {P : PureExpr} {σ σ' : SemanticStore P}
  {vs : List P.Ident} {e : P.Expr} {v : P.Ident} :
  isDefined σ' vs →
  UpdateState P σ v e σ' →
  isDefined σ vs := by
  intros Hdef Heval
  cases Heval with
  | update Hold HH Hsome =>
  simp only [isDefined, ne_eq] at *
  intros v' Hv'
  by_cases Heq: (v = v')
  case pos =>
    simp only [Option.isSome]
    simp only [Heq] at *
    split <;> simp_all
  case neg =>
    specialize Hsome v' Heq
    specialize Hdef v'
    simp only [← Hsome]
    exact Hdef Hv'

/-- A key defined after updating a list of slots was defined before. -/
theorem UpdateStatesDefMonotone'
  {P : PureExpr} {σ σ' : SemanticStore P}
  {vs : List P.Ident} {es' : List P.Expr} {vs' : List P.Ident} :
  isDefined σ' vs →
  UpdateStates σ vs' es' σ' →
  isDefined σ vs := by
  intros Hdef Heval
  induction Heval with
  | update_none => assumption
  | update_some Hup Hups ih =>
  intros v Hv
  apply UpdateStateDefMonotone' (ih Hdef) Hup
  exact Hv

/-- Every updated slot is defined after the updates. -/
theorem UpdateStatesDefined :
  UpdateStates σ vs es σ' →
  isDefined σ' vs := by
  intros Hhavoc
  induction vs generalizing es σ σ'
  case nil => simp [isDefined]
  case cons h t ih =>
    cases Hhavoc with
    | @update_some _ _ v σ₁ _ _ Hup Hhav =>
    apply isDefinedCons
    apply UpdateStatesDefMonotone <;> try assumption
    exact UpdateStateDefined Hhav
    apply ih <;> assumption

/-- Every updated slot is defined before the updates. -/
theorem UpdateStatesDefined' :
  UpdateStates σ vs es σ' →
  isDefined σ vs := by
  intros Hhavoc
  induction vs generalizing es σ σ'
  case nil => simp [isDefined]
  case cons h t ih =>
    cases Hhavoc with
    | update_some Hup Hups =>
    apply isDefinedCons
    exact UpdateStateDefined' Hup
    apply UpdateStatesDefMonotone'
    apply ih Hups
    exact UpdateStates.update_some Hup UpdateStates.update_none

/-- Every initialized slot is undefined before the initialization. -/
theorem InitStatesNotDefined :
  InitStates σ hs vs σ' → isNotDefined σ hs := by
  intros Hinit
  induction Hinit <;> simp only [isNotDefined, List.not_mem_nil, false_implies, implies_true,
    List.mem_cons, forall_eq_or_imp]
  case init_some x v σ' xs vs σ'' Hinit Hinits ih =>
    simp only [isNotDefined] at *
    cases Hinit with
    | init Hnone Hsome Heq =>
    refine ⟨Hnone, ?_⟩
    intros x' Hin
    by_cases Heqx : x = x' <;> simp_all only [ne_eq, reduceCtorEq]
    specialize Heq x' Heqx
    specialize ih x' Hin
    simp_all

/-- The slots initialized by `InitStates` are pairwise distinct. -/
theorem InitStatesNodup :
  InitStates σ hs vs σ' → hs.Nodup := by
  intros Hinit
  induction Hinit <;> simp_all only [List.nodup_nil, List.nodup_cons, and_true]
  case init_some x v σ' xs vs σ'' Hinit Hinits ih =>
  apply Not.intro
  intros Hin
  cases Hinit with
  | init Hnone Hsome Heq =>
    have Hnd := InitStatesNotDefined Hinits
    specialize Hnd x Hin
    simp_all

/-- Initializing a slot with a value has a unique resulting store. -/
theorem InitStateInjective :
  InitState P σ k1 k2 σ' →
  InitState P σ k1 k2 σ'' →
  σ' = σ'' := by
  intros Hinit1 Hinit2
  cases Hinit1
  case init Hnone1 Heq1 Hsome1 =>
  cases Hinit2
  case init Hnone2 Heq2 Hsome2 =>
  funext x
  by_cases H : k1 = x
  · simp_all
  · rw [Heq1, Heq2] <;> simp_all

/-- Initializing a list of slots with a list of values has a unique resulting store. -/
theorem InitStatesInjective :
  InitStates σ k1 k2 σ' →
  InitStates σ k1 k2 σ'' →
  σ' = σ'' := by
  intros Hinit1 Hinit2
  induction Hinit1 generalizing σ''
  case init_none =>
    have Heq := InitStatesEmpty Hinit2
    simp_all
  case init_some Hinit Hinits ih =>
    cases Hinit2 with
    | init_some Hinit2 Hinits2 =>
    apply ih
    have Hinj := InitStateInjective Hinit Hinit2
    simp_all

/-- Every expression returned by `ReadValues` is a value in its factory. -/
theorem ReadValues.all_values
    {P : PureExpr} [HasVal P] {f : P.Factory} {σ : SemanticStore P}
    {ks : List P.Ident} {vs : List P.Expr} (h : ReadValues f σ ks vs) :
    ∀ v ∈ vs, HasVal.value f v := by
  induction h with
  | read_none => simp
  | read_some _ hval _ ih =>
    intro v hv
    cases hv with
    | head => exact hval
    | tail _ hmem => exact ih v hmem

/-- Reading the same keys from the same store yields the same value list. -/
theorem ReadValuesInjective {P : PureExpr} [HasVal P] {f : P.Factory}
  {σ : SemanticStore P} {ks : List P.Ident} {vs vs' : List P.Expr} :
  ReadValues f σ ks vs →
  ReadValues f σ ks vs' →
  vs = vs' := by
  intros Hrd1 Hrd2
  induction Hrd1 generalizing vs'
  case read_none =>
    cases Hrd2
    rfl
  case read_some Hrd Hrds ih =>
    cases Hrd2 with
    | read_some Hrd2 _ Hrds2 =>
    congr
    · simp_all
    · apply ih
      simp_all

/-- Concatenating two reads from one store reads the concatenated keys and values. -/
theorem ReadValuesApp {P : PureExpr} [HasVal P] {f : P.Factory}
  {σ : SemanticStore P} {k1 k2 : List P.Ident} {v1 v2 : List P.Expr} :
  ReadValues f σ k1 v1 →
  ReadValues f σ k2 v2 →
  ReadValues f σ (k1 ++ k2) (v1 ++ v2) := by
  intros Hrd1 Hrd2
  induction Hrd1 <;> simp_all only [List.nil_append, List.cons_append]
  case read_some Hsome Hrd Hrds =>
  constructor <;> assumption

/-- A read over appended key lists splits into corresponding value lists and reads. -/
theorem ReadValuesAppKeys' {P : PureExpr} [HasVal P] {f : P.Factory}
  {σ : SemanticStore P} {k1 k2 : List P.Ident} {vs : List P.Expr} :
  ReadValues f σ (k1 ++ k2) vs →
  exists v1 v2,
  v1 ++ v2 = vs ∧
  ReadValues f σ k1 v1 ∧
  ReadValues f σ k2 v2 := by
  intros Hrd
  induction vs generalizing k1 k2
  case nil =>
    exists [],[]
    generalize Hk12 : k1 ++ k2 = k12 at Hrd
    cases Hrd
    simp_all only [List.append_eq_nil_iff, List.append_nil, and_self, true_and]
    constructor
  case cons vh vt vih =>
    cases k1
    case nil =>
      exists [],vh :: vt
      simp_all only [List.nil_append, and_true, true_and]
      constructor
    case cons kh kt =>
      cases Hrd with
      | read_some Hsome _ Hrd =>
        specialize vih Hrd
        cases vih with
        | intro v1' vih =>
        cases vih with
        | intro v2 vih =>
        exists vh::v1',v2
        simp_all only [List.append_eq, List.cons_append, and_true, true_and]
        constructor <;> simp_all

/-- A read returns exactly one value for each requested key. -/
theorem ReadValuesLength {P : PureExpr} [HasVal P] {f : P.Factory}
  {σ : SemanticStore P} {ks : List P.Ident} {vs : List P.Expr} :
  ReadValues f σ ks vs →
  ks.length = vs.length := by
  intros Hrd
  induction Hrd <;> simp_all

/-- `InitStates` pairs each initialized slot with exactly one value. -/
theorem InitStatesLength :
  InitStates σ ks vs σ' →
  ks.length = vs.length := by
  intros Hinit
  induction Hinit <;> simp_all

/-- `UpdateStates` pairs each updated slot with exactly one value. -/
theorem UpdateStatesLength {P : PureExpr}
  {σ σ' : Imperative.SemanticStore P}
  {ks : List P.Ident}
  {vs : List P.Expr}
  :
  UpdateStates (P:=P) σ ks vs σ' →
  List.length ks = List.length vs := by
  intros Hup
  induction Hup <;> simp_all

/-- Initializing a fresh slot preserves every existing `ReadValues` derivation. -/
theorem InitStateReadValuesMonotone {P : PureExpr} [HasVal P] {f : P.Factory}
  {σ σ' : SemanticStore P}
  {ks : List P.Ident} {vs : List P.Expr} {e : P.Expr} {v : P.Ident} :
  ReadValues f σ ks vs →
  InitState P σ v e σ' →
  ReadValues f σ' ks vs := by
  intros Hdef Heval
  cases Heval with
  | init Hold HH Hsome =>
  induction Hdef
  case read_none => constructor
  case read_some xs vs' x v' Hsome' Hrd Hrds =>
  constructor <;> simp_all only [ne_eq]
  rw [Hsome] <;> try simp_all only
  apply Not.intro
  intros Heq
  simp_all

/-- Initializing several fresh slots preserves every existing `ReadValues` derivation. -/
theorem InitStatesReadValuesMonotone
  {P : PureExpr} [HasVal P] {f : P.Factory} {σ σ' : SemanticStore P}
  {ks : List P.Ident} {vs : List P.Expr}
  {es' : List P.Expr} {vs' : List P.Ident} :
  ReadValues f σ ks vs →
  InitStates σ vs' es' σ' →
  ReadValues f σ' ks vs := by
  intros Hdef Heval
  induction Heval with
  | init_none => assumption
  | init_some Hinit Hinits ih =>
    apply ih
    apply InitStateReadValuesMonotone <;> assumption

/-- Updating a slot outside the requested keys preserves a `ReadValues` derivation. -/
theorem UpdateStateReadValuesMonotone {P : PureExpr} [HasVal P] {f : P.Factory}
  {σ σ' : SemanticStore P}
  {ks : List P.Ident} {vs : List P.Expr} {e : P.Expr} {v : P.Ident} :
  ¬ v ∈ ks →
  ReadValues f σ ks vs →
  UpdateState P σ v e σ' →
  ReadValues f σ' ks vs := by
  intros Hnin Hdef Heval
  cases Heval with
  | update Hold HH Hsome =>
  induction Hdef
  case read_none => constructor
  case read_some xs vs' x v' Hsome' Hrd Hrds =>
  constructor <;> simp_all

/-- Updating distinct slots disjoint from the requested keys preserves a `ReadValues`
derivation. -/
theorem UpdateStatesReadValuesMonotone
  {P : PureExpr} [HasVal P] {f : P.Factory} {σ σ' : SemanticStore P}
  {ks : List P.Ident} {vs : List P.Expr}
  {es' : List P.Expr} {vs' : List P.Ident} :
  (ks ++ vs').Nodup →
  ReadValues f σ ks vs →
  UpdateStates σ vs' es' σ' →
  ReadValues f σ' ks vs := by
  intros Hnd Hdef Heval
  induction Heval with
  | update_none => assumption
  | update_some Hinit Hinits ih =>
    have Hnd' := nodup_middle Hnd
    simp_all only [List.nodup_cons, List.mem_append, not_or, forall_const]
    apply ih
    apply UpdateStateReadValuesMonotone _ Hdef Hinit <;> try assumption
    simp_all

/-- Initializing one slot with a value makes that value readable
    from the slot in the resulting store. -/
theorem InitStateReadValues {P : PureExpr} [HasVal P] {f : P.Factory}
  {σ σ' : SemanticStore P} {v : P.Ident} {e : P.Expr} :
  HasVal.value f e →
  InitState P σ v e σ' →
  ReadValues f σ' [v] [e] := by
  intro hval Hinit
  cases Hinit with
  | init _ Hsome _ => exact .read_some Hsome hval .read_none

/-- Updating one slot with a value makes that value readable
    from the slot in the resulting store. -/
theorem UpdateStateReadValues {P : PureExpr} [HasVal P] {f : P.Factory}
  {σ σ' : SemanticStore P} {v : P.Ident} {e : P.Expr} :
  HasVal.value f e →
  UpdateState P σ v e σ' →
  ReadValues f σ' [v] [e] := by
  intro hval Hupdate
  cases Hupdate with
  | update _ Hsome _ => exact .read_some Hsome hval .read_none

/-- Initializing slots from values makes those values readable
    at the corresponding slots in the resulting store. -/
theorem InitStatesReadValues {P : PureExpr} [HasVal P] {f : P.Factory}
  {σ σ' : SemanticStore P} {vs : List P.Ident} {es : List P.Expr} :
  (∀ v ∈ es, HasVal.value f v) →
  InitStates σ vs es σ' →
  ReadValues f σ' vs es := by
  intro hvals Hinit
  induction Hinit with
  | init_none => exact .read_none
  | init_some Hinit Hinits ih =>
    rename_i x v σ₁ xs es' σ''
    have hv : HasVal.value f v := hvals v List.mem_cons_self
    have hrd : ReadValues f σ'' [x] [v] :=
      InitStatesReadValuesMonotone (σ := σ₁)
        (InitStateReadValues hv Hinit) Hinits
    cases hrd with
    | read_some hx _ _ =>
      exact .read_some hx hv
        (ih (fun w hw => hvals w (List.mem_cons_of_mem _ hw)))

/-- Updating distinct slots from values makes those values
    readable at the corresponding slots in the resulting store. -/
theorem UpdateStatesReadValues {P : PureExpr} [HasVal P] {f : P.Factory}
  {σ σ' : SemanticStore P} {vs : List P.Ident} {es : List P.Expr} :
  vs.Nodup →
  (∀ v ∈ es, HasVal.value f v) →
  UpdateStates σ vs es σ' →
  ReadValues f σ' vs es := by
  intro hnd hvals Hupdates
  induction Hupdates with
  | update_none => exact .read_none
  | update_some Hupdate Hupdates ih =>
    rename_i x v σ₁ xs es' σ''
    have hv : HasVal.value f v := hvals v List.mem_cons_self
    have hrd : ReadValues f σ'' [x] [v] :=
      UpdateStatesReadValuesMonotone (σ := σ₁) hnd
        (UpdateStateReadValues hv Hupdate) Hupdates
    cases hrd with
    | read_some hx _ _ =>
      exact .read_some hx hv
        (ih hnd.tail (fun w hw => hvals w (List.mem_cons_of_mem _ hw)))

/-- Updating a different slot preserves the value stored at a key. -/
theorem UpdateStateSomeMonotone
  {P : PureExpr} {σ σ' : SemanticStore P}
  {k' : P.Ident} {v' : P.Expr} {e : P.Expr} {v : P.Ident} :
  v ≠ k' →
  σ k' = some v' →
  UpdateState P σ v e σ' →
  σ' k' = some v' := by
  intro hne hdef hupdate
  cases hupdate with
  | update _ _ hother => simpa [hother k' hne] using hdef

/-- Updating a list of slots not containing a key preserves the value stored at that key. -/
theorem UpdateStatesSomeMonotone
  {P : PureExpr} {σ σ' : SemanticStore P}
  {k' : P.Ident} {v' : P.Expr}
  {ks': List P.Ident} {vs': List P.Expr} :
  ¬ k' ∈ ks' →
  σ k' = some v' →
  UpdateStates σ ks' vs' σ' →
  σ' k' = some v' := by
  intros Hnin Hsome Hinit
  induction Hinit <;> try simp_all only [List.not_mem_nil, not_false_eq_true, List.mem_cons,
    not_or, forall_const]
  next Hinit Hinits ih =>
  apply ih
  apply UpdateStateSomeMonotone ?_ Hsome Hinit
  exact fun a => Hnin.1 (Eq.symm a)

/-- Initializing a slot preserves the value stored at an already defined key. -/
theorem InitStateSomeMonotone
  {P : PureExpr} {σ σ' : SemanticStore P}
  {k' : P.Ident} {v' : P.Expr} {e : P.Expr} {v : P.Ident} :
  σ k' = some v' →
  InitState P σ v e σ' →
  σ' k' = some v' := by
  intro hdef hinit
  cases hinit with
  | init hnone _ hother =>
    by_cases h : v = k'
    · subst h; simp_all
    · simpa [hother k' h] using hdef

/-- A key other than the initialized slot stores the same value before the initialization. -/
theorem InitStateSomeMonotone'
  {P : PureExpr} {σ σ' : SemanticStore P}
  {k' : P.Ident} {v' : P.Expr} {e : P.Expr} {v : P.Ident} :
  k' ≠ v →
  σ' k' = some v' →
  InitState P σ v e σ' →
  σ k' = some v' := by
  intro hne hdef hinit
  cases hinit with
  | init _ _ hother => simpa [hother k' (Ne.symm hne)] using hdef

/-- Initializing a list of slots preserves the value stored at an already defined key. -/
theorem InitStatesSomeMonotone
  {P : PureExpr} {σ σ' : SemanticStore P}
  {k' : P.Ident} {v' : P.Expr}
  {ks': List P.Ident} {vs': List P.Expr} :
  σ k' = some v' →
  InitStates σ ks' vs' σ' →
  σ' k' = some v' := by
  intros Hsome Hinit
  induction Hinit <;> try simp_all only
  next Hinit Hinits ih =>
  apply ih
  apply InitStateSomeMonotone Hsome Hinit

/-- A key outside the initialized slots stores the same value before the initialization. -/
theorem InitStatesSomeMonotone'
  {P : PureExpr} {σ σ' : SemanticStore P}
  {k' : P.Ident} {v' : P.Expr}
  {ks': List P.Ident} {vs': List P.Expr} :
  ¬ k' ∈ ks' →
  σ' k' = some v' →
  InitStates σ ks' vs' σ' →
  σ k' = some v' := by
  intros Hnin Hsome Hinit
  induction Hinit
  case init_none => simp_all
  case init_some Hinit Hinits ih =>
  apply InitStateSomeMonotone' ?_ ?_ Hinit
  · simp_all
  · apply ih <;> simp_all

/-- If a store defines every requested key and all of its bindings are values, those keys admit a corresponding `ReadValues` derivation. -/
theorem isDefinedReadValues {P : PureExpr} [HasVal P] {f : P.Factory}
  {σ : SemanticStore P} {ks : List P.Ident} :
  WellFormedStore σ f →
  isDefined σ ks →
  ∃ vs, ReadValues f σ ks vs := by
  intro hwf hdef
  induction ks with
  | nil => exact ⟨[], .read_none⟩
  | cons x xs ih =>
    have hx := hdef x List.mem_cons_self
    rw [Option.isSome_iff_exists] at hx
    obtain ⟨v, hx⟩ := hx
    obtain ⟨vs, hvs⟩ := ih (fun y hy => hdef y (List.mem_cons_of_mem _ hy))
    exact ⟨v :: vs, .read_some hx (hwf x v hx) hvs⟩

/-- Successfully reading a key list implies that every requested key is defined in
the store. -/
theorem ReadValuesIsDefined {P : PureExpr} [HasVal P] {f : P.Factory}
  {σ : SemanticStore P} {ks : List P.Ident} {vs : List P.Expr} :
  ReadValues f σ ks vs →
  isDefined σ ks := by
  intros Hrd
  induction Hrd <;> simp only [isDefined, List.not_mem_nil, Option.isSome, false_implies,
    implies_true, List.mem_cons, forall_eq_or_imp]
  apply And.intro
  · split <;> simp_all
  · intros a Hin
    split <;> simp_all only [Bool.false_eq_true]
    next ih ex Hnone =>
    specialize ih a Hin
    simp_all

/-- Initializing slots in the target store preserves a defined store substitution. -/
theorem substStoresInitsInv :
substDefined σ σ' substs →
substStores σ σ' substs →
InitStates σ' ks vs σ'' →
substStores σ σ'' substs := by
  intros Hdef Hsubst Hinit
  simp only [substDefined, substStores] at *
  intros k1 k2 Hin
  induction Hinit generalizing σ
  case init_none =>
    exact Hsubst k1 k2 Hin
  case init_some Hinit Hinits ih =>
    simp only [Hsubst k1 k2 Hin]
    specialize Hdef k1 k2 Hin
    simp only [Option.isSome] at Hdef
    split at Hdef <;> simp_all only [true_and, Bool.false_eq_true, false_and]
    split at Hdef <;> simp_all only [Bool.false_eq_true]
    next x val Hsome =>
    have Hsome' := InitStateSomeMonotone Hsome Hinit
    have Hsome'' := InitStatesSomeMonotone Hsome' Hinits
    simp_all

/-- Initializing slots in the source store preserves a defined store substitution, with the
initialized store as the new source. -/
theorem substStoresInitsInv' :
substDefined σ σ' substs →
substStores σ σ' substs →
InitStates σ ks vs σ'' →
substStores σ'' σ' substs := by
  intros k1 k2 Hin
  rw [← substSwapId _ substs]
  apply substStoresFlip
  apply substStoresInitsInv <;> try assumption
  · exact substDefinedFlip k1
  · exact substStoresFlip k2

/-- Updating a target-store slot that no substitution pair targets preserves the
substitution. -/
theorem substStoresUpdateInv {k : P.Ident} {substs : List (P.Ident × P.Ident)}:
¬ k ∈ substs.unzip.2 →
substStores (P:=P) σ σ' substs →
UpdateState (P:=P) σ' k v σ'' →
substStores (P:=P) σ σ'' substs := by
  intros Hnin Hsubst Hinit
  simp only [List.unzip_snd, List.mem_map, Prod.exists, exists_eq_right, not_exists,
    substStores] at *
  intros k1 k2 Hin
  cases Hinit with
  | update Hnone Hsome' Heq =>
  rw [Heq] <;> simp_all only [ne_eq]
  rw [Hsubst] <;> simp_all only
  intros Heq'
  specialize Hnin k1
  simp_all

/-- Updating target-store slots that no substitution pair targets preserves the
substitution. -/
theorem substStoresUpdatesInv :
ks.Disj substs.unzip.2 →
substStores σ σ' substs →
UpdateStates σ' ks vs σ'' →
substStores σ σ'' substs := by
  intros Hnin Hsubst Hup
  simp only [List.unzip_snd, substStores] at *
  intros k1 k2 Hin
  induction Hup generalizing σ
  case update_none =>
    exact Hsubst k1 k2 Hin
  case update_some σ x v σ' xs vs σ₁ Hup Hinits ih =>
    have Hnin : ¬ x ∈ substs.unzip.2 := by
      simp only [List.Disj, List.mem_cons, List.mem_map, Prod.exists, exists_eq_right, imp_false,
        not_exists, forall_eq_or_imp] at Hnin
      intros Hin
      have Hprod := List.mem_zip_2 (l₁:=substs.unzip.fst) (by simp) Hin
      rw [List.zip_unzip] at Hprod
      cases Hprod with
      | intro w Hprod =>
      have HH := Hnin.1 w
      contradiction
    have HH := substStoresUpdateInv (σ:=σ) Hnin Hsubst Hup
    apply ih HH
    simp only [List.Disj, List.mem_map, Prod.exists, exists_eq_right, imp_false, not_exists,
      List.mem_cons, forall_eq_or_imp, List.unzip_snd] at *
    simp_all

/-- Updating source-store slots that no substitution pair reads from preserves the
substitution, with the updated store as the new source. -/
theorem substStoresUpdatesInv' :
ks.Disj substs.unzip.1 →
substStores σ σ' substs →
UpdateStates σ ks vs σ'' →
substStores σ'' σ' substs := by
  intros Hdisj Hsubst Hup
  rw [← substSwapId _ substs]
  apply substStoresFlip
  apply substStoresUpdatesInv <;> try assumption
  · intros a Hin Hin'
    specialize Hdisj Hin
    simp only [substSwap, List.unzip_snd, List.map_map, List.mem_map, Function.comp_apply,
      Prod.snd_swap, Prod.exists, exists_and_right, exists_eq_right] at Hin'
    simp_all
  · exact substStoresFlip Hsubst

/-- Store substitutions under a head pair and under a zipped tail combine into one substitution
under the whole list. -/
theorem substStoresCons :
  substStores σ σ' [(h,h')] →
  substStores σ σ' (List.zip t t') →
  substStores σ σ' ((h,h') :: (List.zip t t')) := by
  intros Hh Ht
  intros k1 k2 Hin
  simp only [List.mem_cons, Prod.mk.injEq] at Hin
  cases Hin with
  | inl Hin =>
    apply Hh
    simp_all
  | inr Hin =>
    apply Ht
    simp_all

/-- If two stores read the same values at respective key lists, the stores agree
under the substitution that zips those keys. -/
theorem ReadValuesSubstStores {P : PureExpr} [HasVal P] {f : P.Factory}
  {σ σ' : SemanticStore P} {ks ks' : List P.Ident} {vs : List P.Expr} :
  ReadValues f σ ks vs →
  ReadValues f σ' ks' vs →
  Imperative.substStores σ σ' (List.zip ks ks') := by
  intros H1 H2
  induction vs generalizing ks ks'
  case nil =>
    cases H1
    cases H2
    intros h1 h2 Hin
    cases Hin
  case cons h t ih =>
    cases ks
    cases H1
    cases ks'
    cases H2
    cases H1 with
    | read_some Hh _ Ht =>
    cases H2 with
    | read_some Hh' _ Ht' =>
    simp only [List.zip_cons_cons]
    apply substStoresCons
    · simp only [substStores, List.mem_cons, Prod.mk.injEq, List.not_mem_nil, or_false, and_imp,
        forall_eq_apply_imp_iff, forall_eq]
      simp_all
    · exact ih Ht Ht'

/-- Initializing a list of slots keeps every defined key defined. -/
theorem InitStatesDefMonotone :
  isDefined σ vs →
  InitStates σ vs' es' σ' →
  isDefined σ' vs := by
  intros Hdef Hhavoc
  induction Hhavoc with
  | init_some Hup Hhav ih =>
  apply ih
  apply InitStateDefMonotone <;> assumption
  | init_none => simp_all

/-- A key other than the initialized slot that is defined after the initialization was
defined before. -/
theorem InitStateDefMonotone'
  {P : PureExpr} {σ σ' : SemanticStore P}
  {vs : List P.Ident} {e : P.Expr} {v : P.Ident} :
  ¬ v ∈ vs →
  isDefined σ' vs →
  InitState P σ v e σ' →
  isDefined σ vs := by
  intros Hnin Hdef Heval
  cases Heval with
  | init Hold HH Hsome =>
  simp only [isDefined, ne_eq] at *
  intros v' Hv'
  by_cases Heq: (v = v')
  case pos =>
    simp only [Option.isSome]
    simp only [Heq] at *
    split <;> simp_all
  case neg =>
    specialize Hsome v' Heq
    specialize Hdef v'
    simp only [← Hsome]
    exact Hdef Hv'

/-- Keys disjoint from the initialized slots that are defined after the initialization were
defined before. -/
theorem InitStatesDefMonotone' :
  vs.Disj vs' →
  isDefined σ' vs →
  InitStates σ vs' es' σ' →
  isDefined σ vs := by
  intros Hdisj Hdef Hhavoc
  induction Hhavoc with
  | init_none => assumption
  | init_some Hup Hhav ih =>
  next σ x v σ' xs' ys' σ'' =>
  apply InitStateDefMonotone' (σ':=σ') <;> try assumption
  · intros Hin
    apply Hdisj Hin
    exact List.mem_cons_self
  · apply ih
    · apply List.Disj.mono_right _ Hdisj
      exact List.sublist_cons_self x xs'
    · assumption

/-- Every initialized slot is defined after the initialization. -/
theorem InitStatesDefined :
  InitStates σ hs vs σ' → isDefined σ' hs := by
  intros Hinit
  induction Hinit <;> simp only [isDefined, List.not_mem_nil, false_implies, implies_true,
    List.mem_cons, forall_eq_or_imp]
  case init_some x v σ' xs vs σ'' Hinit Hinits ih =>
    simp only [isDefined] at *
    cases Hinit with
    | init Hnone Hsome Heq =>
    refine ⟨?_, by simp_all⟩
    have Hdef : isDefined σ'' [x] := by
      apply InitStatesDefMonotone ?_ Hinits
      simp only [isDefined, List.mem_cons, List.not_mem_nil, or_false, Option.isSome, forall_eq]
      split <;> simp_all
    simp only [isDefined, List.mem_cons, List.not_mem_nil, or_false, forall_eq] at Hdef
    assumption

/-- If two stores agree outside `ks`, updating slots `ks'` of the first keeps them agreeing
outside `ks ++ ks'`. -/
theorem InvStoresExceptUpdateStates :
  invStoresExcept σ σ' ks →
  UpdateStates σ ks' vs' σ'' →
  invStoresExcept σ'' σ' (ks ++ ks') := by
  intro Hinv Hup
  induction Hup generalizing ks with
  | update_none => simpa using Hinv
  | @update_some σ₀ x _ σ₁ _ _ _ hu _ ih =>
    cases hu with
    | update _ _ hfr =>
    have Hstep : invStoresExcept σ₁ σ' (ks ++ [x]) := fun ws hws k1 k2 hin => by
      have Hmem := (List.of_mem_zip hin).1
      cases zip_self_eq hin
      rw [hfr k1 fun h => hws (h ▸ Hmem) (by simp)]
      exact Hinv ws (fun a ha hk => hws ha (by simp [hk])) k1 k1 hin
    simpa using ih Hstep

/-- If two stores agree outside `ks`, initializing slots `ks'` of the first keeps them agreeing
outside `ks ++ ks'`. -/
theorem InvStoresExceptInitStates :
  invStoresExcept σ σ' ks →
  InitStates σ ks' vs' σ'' →
  invStoresExcept σ'' σ' (ks ++ ks') := by
  intro Hinv Hup
  induction Hup generalizing ks with
  | init_none => simpa using Hinv
  | @init_some σ₀ x _ σ₁ _ _ _ hu _ ih =>
    cases hu with
    | init _ _ hfr =>
    have Hstep : invStoresExcept σ₁ σ' (ks ++ [x]) := fun ws hws k1 k2 hin => by
      have Hmem := (List.of_mem_zip hin).1
      cases zip_self_eq hin
      rw [hfr k1 fun h => hws (h ▸ Hmem) (by simp)]
      exact Hinv ws (fun a ha hk => hws ha (by simp [hk])) k1 k1 hin
    simpa using ih Hstep

end -- public section
