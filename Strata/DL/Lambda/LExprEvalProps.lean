/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import Strata.DL.Lambda.LExprEval
public import Strata.DL.Lambda.FactoryWF
import all Strata.DL.Lambda.LExprWFProps

import all Strata.DL.Lambda.LExprEval
import all Strata.DL.Lambda.LExprType
import Strata.DL.Lambda.LTyUnifyProps
import all Strata.DL.Lambda.LTyProps
import all Strata.DL.Lambda.Denote.CallOfLFuncDenote
import all Strata.DL.Lambda.Denote.LExprAnnotated
import all Strata.DL.Lambda.LTyUnify
import all Strata.DL.Lambda.FactoryProps
import all Strata.DL.Lambda.LState
public import Strata.DL.Lambda.LStateProps
import all Strata.DL.Lambda.LStateProps
import all Strata.DL.Lambda.LExprWF
import all Strata.DL.Lambda.LExprProps
import Strata.DL.Lambda.OperationalSemanticsProps

/-!
## Properties of the Lambda expression evaluator

- `LExpr.shortCircuitCall?_some` — what a successful short-circuit lookup returns.
- `eval_eraseMetadata_invariant` — expressions that differ only in metadata
  evaluate to results that also differ only in metadata.
- `LExpr.isValue_bool_eq_boolConst` — a value whose factory-checked type is
  `bool` is a Boolean constant, when no constructor produces a Boolean (Part VI).
-/

namespace Lambda
open Strata
open Std (ToFormat Format format)

variable {Tbase : LExprParams}
  [DecidableEq Tbase.IDMeta]
  [Inhabited Tbase.IDMeta]
  [Traceable LExpr.EvalProvenance Tbase.Metadata]

omit [DecidableEq Tbase.IDMeta] [Inhabited Tbase.IDMeta]
  [Traceable LExpr.EvalProvenance Tbase.Metadata] in
/-- If `shortCircuitCall?` returns `(a, rest, ceval)`, then `args = a :: rest` and
    `lfunc.concreteEval = some ceval`. -/
public theorem LExpr.shortCircuitCall?_some {lfunc : LFunc Tbase} {args : List (LExpr Tbase.mono)}
    {a : LExpr Tbase.mono} {rest : List (LExpr Tbase.mono)}
    {ceval : Tbase.Metadata → List (LExpr Tbase.mono) → Option (LExpr Tbase.mono)}
    (h : LExpr.shortCircuitCall? lfunc args = some (a, rest, ceval)) :
    args = a :: rest ∧ lfunc.concreteEval = some ceval := by
  unfold LExpr.shortCircuitCall? at h
  split at h
  · split at h
    · rename_i a' rest' ceval' h_ce
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact ⟨rfl, h_ce⟩
    · simp at h
  · simp at h

omit [DecidableEq Tbase.IDMeta] [Inhabited Tbase.IDMeta]
  [Traceable LExpr.EvalProvenance Tbase.Metadata] in
/-- `shortCircuitCall?` declines every argument list of the length of one it declines. -/
private theorem LExpr.shortCircuitCall?_none_of_length {lfunc : LFunc Tbase}
    {args₁ args₂ : List (LExpr Tbase.mono)}
    (h : LExpr.shortCircuitCall? lfunc args₁ = none) (hl : args₁.length = args₂.length) :
    LExpr.shortCircuitCall? lfunc args₂ = none := by
  unfold LExpr.shortCircuitCall? at h ⊢
  split at h
  · rename_i hsc
    rw [ite_eq_left hsc]
    cases args₁ <;> cases args₂ <;> cases hce : lfunc.concreteEval <;> simp_all
  · rename_i hsc
    rw [ite_eq_right hsc]

omit [DecidableEq Tbase.IDMeta] [Inhabited Tbase.IDMeta]
  [Traceable LExpr.EvalProvenance Tbase.Metadata] in
/-- `shortCircuitCall?` accepts every non-empty argument list once it accepts one. -/
private theorem LExpr.shortCircuitCall?_cons {lfunc : LFunc Tbase}
    {args : List (LExpr Tbase.mono)} {a : LExpr Tbase.mono} {rest : List (LExpr Tbase.mono)}
    {ceval : Tbase.Metadata → List (LExpr Tbase.mono) → Option (LExpr Tbase.mono)}
    (h : LExpr.shortCircuitCall? lfunc args = some (a, rest, ceval))
    (b : LExpr Tbase.mono) (rest' : List (LExpr Tbase.mono)) :
    LExpr.shortCircuitCall? lfunc (b :: rest') = some (b, rest', ceval) := by
  have hsc : Strata.DL.Util.FuncAttr.hasShortCircuit lfunc.attr = true := by
    unfold LExpr.shortCircuitCall? at h; split at h
    · assumption
    · simp at h
  obtain ⟨_, hce⟩ := LExpr.shortCircuitCall?_some h
  unfold LExpr.shortCircuitCall?
  rw [ite_eq_left hsc, hce]

public section

---------------------------------------------------------------------
-- eval is eraseMetadata-invariant: if two expressions have the same eraseMetadata,
-- their eval results also have the same eraseMetadata.
-- This is a key structural property of eval: metadata is only used for provenance
-- tracking and does not affect the computation.

/-- The `shortCircuit` case of `eval_eraseMetadata_invariant`, given the invariant at
    the lower fuel. -/
private theorem evalShortCircuit_eraseMetadata
    {Tbase : LExprParams}
    [DecidableEq Tbase.Metadata] [DecidableEq Tbase.IDMeta]
    [Inhabited Tbase.IDMeta] [ToFormat Tbase.Metadata] [ToFormat Tbase.IDMeta]
    [Traceable LExpr.EvalProvenance Tbase.Metadata]
    (F : @Factory Tbase) (env : Env Tbase) (n' : Nat) (lfunc : LFunc Tbase)
    (h_wf : LFuncWF lfunc)
    (ceval : Tbase.Metadata → List (LExpr Tbase.mono) → Option (LExpr Tbase.mono))
    (hce : lfunc.concreteEval = some ceval)
    (e₁ e₂ op₁ op₂ a₁ a₂ : LExpr Tbase.mono) (rest₁ rest₂ : List (LExpr Tbase.mono))
    (h_op : op₁.eraseMetadata = op₂.eraseMetadata)
    (h_a : a₁.eraseMetadata = a₂.eraseMetadata)
    (h_rest : rest₁.map LExpr.eraseMetadata = rest₂.map LExpr.eraseMetadata)
    (ih : ∀ (e₁ e₂ : LExpr Tbase.mono), e₁.eraseMetadata = e₂.eraseMetadata →
      (LExpr.eval n' F env e₁).fst.eraseMetadata = (LExpr.eval n' F env e₂).fst.eraseMetadata) :
    (LExpr.evalShortCircuit n' F env e₁ op₁ a₁ rest₁ ceval).fst.eraseMetadata =
      (LExpr.evalShortCircuit n' F env e₂ op₂ a₂ rest₂ ceval).fst.eraseMetadata := by
  have hr1 := ih a₁ a₂ h_a
  have hval := isValue_eraseMetadata_eq F _ _ hr1
  have hargs : ((LExpr.eval n' F env a₁).fst :: rest₁).map LExpr.eraseMetadata =
      ((LExpr.eval n' F env a₂).fst :: rest₂).map LExpr.eraseMetadata := by
    simp only [List.map_cons, hr1, h_rest]
  have hrest_ev : ∀ (l₁ l₂ : List (LExpr Tbase.mono)),
      l₁.map LExpr.eraseMetadata = l₂.map LExpr.eraseMetadata →
      (l₁.map (fun x => (LExpr.eval n' F env x).fst)).map LExpr.eraseMetadata =
        (l₂.map (fun x => (LExpr.eval n' F env x).fst)).map LExpr.eraseMetadata := by
    intro l₁
    induction l₁ with
    | nil => intro l₂ h; cases l₂ <;> simp_all
    | cons x xs ihl =>
      intro l₂ h
      cases l₂ with
      | nil => simp at h
      | cons y ys =>
        simp only [List.map_cons, List.cons.injEq] at h ⊢
        exact ⟨ih _ _ h.1, ihl ys h.2⟩
  have hrebuild :
      (LExpr.mkApp e₁.metadata op₁
          ((LExpr.eval n' F env a₁).fst :: rest₁.map (fun x => (LExpr.eval n' F env x).fst))
        ).eraseMetadata =
      (LExpr.mkApp e₂.metadata op₂
          ((LExpr.eval n' F env a₂).fst :: rest₂.map (fun x => (LExpr.eval n' F env x).fst))
        ).eraseMetadata := by
    rw [LExpr.eraseMetadata_mkApp, LExpr.eraseMetadata_mkApp, h_op]
    simp only [List.map_cons, hr1, hrest_ev rest₁ rest₂ h_rest]
  unfold LExpr.evalShortCircuit
  simp only [LExpr.combineEvalResValueFlag_eq_pair]
  by_cases hv : LExpr.isValue F (LExpr.eval n' F env a₁).fst = true
  · rw [ite_eq_left hv, ite_eq_left (hval ▸ hv)]
    cases hc₁ : ceval e₁.metadata ((LExpr.eval n' F env a₁).fst :: rest₁) with
    | some r₁ =>
      obtain ⟨r₂, hc₂, hr⟩ :=
        h_wf.concreteEval_eraseMetadata ceval hce _ e₂.metadata _ _ r₁ hargs hc₁
      rw [hc₂]
      exact ih _ _ hr
    | none =>
      cases hc₂ : ceval e₂.metadata ((LExpr.eval n' F env a₂).fst :: rest₂) with
      | some r₂ =>
        obtain ⟨r₁, hc₁', _⟩ :=
          h_wf.concreteEval_eraseMetadata ceval hce _ e₁.metadata _ _ r₂ hargs.symm hc₂
        rw [hc₁] at hc₁'; simp at hc₁'
      | none => exact hrebuild
  · rw [ite_eq_right hv, ite_eq_right (by rwa [← hval])]
    exact hrebuild

theorem eval_eraseMetadata_invariant
    {Tbase : LExprParams}
    [DecidableEq Tbase.Metadata] [DecidableEq Tbase.IDMeta]
    [Inhabited Tbase.IDMeta] [ToFormat Tbase.Metadata] [ToFormat Tbase.IDMeta]
    [Traceable LExpr.EvalProvenance Tbase.Metadata]
    (F : @Factory Tbase) (env : Env Tbase) (e₁ e₂ : LExpr Tbase.mono) (n : Nat)
    (hWF : FactoryWF F)
    (h_eM : e₁.eraseMetadata = e₂.eraseMetadata) :
    (LExpr.eval n F env e₁).fst.eraseMetadata = (LExpr.eval n F env e₂).fst.eraseMetadata := by
  induction n generalizing e₁ e₂ with
  | zero =>
    simp only [LExpr.eval]
    rw [isValue_eraseMetadata_eq F e₁ e₂ h_eM]
    split
    · exact h_eM
    · exact LExpr.substFvarsFromEnv_eraseMetadata_congr env e₁ e₂ h_eM
  | succ n' ih =>
    simp only [LExpr.eval, LExpr.List_map_fst_map_eval,
      LExpr.List_all_snd_isValueTrue_map_eval, LExpr.combineEvalResValueFlag_eq_pair]
    rw [isValue_eraseMetadata_eq F e₁ e₂ h_eM]
    split
    · exact h_eM
    · split
      · -- factory case (inline/concreteEval/terminal)
        rename_i h_nval op_expr₁ args₁ lfunc h_call₁
        -- Get the corresponding callOfLFunc for e₂
        obtain ⟨op₂, args₂, h_call₂, h_args_eM_raw, h_op_eM⟩ :=
          callOfLFunc_some_of_eraseMetadata_eq F e₁ e₂ false h_eM op_expr₁ args₁ lfunc h_call₁
        rw [h_call₂]; simp only []
        -- Derive length equality
        have h_len : args₁.length = args₂.length := by
          have h_len_eq := congrArg List.length h_args_eM_raw; simp only [List.length_map] at h_len_eq ; exact h_len_eq
        -- Show evaluated args have the same eraseMetadata
        have h_eval_args_eM :
            (args₁.map (fun a => (LExpr.eval n' F env a).fst)).map LExpr.eraseMetadata =
            (args₂.map (fun a => (LExpr.eval n' F env a).fst)).map LExpr.eraseMetadata := by
          apply List.ext_getElem
          · simp [h_len]
          · intro i hi₁ hi₂
            simp only [List.getElem_map]
            have h_arg_eM : (args₁[i]'(by simp at hi₁; omega)).eraseMetadata =
                (args₂[i]'(by simp at hi₂; omega)).eraseMetadata := by
              have h_eM_i := congrArg (·[i]?) h_args_eM_raw
              simp only [List.length_map, show i < args₁.length from by simp at hi₁; omega, getElem?_pos, List.getElem_map,
    show i < args₂.length from by simp at hi₂; omega, Option.some.injEq] at h_eM_i
              exact h_eM_i
            exact ih _ _ h_arg_eM
        -- Show constrArgAt equality
        have h_constrArgAt_eq : ∀ idx : Option Nat,
            (match idx with
            | some i => ((args₁.map (fun a => (LExpr.eval n' F env a).fst))[i]? |>.map
                (LExpr.isConstrApp F)).getD false
            | none => false) =
            (match idx with
            | some i => ((args₂.map (fun a => (LExpr.eval n' F env a).fst))[i]? |>.map
                (LExpr.isConstrApp F)).getD false
            | none => false) := by
          intro idx
          cases idx with
          | none => rfl
          | some i =>
            simp only []
            by_cases h : i < args₁.length
            · have hi₁ : i < (args₁.map (fun a => (LExpr.eval n' F env a).fst)).length := by simp; omega
              have hi₂ : i < (args₂.map (fun a => (LExpr.eval n' F env a).fst)).length := by simp; omega
              rw [List.getElem?_eq_getElem hi₁, List.getElem?_eq_getElem hi₂]
              simp only [Option.map_some, Option.getD_some]
              simp only [List.getElem_map]
              have h_arg_eM : (args₁[i]'(by omega)).eraseMetadata = (args₂[i]'(by omega)).eraseMetadata := by
                have h_eM_i := congrArg (·[i]?) h_args_eM_raw
                simp only [List.length_map, h, getElem?_pos, List.getElem_map, show i < args₂.length from by omega,
    Option.some.injEq] at h_eM_i
                exact h_eM_i
              exact isConstrApp_eraseMetadata_eq F _ _ (ih _ _ h_arg_eM)
            · have hi₁ : (args₁.map (fun a => (LExpr.eval n' F env a).fst)).length ≤ i := by simp; omega
              have hi₂ : (args₂.map (fun a => (LExpr.eval n' F env a).fst)).length ≤ i := by simp; omega
              simp [List.getElem?_eq_none hi₁, List.getElem?_eq_none hi₂]
        -- Show valueArgAt equality
        have h_valueArgAt_eq : ∀ idx : Option Nat,
            (match idx with
            | some i => ((args₁.map (fun a => (LExpr.eval n' F env a).fst))[i]? |>.map
                (LExpr.isValue F)).getD false
            | none => false) =
            (match idx with
            | some i => ((args₂.map (fun a => (LExpr.eval n' F env a).fst))[i]? |>.map
                (LExpr.isValue F)).getD false
            | none => false) := by
          intro idx
          cases idx with
          | none => rfl
          | some i =>
            simp only []
            by_cases h : i < args₁.length
            · have hi₁ : i < (args₁.map (fun a => (LExpr.eval n' F env a).fst)).length := by simp; omega
              have hi₂ : i < (args₂.map (fun a => (LExpr.eval n' F env a).fst)).length := by simp; omega
              rw [List.getElem?_eq_getElem hi₁, List.getElem?_eq_getElem hi₂]
              simp only [Option.map_some, Option.getD_some]
              simp only [List.getElem_map]
              have h_arg_eM : (args₁[i]'(by omega)).eraseMetadata = (args₂[i]'(by omega)).eraseMetadata := by
                have h_eM_i := congrArg (·[i]?) h_args_eM_raw
                simp only [List.length_map, h, getElem?_pos, List.getElem_map, show i < args₂.length from by omega,
    Option.some.injEq] at h_eM_i
                exact h_eM_i
              exact isValue_eraseMetadata_eq F _ _ (ih _ _ h_arg_eM)
            · have hi₁ : (args₁.map (fun a => (LExpr.eval n' F env a).fst)).length ≤ i := by simp; omega
              have hi₂ : (args₂.map (fun a => (LExpr.eval n' F env a).fst)).length ≤ i := by simp; omega
              simp [List.getElem?_eq_none hi₁, List.getElem?_eq_none hi₂]
        -- Show all-p equality for every metadata-insensitive p
        have h_all_eq : ∀ p : LExpr Tbase.mono → Bool,
            (∀ a b : LExpr Tbase.mono, a.eraseMetadata = b.eraseMetadata → p a = p b) →
            (args₁.map (fun a => (LExpr.eval n' F env a).fst)).all p =
            (args₂.map (fun a => (LExpr.eval n' F env a).fst)).all p := by
          intro p hp
          have h_map_eq :
              (args₁.map (fun a => (LExpr.eval n' F env a).fst)).map p =
              (args₂.map (fun a => (LExpr.eval n' F env a).fst)).map p := by
            apply List.ext_getElem
            · simp [h_len]
            · intro i hi₁ hi₂
              simp only [List.getElem_map]
              have h_arg_eM : (args₁[i]'(by simp at hi₁; omega)).eraseMetadata =
                  (args₂[i]'(by simp at hi₂; omega)).eraseMetadata := by
                have h_eM_i := congrArg (·[i]?) h_args_eM_raw
                simp only [List.length_map, show i < args₁.length from by simp at hi₁; omega, getElem?_pos, List.getElem_map,
    show i < args₂.length from by simp at hi₂; omega, Option.some.injEq] at h_eM_i
                exact h_eM_i
              exact hp _ _ (ih _ _ h_arg_eM)
          rw [show (args₁.map (fun a => (LExpr.eval n' F env a).fst)).all p =
              ((args₁.map (fun a => (LExpr.eval n' F env a).fst)).map p).all id
              from by simp [List.all_map]]
          rw [show (args₂.map (fun a => (LExpr.eval n' F env a).fst)).all p =
              ((args₂.map (fun a => (LExpr.eval n' F env a).fst)).map p).all id
              from by simp [List.all_map]]
          rw [h_map_eq]
        have h_all_values := h_all_eq _ (isValue_eraseMetadata_eq F)
        -- Show inline condition equality
        have h_inline_cond_eq :
            (lfunc.body.isSome && (lfunc.attr.contains Strata.DL.Util.FuncAttr.inline ||
              (match Strata.DL.Util.FuncAttr.findInlineIfConstr lfunc.attr with
              | some i => ((args₁.map (fun a => (LExpr.eval n' F env a).fst))[i]? |>.map
                  (LExpr.isConstrApp F)).getD false
              | none => false) ||
              (Strata.DL.Util.FuncAttr.hasInlineIfAllValues lfunc.attr &&
                (args₁.map (fun a => (LExpr.eval n' F env a).fst)).all (LExpr.isInlineArg F)))) =
            (lfunc.body.isSome && (lfunc.attr.contains Strata.DL.Util.FuncAttr.inline ||
              (match Strata.DL.Util.FuncAttr.findInlineIfConstr lfunc.attr with
              | some i => ((args₂.map (fun a => (LExpr.eval n' F env a).fst))[i]? |>.map
                  (LExpr.isConstrApp F)).getD false
              | none => false) ||
              (Strata.DL.Util.FuncAttr.hasInlineIfAllValues lfunc.attr &&
                (args₂.map (fun a => (LExpr.eval n' F env a).fst)).all
                  (LExpr.isInlineArg F)))) := by
          congr 1; congr 1; congr 1
          · exact h_constrArgAt_eq _
          · exact congrArg _ (h_all_eq _ (isInlineArg_eraseMetadata_eq F))
        -- Show can_cond equality (for non-inline branch)
        have h_val_cond_eq :
            ((args₁.map (fun a => (LExpr.eval n' F env a).fst)).all (LExpr.isValue F) ||
              (match Strata.DL.Util.FuncAttr.findEvalIfConstr lfunc.attr with
              | some i => ((args₁.map (fun a => (LExpr.eval n' F env a).fst))[i]? |>.map
                  (LExpr.isConstrApp F)).getD false
              | none => false) ||
              (match Strata.DL.Util.FuncAttr.findEvalIfValue lfunc.attr with
              | some i => ((args₁.map (fun a => (LExpr.eval n' F env a).fst))[i]? |>.map
                  (LExpr.isValue F)).getD false
              | none => false)) =
            ((args₂.map (fun a => (LExpr.eval n' F env a).fst)).all (LExpr.isValue F) ||
              (match Strata.DL.Util.FuncAttr.findEvalIfConstr lfunc.attr with
              | some i => ((args₂.map (fun a => (LExpr.eval n' F env a).fst))[i]? |>.map
                  (LExpr.isConstrApp F)).getD false
              | none => false) ||
              (match Strata.DL.Util.FuncAttr.findEvalIfValue lfunc.attr with
              | some i => ((args₂.map (fun a => (LExpr.eval n' F env a).fst))[i]? |>.map
                  (LExpr.isValue F)).getD false
              | none => false)) := by
          rw [h_all_values, h_constrArgAt_eq, h_valueArgAt_eq]
        -- Split the inline conditions and type-substitution results on both
        -- sides. The corresponding equalities rule out mismatched branches.
        have h_computeTypeSubst_eq :=
          computeTypeSubst_eraseMetadata_congr lfunc op_expr₁ op₂ _ _ h_op_eM h_eval_args_eM
        rcases hsc₁ : LExpr.shortCircuitCall? lfunc args₁ with _ | ⟨a₁, rest₁, ceval⟩
        rotate_left
        · -- shortCircuit call
          obtain ⟨rfl, hce⟩ := LExpr.shortCircuitCall?_some hsc₁
          cases args₂ with
          | nil => simp at h_len
          | cons a₂ rest₂ =>
            rw [LExpr.shortCircuitCall?_cons hsc₁ a₂ rest₂]
            simp only [List.map_cons, List.cons.injEq] at h_args_eM_raw
            exact evalShortCircuit_eraseMetadata F env n' lfunc
              (hWF.lfuncs_wf lfunc (callOfLFunc_func_mem F _ _ _ lfunc false h_call₁)) ceval hce
              e₁ e₂ op_expr₁ op₂ a₁ a₂ rest₁ rest₂ h_op_eM h_args_eM_raw.1 h_args_eM_raw.2 ih
        rw [LExpr.shortCircuitCall?_none_of_length hsc₁ h_len]
        dsimp only
        split
        · -- LHS inline condition holds
          rename_i h_inline₁
          split
          · -- LHS: some tySubst (computeTypeSubst matched)
            rename_i tySubst h_tySubst₁
            split
            · -- RHS: inline condition true
              -- Now split RHS computeTypeSubst
              split
              · -- RHS: some tySubst₂
                rename_i tySubst₂ h_tySubst₂
                -- tySubst₁ = tySubst₂ via h_computeTypeSubst_eq
                have h_eq : tySubst = tySubst₂ := by
                  have h := h_computeTypeSubst_eq; rw [h_tySubst₁, h_tySubst₂] at h
                  exact Option.some.inj h
                subst h_eq
                apply ih
                exact substFvarsLifting_zip_eraseMetadata_congr _ _ _ _ h_eval_args_eM
              · -- RHS: none (impossible)
                rename_i h_none₂
                exfalso
                have h := h_computeTypeSubst_eq; rw [h_tySubst₁, h_none₂] at h
                exact absurd h (by simp)
            · -- RHS: inline condition false (contradicts h_inline₁ via h_inline_cond_eq)
              rename_i h_ninline₂
              exfalso; exact h_ninline₂ (h_inline_cond_eq.symm.trans h_inline₁)
          · -- LHS: none (computeTypeSubst returned none)
            rename_i h_none₁
            -- Goal: (e₁, .nonvalue).eM = (if h:... then ... else ...).eM
            split
            · -- RHS: inline condition true
              split
              · -- RHS: some tySubst₂ (impossible since LHS was none)
                rename_i tySubst₂ h_tySubst₂
                exfalso
                have h := h_computeTypeSubst_eq; rw [h_none₁, h_tySubst₂] at h
                exact absurd h (by simp)
              · -- RHS: none
                simp [LExpr.eraseMetadata_mkApp, h_op_eM, h_eval_args_eM]
            · -- RHS: inline condition false (contradicts h_inline₁)
              rename_i h_ninline₂
              exfalso; exact h_ninline₂ (h_inline_cond_eq.symm.trans h_inline₁)
        · -- LHS non-inline
          rename_i h_ninline₁
          -- Case on both attribute lookups to eliminate inner matches
          -- (findEvalIfConstr and findEvalIfValue) which cause `split`
          -- to misfire when nested inside the outer `if value`.  After
          -- this cases, the outer `if value` will be split cleanly.
          have h_lfunc_mem := callOfLFunc_func_mem F _ _ _ lfunc false h_call₁
          have h_wf_fn := hWF.lfuncs_wf lfunc h_lfunc_mem
          cases h_fEC : Strata.DL.Util.FuncAttr.findEvalIfConstr lfunc.attr <;>
          cases h_fEV : Strata.DL.Util.FuncAttr.findEvalIfValue lfunc.attr <;> (
            simp only [h_fEC, h_fEV] at h_val_cond_eq h_constrArgAt_eq h_valueArgAt_eq ⊢
            -- Now `split` on the outer LHS `if value` works.
            split
            · rename_i h_val₁
              cases h_ce : lfunc.concreteEval with
              | none =>
                simp only []
                split
                next h_inline₂ =>
                  exfalso; exact h_ninline₁ (h_inline_cond_eq.trans h_inline₂)
                next h_ninline₂ =>
                  simp [apply_ite Prod.fst, LExpr.eraseMetadata_mkApp,
                    h_op_eM, h_eval_args_eM]
              | some ceval =>
                match h_cv₁ : ceval (@LExpr.mkApp Tbase.mono e₁.metadata op_expr₁
                    (args₁.map (fun a => (LExpr.eval n' F env a).fst))).metadata
                    (args₁.map (fun a => (LExpr.eval n' F env a).fst)) with
                | some e'₁ =>
                  simp only [h_cv₁]
                  split
                  next h_inline₂ =>
                    exfalso; exact h_ninline₁ (h_inline_cond_eq.trans h_inline₂)
                  next h_ninline₂ =>
                    -- LHS value check is true (h_val₁); derive RHS value check is true
                    have h_val₂ := h_val_cond_eq ▸ h_val₁
                    rw [ite_eq_left h_val₂]
                    match h_cv₂ : ceval (@LExpr.mkApp Tbase.mono e₂.metadata op₂
                        (args₂.map (fun a => (LExpr.eval n' F env a).fst))).metadata
                        (args₂.map (fun a => (LExpr.eval n' F env a).fst)) with
                    | some e'₂ =>
                      obtain ⟨e'₂', h_cv₂', h_res_eM⟩ :=
                        h_wf_fn.concreteEval_eraseMetadata ceval h_ce _ _ _ _ e'₁ h_eval_args_eM h_cv₁
                      rw [h_cv₂'] at h_cv₂; cases h_cv₂
                      exact ih _ _ h_res_eM
                    | none =>
                      obtain ⟨e'₂, h_cv₂', _⟩ :=
                        h_wf_fn.concreteEval_eraseMetadata ceval h_ce _ _ _ _ e'₁ h_eval_args_eM h_cv₁
                      exact absurd (h_cv₂.symm.trans h_cv₂') (by simp)
                | none =>
                  simp only [h_cv₁]
                  split
                  next h_inline₂ =>
                    exfalso; exact h_ninline₁ (h_inline_cond_eq.trans h_inline₂)
                  next h_ninline₂ =>
                    have h_val₂ := h_val_cond_eq ▸ h_val₁
                    rw [ite_eq_left h_val₂]
                    match h_cv₂ : ceval (@LExpr.mkApp Tbase.mono e₂.metadata op₂
                        (args₂.map (fun a => (LExpr.eval n' F env a).fst))).metadata
                        (args₂.map (fun a => (LExpr.eval n' F env a).fst)) with
                    | some e'₂ =>
                      obtain ⟨e'₁, h_cv₁', _⟩ :=
                        h_wf_fn.concreteEval_eraseMetadata ceval h_ce _ _ _ _ e'₂ h_eval_args_eM.symm h_cv₂
                      exact absurd (h_cv₁.symm.trans h_cv₁') (by simp)
                    | none =>
                      simp [LExpr.eraseMetadata_mkApp, h_op_eM, h_eval_args_eM]
            · rename_i h_nval₁
              split
              next h_inline₂ =>
                exfalso; exact h_ninline₁ (h_inline_cond_eq.trans h_inline₂)
              next h_ninline₂ =>
                split
                next h_val₂_prop =>
                  exact absurd (h_val_cond_eq ▸ h_val₂_prop) h_nval₁
                next h_nval₂_prop =>
                  simp [LExpr.eraseMetadata_mkApp, h_op_eM, h_eval_args_eM]
          )
      · rename_i h_none₁
        have h_none₂ := callOfLFunc_none_of_eraseMetadata_eq F _ _ false h_eM h_none₁
        rw [h_none₂]
        exact evalCore_eraseMetadata_congr n' F env e₁ e₂ h_eM ih

end -- public section

/-! ## Part VI: values of type `bool`

With operator annotations checked against the factory, and no constructor
producing a Boolean, the values of type `bool` are exactly the two
Boolean constants (`LExpr.isValue_bool_eq_boolConst`). -/

public section

section value_bool

/-- The head of an application spine inherits `opsConsistent` from the spine. -/
private theorem opsConsistent_getLFuncCall_go {T : LExprParams} {F : Factory T}
    (e : LExpr T.mono) (acc : List (LExpr T.mono)) (h : e.opsConsistent F = true) :
    (getLFuncCall.go e acc).1.opsConsistent F = true := by
  fun_induction getLFuncCall.go e acc <;> simp_all only [LExpr.opsConsistent, Bool.and_eq_true]

/-- **Values of type `bool` are Boolean constants.** If no constructor of `F`
produces a Boolean (`Factory.ConstrsNotBool`), a value whose type,
checked against `F` by `LExpr.typeCheckWith`, is `bool` is `.boolConst m b`. -/
theorem LExpr.isValue_bool_eq_boolConst {T : LExprParams} {F : Factory T} (hF : F.ConstrsNotBool)
    {e : LExpr T.mono} (hc : LExpr.isValue F e = true)
    (ht : LExpr.typeCheckWith F [] e = some .bool) : ∃ m b, e = .boolConst m b := by
  unfold LExpr.typeCheckWith at ht
  split at ht
  rotate_left
  · cases ht
  rename_i hops
  unfold LExpr.isValue at hc
  split at hc
  · cases ‹LConst› <;> simp_all [LExpr.typeCheck, LConst.ty, LExpr.boolConst, LMonoTy.bool,
      LMonoTy.int, LMonoTy.real, LMonoTy.string]
  · cases ‹Option LMonoTy› <;>
      simp_all [LExpr.typeCheck, LMonoTy.arrow, LMonoTy.bool, Option.bind_eq_some_iff]
  · cases hc
  split at hc
  rotate_left
  · cases hc
  rename_i op args fn hcall
  have hle : args.length ≤ fn.inputs.length := by
    simp only [Factory.callOfLFunc] at hcall
    repeat' split at hcall
    all_goals simp_all [Nat.ble_eq]
  obtain ⟨m, name, ty, rfl, hget⟩ := Factory.callOfLFunc_getElem? hcall
  have hgl := callOfLFunc_getLFuncCall hcall
  have hspec := getLFuncCall_spec (LExpr.typeCheck_to_HasTypeA ht)
  rw [hgl] at hspec
  obtain ⟨tys, hrel, hop⟩ := hspec
  have hlen := hrel.length_eq.symm
  replace hop := LExpr.HasTypeA_to_typeCheck hop
  simp only [getLFuncCall] at hgl
  have hops' := opsConsistent_getLFuncCall_go e [] hops
  rw [hgl] at hops'
  cases ty
  · cases hop
  simp only [LExpr.typeCheck, Option.some.injEq] at hop
  subst hop
  simp only [LExpr.opsConsistent, hget] at hops'
  obtain ⟨S, hS⟩ := Option.isSome_iff_exists.mp hops'
  have hops' := (LMonoTy.matchSubst_sound hS).symm
  rw [subst_mkArrow'] at hops'
  have hd := LMonoTy.mkArrow'_eq_drop hops' (by
    rw [hlen, List.length_map]
    exact Nat.le_trans hle (Nat.le_of_eq (List.length_map _).symm))
  simp only [Bool.and_eq_true, Bool.or_eq_true, Nat.blt_eq] at hc
  revert hd
  cases hdrop : List.drop tys.length (List.map (LMonoTy.subst _) (List.map Prod.snd fn.inputs))
  · have hn : ¬ args.length < fn.inputs.length := by
      simp only [List.drop_eq_nil_iff, List.length_map] at hdrop
      exact Nat.not_lt_of_le (hlen ▸ (List.length_map _) ▸ hdrop)
    exact fun hd => absurd hd.symm
      (hF fn (Factory.getElem?_is_some_implies_mem hget) (hc.1.resolve_right hn) _)
  · simp [LMonoTy.bool, LMonoTy.arrow]

end value_bool

end -- public section

end Lambda
