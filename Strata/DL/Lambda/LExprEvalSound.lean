/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import Strata.DL.Lambda.OperationalSemanticsProps
public import Strata.DL.Lambda.LExprEvalProps
import all Strata.DL.Lambda.OperationalSemanticsProps
import all Strata.DL.Lambda.LExprEval
import all Strata.DL.Lambda.Factory
import all Strata.DL.Lambda.FactoryProps

/-!
# Soundness of the Lambda evaluator

`eval_StepStar` connects the executable, fuel-bounded evaluator to the
reflexive-transitive closure of the Lambda small-step semantics.
-/

namespace Lambda

open Std (ToFormat Format format)

public section

variable {Tbase : LExprParams} [DecidableEq Tbase.Metadata]
    [DecidableEq Tbase.Identifier] [DecidableEq Tbase.IDMeta] [Inhabited Tbase.IDMeta]

---------------------------------------------------------------------
-- Helper lemma: for the terminal factory case.

omit [DecidableEq Tbase.Metadata] [DecidableEq Tbase.Identifier] in
private theorem eval_StepStar_factory_terminal
    {Tbase : LExprParams}
    [DecidableEq Tbase.Metadata] [DecidableEq Tbase.IDMeta]
    [Inhabited Tbase.IDMeta] [ToFormat Tbase.Metadata] [ToFormat Tbase.IDMeta]
    [Traceable LExpr.EvalProvenance Tbase.Metadata]
    (F : @Factory Tbase) (env : Env Tbase) (e : LExpr Tbase.mono) (n : Nat)
    (op_expr : LExpr Tbase.mono)
    (args : List (LExpr Tbase.mono))
    (lfunc : LFunc Tbase)
    (h_call : F.callOfLFunc e = some (op_expr, args, lfunc))
    (ih : ∀ (e : LExpr Tbase.mono),
      ∃ (e' : LExpr Tbase.mono),
        StepStar F env e e' ∧
        e'.eraseMetadata = (LExpr.eval n F env e).fst.eraseMetadata) :
    ∃ (e' : LExpr Tbase.mono),
      StepStar F env e e' ∧
      e'.eraseMetadata =
        (LExpr.mkApp e.metadata op_expr (args.map (fun a => (LExpr.eval n F env a).fst))).eraseMetadata := by
  obtain ⟨h_get, m_op, name_op, ty_op, h_op_eq⟩ := callOfLFunc_getLFuncCall_op h_call
  let stepped_args := args.map (fun a => (ih a).choose)
  have h_stepped_len : args.length = stepped_args.length := by simp [stepped_args]
  have h_per_step : ∀ i (hi : i < args.length),
      StepStar F env
        (args.get ⟨i, hi⟩) (stepped_args.get ⟨i, h_stepped_len ▸ hi⟩) := by
    intro i hi
    have h_get_eq : stepped_args.get ⟨i, h_stepped_len ▸ hi⟩ = (ih (args.get ⟨i, hi⟩)).choose := by
      simp [stepped_args]
    rw [h_get_eq]; exact (ih (args.get ⟨i, hi⟩)).choose_spec.1
  have h_per_eM : ∀ i (hi : i < args.length),
      (stepped_args.get ⟨i, h_stepped_len ▸ hi⟩).eraseMetadata =
        (LExpr.eval n F env (args.get ⟨i, hi⟩)).fst.eraseMetadata := by
    intro i hi
    have h_get_eq : stepped_args.get ⟨i, h_stepped_len ▸ hi⟩ = (ih (args.get ⟨i, hi⟩)).choose := by
      simp [stepped_args]
    rw [h_get_eq]; exact (ih (args.get ⟨i, hi⟩)).choose_spec.2
  obtain ⟨e', h_step_e, h_e'_eq⟩ :=
    StepStar_getLFuncCall_args e op_expr args stepped_args h_get h_stepped_len h_per_step
  refine ⟨e', h_step_e, ?_⟩
  have hA : e'.eraseMetadata = (LExpr.mkApp e.metadata op_expr stepped_args).eraseMetadata := by
    rw [h_e'_eq, LExpr.eraseMetadata_mkApp]
  have hB : (LExpr.mkApp e.metadata op_expr stepped_args).eraseMetadata =
      (LExpr.mkApp e.metadata op_expr (args.map (fun a => (LExpr.eval n F env a).fst))).eraseMetadata := by
    rw [LExpr.eraseMetadata_mkApp, LExpr.eraseMetadata_mkApp]
    congr 1
    have h_len_eq : stepped_args.length = (args.map (fun a => (LExpr.eval n F env a).fst)).length := by simp [stepped_args]
    apply List.ext_getElem (by simp [h_len_eq])
    intro i hi1 hi2
    simp only [List.getElem_map]
    have hi_args : i < args.length := by simp [stepped_args] at hi1; exact hi1
    exact h_per_eM i hi_args
  rw [hA, hB]

/-- A call whose arguments step to `stepped_args`, which agree up to metadata with
    `vals`, steps to an expression that agrees up to metadata with the evaluation of
    `concreteEval md vals`: the call fires `eval_fn`, and `concreteEval_eraseMetadata`
    relates its result to the evaluator's. -/
private theorem eval_StepStar_factory_ceval_of_stepped
    {Tbase : LExprParams}
    [DecidableEq Tbase.Metadata] [DecidableEq Tbase.IDMeta]
    [Inhabited Tbase.IDMeta] [ToFormat Tbase.Metadata] [ToFormat Tbase.IDMeta]
    [Traceable LExpr.EvalProvenance Tbase.Metadata]
    (F : @Factory Tbase) (env : Env Tbase) (e : LExpr Tbase.mono) (n : Nat)
    (hWF : FactoryWF F)
    (op_expr : LExpr Tbase.mono)
    (args : List (LExpr Tbase.mono))
    (lfunc : LFunc Tbase)
    (h_call : F.callOfLFunc e = some (op_expr, args, lfunc))
    (ceval : Tbase.Metadata → List (LExpr Tbase.mono) → Option (LExpr Tbase.mono))
    (h_ceval : lfunc.concreteEval = some ceval)
    (md : Tbase.Metadata) (vals stepped_args : List (LExpr Tbase.mono))
    (e'_ceval : LExpr Tbase.mono)
    (h_ceval_succ : ceval md vals = some e'_ceval)
    (h_stepped_len : args.length = stepped_args.length)
    (h_per_step : ∀ i (hi : i < args.length),
      StepStar F env (args.get ⟨i, hi⟩) (stepped_args.get ⟨i, h_stepped_len ▸ hi⟩))
    (h_args_eM : stepped_args.map LExpr.eraseMetadata = vals.map LExpr.eraseMetadata)
    (ih : ∀ (e : LExpr Tbase.mono),
      ∃ (e' : LExpr Tbase.mono),
        StepStar F env e e' ∧
        e'.eraseMetadata = (LExpr.eval n F env e).fst.eraseMetadata) :
    ∃ (e' : LExpr Tbase.mono),
      StepStar F env e e' ∧
      e'.eraseMetadata = (LExpr.eval n F env e'_ceval).fst.eraseMetadata := by
  obtain ⟨h_get, m_op, name_op, ty_op, h_op_eq⟩ := callOfLFunc_getLFuncCall_op h_call
  obtain ⟨e_stepped, h_step_e, h_eM_stepped⟩ :=
    StepStar_getLFuncCall_args e op_expr args stepped_args h_get h_stepped_len h_per_step
  have h_vals_len : vals.length = args.length := by
    have := congrArg List.length h_args_eM; simp at this; omega
  have h_eM_eq : e_stepped.eraseMetadata =
      (LExpr.mkApp e.metadata op_expr vals).eraseMetadata := by
    rw [h_eM_stepped, LExpr.eraseMetadata_mkApp, h_args_eM]
  have h_call_mkApp : F.callOfLFunc
      (LExpr.mkApp e.metadata op_expr args) = some (op_expr, args, lfunc) := by
    subst h_op_eq
    simp only [Factory.callOfLFunc, getLFuncCall_mkApp_op] at h_call ⊢
    simp only [h_get] at h_call
    exact h_call
  have h_call_eval : F.callOfLFunc (LExpr.mkApp e.metadata op_expr vals) =
      some (op_expr, vals, lfunc) :=
    callOfLFunc_mkApp_op F e.metadata op_expr args vals lfunc ⟨m_op, name_op, ty_op, h_op_eq⟩
      h_call_mkApp h_vals_len
  obtain ⟨op_s, args_s, h_call_s, h_args_s_eM, _⟩ :=
    callOfLFunc_some_of_eraseMetadata_eq F (LExpr.mkApp e.metadata op_expr vals)
      e_stepped false h_eM_eq.symm op_expr vals lfunc h_call_eval
  have h_lfunc_mem := callOfLFunc_func_mem F _ _ _ lfunc false h_call
  have h_wf_fn := hWF.lfuncs_wf lfunc h_lfunc_mem
  obtain ⟨res_s, h_ceval_s, h_res_eM⟩ :=
    h_wf_fn.concreteEval_eraseMetadata ceval h_ceval md e.metadata vals args_s e'_ceval
      h_args_s_eM h_ceval_succ
  have h_step_eval : Step F env e_stepped res_s :=
    Step.eval_fn e_stepped op_s res_s args_s lfunc ceval h_call_s h_ceval h_ceval_s.symm
  obtain ⟨e_final, h_step_final, h_eM_final⟩ := ih res_s
  refine ⟨e_final, ReflTrans_Transitive _ _ _ _ h_step_e (ReflTrans.step _ _ _ h_step_eval h_step_final), ?_⟩
  rw [h_eM_final]
  exact eval_eraseMetadata_invariant F env res_s e'_ceval n hWF h_res_eM.symm

/-- The concreteEval factory case of `eval_StepStar`: when `concreteEval` succeeds on
    the evaluated arguments, the call steps to an expression that agrees up to
    metadata with the evaluation of its result. -/
private theorem eval_StepStar_factory_ceval
    {Tbase : LExprParams}
    [DecidableEq Tbase.Metadata] [DecidableEq Tbase.IDMeta]
    [Inhabited Tbase.IDMeta] [ToFormat Tbase.Metadata] [ToFormat Tbase.IDMeta]
    [Traceable LExpr.EvalProvenance Tbase.Metadata]
    (F : @Factory Tbase) (env : Env Tbase) (e : LExpr Tbase.mono) (n : Nat)
    (hWF : FactoryWF F)
    (op_expr : LExpr Tbase.mono)
    (args : List (LExpr Tbase.mono))
    (lfunc : LFunc Tbase)
    (h_call : F.callOfLFunc e = some (op_expr, args, lfunc))
    (ceval : Tbase.Metadata → List (LExpr Tbase.mono) → Option (LExpr Tbase.mono))
    (h_ceval : lfunc.concreteEval = some ceval)
    (e'_ceval : LExpr Tbase.mono)
    (h_ceval_succ : ceval (LExpr.mkApp e.metadata op_expr
        (args.map (fun a => (LExpr.eval n F env a).fst))).metadata (args.map (fun a => (LExpr.eval n F env a).fst)) = some e'_ceval)
    (ih : ∀ (e : LExpr Tbase.mono),
      ∃ (e' : LExpr Tbase.mono),
        StepStar F env e e' ∧
        e'.eraseMetadata = (LExpr.eval n F env e).fst.eraseMetadata) :
    ∃ (e' : LExpr Tbase.mono),
      StepStar F env e e' ∧
      e'.eraseMetadata = (LExpr.eval n F env e'_ceval).fst.eraseMetadata := by
  let stepped_args := args.map (fun a => (ih a).choose)
  have h_stepped_len : args.length = stepped_args.length := by simp [stepped_args]
  have h_per_step : ∀ i (hi : i < args.length),
      StepStar F env
        (args.get ⟨i, hi⟩) (stepped_args.get ⟨i, h_stepped_len ▸ hi⟩) := by
    intro i hi
    have h_get_eq : stepped_args.get ⟨i, h_stepped_len ▸ hi⟩ = (ih (args.get ⟨i, hi⟩)).choose := by
      simp [stepped_args]
    rw [h_get_eq]; exact (ih (args.get ⟨i, hi⟩)).choose_spec.1
  have h_args_eM : stepped_args.map LExpr.eraseMetadata =
      (args.map (fun a => (LExpr.eval n F env a).fst)).map LExpr.eraseMetadata := by
    simp only [stepped_args, List.map_map]
    apply List.map_congr_left
    intro a _
    exact (ih a).choose_spec.2
  exact eval_StepStar_factory_ceval_of_stepped F env e n hWF op_expr args lfunc h_call ceval
    h_ceval _ _ stepped_args e'_ceval h_ceval_succ h_stepped_len h_per_step h_args_eM ih

/-- The `shortCircuit` case of `eval_StepStar`: a call of a `shortCircuit` function
    steps to an expression that agrees up to metadata with `evalShortCircuit`'s
    result. Only the first argument steps before `concreteEval` fires; the others
    are handed to it as they are. -/
private theorem eval_StepStar_shortCircuit
    {Tbase : LExprParams}
    [DecidableEq Tbase.Metadata] [DecidableEq Tbase.IDMeta]
    [Inhabited Tbase.IDMeta] [ToFormat Tbase.Metadata] [ToFormat Tbase.IDMeta]
    [Traceable LExpr.EvalProvenance Tbase.Metadata]
    (F : @Factory Tbase) (env : Env Tbase) (e : LExpr Tbase.mono) (n : Nat)
    (hWF : FactoryWF F)
    (op_expr : LExpr Tbase.mono)
    (args : List (LExpr Tbase.mono))
    (lfunc : LFunc Tbase)
    (h_call : F.callOfLFunc e = some (op_expr, args, lfunc))
    (a : LExpr Tbase.mono) (rest : List (LExpr Tbase.mono))
    (ceval : Tbase.Metadata → List (LExpr Tbase.mono) → Option (LExpr Tbase.mono))
    (h_sc : LExpr.shortCircuitCall? lfunc args = some (a, rest, ceval))
    (ih : ∀ (e : LExpr Tbase.mono),
      ∃ (e' : LExpr Tbase.mono),
        StepStar F env e e' ∧
        e'.eraseMetadata = (LExpr.eval n F env e).fst.eraseMetadata) :
    ∃ (e' : LExpr Tbase.mono),
      StepStar F env e e' ∧
      e'.eraseMetadata = (LExpr.evalShortCircuit n F env e op_expr a rest ceval).fst.eraseMetadata := by
  obtain ⟨h_args, h_ceval⟩ := LExpr.shortCircuitCall?_some h_sc
  subst h_args
  unfold LExpr.evalShortCircuit
  simp only [LExpr.combineEvalResValueFlag_eq_pair]
  split
  · rename_i e'_ceval h_if
    have h_ceval_succ : ceval e.metadata ((LExpr.eval n F env a).fst :: rest) = some e'_ceval := by
      split at h_if
      · exact h_if
      · simp at h_if
    obtain ⟨a_s, h_step_a, h_eM_a⟩ := ih a
    have h_len : (a :: rest).length = (a_s :: rest).length := by simp
    have h_per_step : ∀ i (hi : i < (a :: rest).length),
        StepStar F env ((a :: rest).get ⟨i, hi⟩) ((a_s :: rest).get ⟨i, h_len ▸ hi⟩) := by
      intro i hi
      cases i with
      | zero => exact h_step_a
      | succ j => exact ReflTrans.refl _
    exact eval_StepStar_factory_ceval_of_stepped F env e n hWF op_expr (a :: rest) lfunc h_call
      ceval h_ceval e.metadata _ (a_s :: rest) e'_ceval h_ceval_succ h_len h_per_step
      (by simp [h_eM_a]) ih
  · have h := eval_StepStar_factory_terminal F env e n op_expr (a :: rest) lfunc h_call ih
    simpa only [List.map_cons] using h

---------------------------------------------------------------------
-- Main theorem

theorem eval_StepStar
    {Tbase : LExprParams}
    [DecidableEq Tbase.Metadata] [DecidableEq Tbase.IDMeta]
    [Inhabited Tbase.IDMeta] [ToFormat Tbase.Metadata] [ToFormat Tbase.IDMeta]
    [Traceable LExpr.EvalProvenance Tbase.Metadata]
    (F : @Factory Tbase) (env : Env Tbase) (e : LExpr Tbase.mono) (e2 : LExpr Tbase.mono) (fuel : Nat)
    (hWF : FactoryWF F)
    (hEval : e2 = (LExpr.eval fuel F env e).fst) :
    ∃ (e' : LExpr Tbase.mono),
      StepStar F env e e' ∧
      e'.eraseMetadata = e2.eraseMetadata := by
  subst hEval
  unfold StepStar
  induction fuel generalizing e with
  | zero =>
    exact ⟨e, ReflTrans.refl e, by simp [LExpr.eval]⟩
  | succ fuel ih =>
    simp only [LExpr.eval, LExpr.List_map_fst_map_eval,
      LExpr.List_all_snd_isValueTrue_map_eval, LExpr.combineEvalResValueFlag_eq_pair]
    split
    · -- Canonical: eval returns e
      rename_i h_value
      have h_eval_n : (LExpr.eval fuel F env e).fst = e := by
        cases fuel with
        | zero => simp [LExpr.eval]
        | succ fuel' => simp [LExpr.eval, h_value]
      obtain ⟨e', hstep, hve⟩ := ih e
      rw [h_eval_n] at hve
      exact ⟨e', hstep, hve⟩
    · rename_i h_not_value
      split
      · -- Factory case
        rename_i op_expr args lfunc h_call
        split
        · -- shortCircuit call
          rename_i a rest ceval h_sc
          exact eval_StepStar_shortCircuit F env e fuel hWF op_expr args lfunc h_call
            a rest ceval h_sc ih
        split
        · -- Inline: step args, fire expand_fn, use eval_eraseMetadata_invariant to bridge
          rename_i h_inline
          have h_body_some : lfunc.body.isSome = true := by
            have h_and := Bool.and_eq_true_iff.mp h_inline; exact h_and.1
          obtain ⟨body, h_body_eq⟩ := Option.isSome_iff_exists.mp h_body_some
          -- Split on computeTypeSubst in the eval result
          split
          · -- computeTypeSubst = some tySubst
            rename_i tySubst h_tySubst
            obtain ⟨h_get, m_op, name_op, ty_op, h_op_eq⟩ := callOfLFunc_getLFuncCall_op h_call
            let stepped_args := args.map (fun a => (ih a).choose)
            have h_stepped_len : args.length = stepped_args.length := by simp [stepped_args]
            have h_per_step : ∀ i (hi : i < args.length),
                StepStar F env
                  (args.get ⟨i, hi⟩) (stepped_args.get ⟨i, h_stepped_len ▸ hi⟩) := by
              intro i hi; simp [stepped_args]; exact (ih (args.get ⟨i, hi⟩)).choose_spec.1
            obtain ⟨e_stepped, h_step_e, h_estepped_eM⟩ :=
              StepStar_getLFuncCall_args e op_expr args stepped_args h_get h_stepped_len h_per_step
            have h_ref_call : F.callOfLFunc (LExpr.mkApp e.metadata op_expr stepped_args) =
                some (op_expr, stepped_args, lfunc) := by
              apply callOfLFunc_mkApp_op F e.metadata op_expr args stepped_args lfunc
                ⟨m_op, name_op, ty_op, h_op_eq⟩ _ h_stepped_len.symm
              subst h_op_eq
              simp only [Factory.callOfLFunc, getLFuncCall_mkApp_op] at h_call ⊢
              simp only [h_get] at h_call
              exact h_call
            have h_ref_eM : e_stepped.eraseMetadata =
                (LExpr.mkApp e.metadata op_expr stepped_args).eraseMetadata := by
              rw [h_estepped_eM, LExpr.eraseMetadata_mkApp]
            obtain ⟨op', stepped_args', h_call_stepped, h_args_eM, h_op'_eM⟩ :=
              callOfLFunc_some_of_eraseMetadata_eq F
                (LExpr.mkApp e.metadata op_expr stepped_args) e_stepped false
                h_ref_eM.symm op_expr stepped_args lfunc h_ref_call
            -- Derive computeTypeSubst for stepped_args' via eraseMetadata-congr
            have h_per_eM : ∀ i (hi : i < args.length),
                (stepped_args.get ⟨i, h_stepped_len ▸ hi⟩).eraseMetadata =
                  ((LExpr.eval fuel F env (args.get ⟨i, hi⟩)).fst).eraseMetadata := by
              intro i hi; simp [stepped_args]; exact (ih (args.get ⟨i, hi⟩)).choose_spec.2
            have h_vals_eM : stepped_args'.map LExpr.eraseMetadata =
                (args.map (fun a => (LExpr.eval fuel F env a).fst)).map LExpr.eraseMetadata := by
              rw [← h_args_eM]
              apply List.ext_getElem (by simp [stepped_args])
              intro i hi1 hi2
              simp only [List.getElem_map]
              have hi_args : i < args.length := by simp [stepped_args] at hi1; exact hi1
              exact h_per_eM i hi_args
            have h_tySubst_stepped :
                LFunc.computeTypeSubst lfunc op' stepped_args' = some tySubst := by
              rw [← h_tySubst]
              exact computeTypeSubst_eraseMetadata_congr lfunc op' op_expr _ _
                h_op'_eM.symm h_vals_eM
            have h_expand : Step F (env) e_stepped
                (LExpr.substFvarsLifting (body.applyTypeSubst tySubst)
                  (lfunc.inputs.keys.zip stepped_args')) :=
              Step.expand_fn e_stepped op' body _ stepped_args' lfunc tySubst
                h_call_stepped h_body_eq h_tySubst_stepped rfl
            obtain ⟨e'_s, h_step_s, h_ve_s⟩ :=
              ih (LExpr.substFvarsLifting (body.applyTypeSubst tySubst)
                (lfunc.inputs.keys.zip stepped_args'))
            refine ⟨e'_s, ReflTrans_Transitive _ _ _ _ h_step_e
              (ReflTrans.step _ _ _ h_expand h_step_s), ?_⟩
            have h_subst_eM :
                (LExpr.substFvarsLifting (body.applyTypeSubst tySubst)
                  (lfunc.inputs.keys.zip stepped_args')).eraseMetadata =
                (LExpr.substFvarsLifting (body.applyTypeSubst tySubst)
                  (lfunc.inputs.keys.zip (args.map (fun a => (LExpr.eval fuel F env a).fst)))).eraseMetadata :=
              substFvarsLifting_zip_eraseMetadata_congr _ _ _ _ h_vals_eM
            have h_body_get : lfunc.body.get (by simp [h_body_eq]) = body := by
              simp [h_body_eq]
            show _ = ((LExpr.eval fuel F env _).fst).eraseMetadata
            rw [h_body_get, show (fun a => (LExpr.eval fuel F env a).fst) = (fun a => (LExpr.eval fuel F env a).fst) from rfl]
            exact h_ve_s.trans (eval_eraseMetadata_invariant F env _ _ fuel hWF h_subst_eM)
          · -- computeTypeSubst = none: eval returns e unchanged
            exact ⟨e, ReflTrans.refl e, rfl⟩
        · -- Non-inline
          rename_i h_not_inline
          -- Case on both attribute lookups to eliminate inner matches
          cases h_fEC : Strata.DL.Util.FuncAttr.findEvalIfConstr lfunc.attr <;>
          cases h_fEV : Strata.DL.Util.FuncAttr.findEvalIfValue lfunc.attr <;> (
            simp only []
            split
            · rename_i h_value_args
              split
              · -- No ceval: terminal
                rename_i h_no_ceval
                exact eval_StepStar_factory_terminal F env e fuel op_expr args lfunc h_call ih
              · -- ceval exists
                rename_i ceval h_ceval
                split
                · -- ceval succeeds: eval = eval fuel σ e'_ceval
                  rename_i e'_ceval h_ceval_succ
                  exact eval_StepStar_factory_ceval F env e fuel hWF
                    op_expr args lfunc h_call ceval h_ceval e'_ceval h_ceval_succ ih
                · -- ceval fails: terminal
                  rename_i h_ceval_fail
                  exact eval_StepStar_factory_terminal F env e fuel op_expr args lfunc h_call ih
            · -- Symbolic args: terminal
              rename_i h_symbolic
              exact eval_StepStar_factory_terminal F env e fuel op_expr args lfunc h_call ih
          )
      · -- evalCore case: case analysis on e
        rename_i h_no_call
        match e, h_not_value, h_no_call with
        | .const m c, h_nc, _ =>
          exact absurd (by simp [LExpr.isValue] :
            LExpr.isValue F (.const m c) = true) h_nc
        | .op m fn ty, _, _ =>
          refine ⟨_, ReflTrans.refl _, ?_⟩
          simp only [LExpr.evalCore]
        | .bvar m i, _, _ =>
          refine ⟨_, ReflTrans.refl _, ?_⟩
          simp only [LExpr.evalCore]
        | .fvar m x ty, _, _ =>
          simp only [LExpr.evalCore]
          cases h_env : env x with
          | none =>
            exact ⟨_, ReflTrans.refl _, rfl⟩
          | some v =>
            have h_step : Step F env (.fvar m x ty) v :=
              Step.expand_fvar x v h_env
            exact ⟨v, ReflTrans.step _ v _ h_step (ReflTrans.refl _), rfl⟩
        | .abs m name ty body, _, _ =>
          simp only [LExpr.evalCore]
          exact ⟨LExpr.substFvarsFromEnv env (.abs m name ty body),
            StepStar_to_substFvarsFromEnv_abs F env m name ty body, rfl⟩
        | .quant m qk name ty tr body, _, _ =>
          simp only [LExpr.evalCore]
          exact ⟨LExpr.substFvarsFromEnv env (.quant m qk name ty tr body),
            StepStar_to_substFvarsFromEnv_quant F env m qk name ty tr body, rfl⟩
        | .app m e1 e2, _, _ =>
          obtain ⟨s1, hs1, hv1⟩ := ih e1
          obtain ⟨s2, hs2, hv2⟩ := ih e2
          have h_step_app : StepStar F env
              (.app m e1 e2) (.app m s1 s2) :=
            ReflTrans_Transitive _ _ _ _ (StepStar_app_fn _ _ e1 s1 e2 m hs1)
              (StepStar_app_arg _ _ s1 e2 s2 m hs2)
          simp only [LExpr.evalCore, LExpr.evalApp]
          split
          · -- Beta case: eval fuel σ e1 = .abs mAbs name ty body_e1'
            -- EMEquiv s1 (.abs ...) → s1 IS an abs → fire beta
            rename_i mAbs name ty body_e1' h_eval_abs
            -- Extract abs structure from hv1 before the split complicates things
            -- hv1 : s1.eraseMetadata = (eval fuel σ e1).eraseMetadata, and h_eval_abs : eval fuel σ e1 = .abs ...
            -- So hv1 : s1.eraseMetadata = (.abs mAbs name ty body_e1').eraseMetadata
            -- s1 must be .abs m2 name ty body_s1
            have h_s1_abs : ∃ m2 body_s1,
                s1 = .abs m2 name ty body_s1 ∧ body_s1.eraseMetadata = body_e1'.eraseMetadata := by
              rw [h_eval_abs] at hv1
              simp [LExpr.eraseMetadata, LExpr.replaceMetadata] at hv1
              cases s1 <;> simp [LExpr.replaceMetadata] at hv1 <;> try contradiction
              rename_i m2 name2 ty2 body2
              have ⟨hn, hty, hb⟩ := hv1; subst hn hty
              exact ⟨_, _, rfl, hb⟩
            obtain ⟨m2, body_s1, h_s1_eq, h_eM_body⟩ := h_s1_abs
            subst h_s1_eq
            -- Fire beta
            have h_beta : Step F (env)
                (.app m (.abs m2 name ty body_s1) s2)
                (LExpr.subst (fun _ => s2) body_s1) :=
              Step.beta body_s1 s2 _ rfl
            have h_steps_to_beta := ReflTrans_Transitive _ _ _ _ h_step_app
              (ReflTrans.step _ _ _ h_beta (ReflTrans.refl _))
            -- The evalApp with .abs: splits on eqModuloMeta
            split
            · exact ⟨.app m e1 e2, ReflTrans.refl _, rfl⟩
            · rename_i h_not_eqmod e'_eval h_not_eqmod_bool
              obtain ⟨e'', hstep'', hve''⟩ := ih (LExpr.subst (fun _ => s2) body_s1)
              refine ⟨e'', ReflTrans_Transitive _ _ _ _ h_steps_to_beta hstep'', ?_⟩
              have h_subst_eM : (LExpr.subst (fun _ => s2) body_s1).eraseMetadata =
                  (LExpr.subst (fun m₂ =>
                    LExpr.replaceMetadata1 (LExpr.mergeMetadataForSubst mAbs ((LExpr.eval fuel F env e2).fst).metadata m₂)
                      ((LExpr.eval fuel F env e2).fst)) body_e1').eraseMetadata := by
                simp only [LExpr.subst]
                exact substK_eraseMetadata_congr₂ body_s1 body_e1' 0 _ _
                  h_eM_body
                  (fun m₁ m₂ => by
                    have h_rp1 : ∀ (m' : Tbase.Metadata) (e' : LExpr Tbase.mono),
                        (LExpr.replaceMetadata1 m' e').eraseMetadata = e'.eraseMetadata := by
                      intro m' e'; cases e' <;> simp [LExpr.replaceMetadata1, LExpr.eraseMetadata, LExpr.replaceMetadata]
                    rw [h_rp1]
                    exact hv2)
              have h_eval_eM := eval_eraseMetadata_invariant F env
                (LExpr.subst (fun _ => s2) body_s1)
                (LExpr.subst (fun m₂ =>
                    LExpr.replaceMetadata1 (LExpr.mergeMetadataForSubst mAbs ((LExpr.eval fuel F env e2).fst).metadata m₂)
                      ((LExpr.eval fuel F env e2).fst)) body_e1')
                fuel hWF h_subst_eM
              exact hve''.trans h_eval_eM
          · rename_i h_not_abs
            split
            · exact ⟨.app m e1 e2, ReflTrans.refl _, rfl⟩
            · rename_i h_not_eqmod e'_app
              obtain ⟨e'', hstep'', hve''⟩ := ih (.app m s1 s2)
              refine ⟨e'', ReflTrans_Transitive _ _ _ _ h_step_app hstep'', ?_⟩
              have h_app_eM : (LExpr.app m s1 s2).eraseMetadata =
                  (LExpr.app (LExpr.app m e1 e2 : LExpr Tbase.mono).metadata ((LExpr.eval fuel F env e1).fst) ((LExpr.eval fuel F env e2).fst)).eraseMetadata := by
                simp [LExpr.eraseMetadata]
                exact eraseMetadata_app_congr hv1 hv2
              have h_eval_eM := eval_eraseMetadata_invariant F env
                (LExpr.app m s1 s2)
                (LExpr.app (LExpr.app m e1 e2 : LExpr Tbase.mono).metadata ((LExpr.eval fuel F env e1).fst) ((LExpr.eval fuel F env e2).fst))
                fuel hWF h_app_eM
              exact hve''.trans h_eval_eM
        | .eq m e1 e2, _, _ =>
          obtain ⟨s1, hs1, hv1⟩ := ih e1
          obtain ⟨s2, hs2, hv2⟩ := ih e2
          simp only [LExpr.evalCore, LExpr.evalEq]
          split
          · -- eql resolves to some b
            rename_i b h_eql_some
            have h_eql_s : LExpr.eql F s1 s2 = some b := by
              rw [eql_eraseMetadata_eq F s1 s2
                ((LExpr.eval fuel F env e1).fst) ((LExpr.eval fuel F env e2).fst)
                hv1 hv2]
              exact h_eql_some
            have h_step_eq := ReflTrans_Transitive _ _ _ _
              (StepStar_eq_lhs_pres _ _ e1 s1 e2 m hs1)
              (StepStar_eq_rhs_pres _ _ s1 e2 s2 m hs2)
            cases b with
            | true =>
              exact ⟨.const m (.boolConst true),
                ReflTrans_Transitive _ _ _ _ h_step_eq
                  (ReflTrans.step _ _ _ (Step.eq_reduce_true s1 s2 h_eql_s) (ReflTrans.refl _)),
                rfl⟩
            | false =>
              exact ⟨.const m (.boolConst false),
                ReflTrans_Transitive _ _ _ _ h_step_eq
                  (ReflTrans.step _ _ _ (Step.eq_reduce_false s1 s2 h_eql_s) (ReflTrans.refl _)),
                rfl⟩
          · -- eql returns none → .eq m (eval e1) (eval e2)
            rename_i h_eql_none
            exact ⟨.eq m s1 s2,
              ReflTrans_Transitive _ _ _ _ (StepStar_eq_lhs_pres _ _ e1 s1 e2 m hs1)
                (StepStar_eq_rhs_pres _ _ s1 e2 s2 m hs2),
              by simp [LExpr.eraseMetadata, LExpr.replaceMetadata]; exact ⟨hv1, hv2⟩⟩
        | .ite m c t f, _, _ =>
          obtain ⟨sc, hsc, hvc⟩ := ih c
          simp only [LExpr.evalCore, LExpr.evalIte]
          split
          · -- condition resolves to true → eval t
            rename_i mc_true h_eval_c_true
            rw [h_eval_c_true] at hvc
            obtain ⟨mc', h_step_to_true⟩ :=
              step_to_const_via_IH F env c sc mc_true (LConst.boolConst true) hsc hvc
            obtain ⟨st, hst_step, hvt⟩ := ih t
            refine ⟨st, ?_, hvt⟩
            exact ReflTrans_Transitive _ _ _ _
              (StepStar_ite_cond_pres _ _ c (.const mc' (.boolConst true)) t f m h_step_to_true)
              (ReflTrans.step _ t _ (Step.ite_reduce_then (m := m) (mc := mc') t f) hst_step)
          · -- condition resolves to false → eval f
            rename_i mc_false h_eval_c_false
            rw [h_eval_c_false] at hvc
            obtain ⟨mc', h_step_to_false⟩ :=
              step_to_const_via_IH F env c sc mc_false (LConst.boolConst false) hsc hvc
            obtain ⟨sf, hsf_step, hvf⟩ := ih f
            refine ⟨sf, ?_, hvf⟩
            exact ReflTrans_Transitive _ _ _ _
              (StepStar_ite_cond_pres _ _ c (.const mc' (.boolConst false)) t f m h_step_to_false)
              (ReflTrans.step _ f _ (Step.ite_reduce_else (m := m) (mc := mc') t f) hsf_step)
          · -- condition unresolved → .ite m (eval c) (eval t) (eval f)
            rename_i h_not_true h_not_false
            obtain ⟨st, hst, hvt⟩ := ih t
            obtain ⟨sf, hsf, hvf⟩ := ih f
            refine ⟨.ite m sc st sf,
              ReflTrans_Transitive _ _ _ _ (StepStar_ite_cond_pres _ _ c sc t f m hsc)
                (ReflTrans_Transitive _ _ _ _ (StepStar_ite_then_pres _ _ sc t st f m hst)
                  (StepStar_ite_else_pres _ _ sc st f sf m hsf)), ?_⟩
            show (LExpr.ite m sc st sf).eraseMetadata = (LExpr.ite m ((LExpr.eval fuel F env c).fst) ((LExpr.eval fuel F env t).fst) ((LExpr.eval fuel F env f).fst)).eraseMetadata
            simp only [LExpr.eraseMetadata, LExpr.replaceMetadata]
            exact congr (congr (congr rfl hvc) hvt) hvf

end -- public section
end Lambda
