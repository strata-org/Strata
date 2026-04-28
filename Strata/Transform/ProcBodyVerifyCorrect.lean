/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.ProcBodyVerify
public import Strata.Transform.CoreSpecification
public import Strata.Languages.Core.WF
public import Strata.Languages.Core.ProcedureWF
import Strata.DL.Util.ListMap
import Strata.DL.Util.List

public section

/-! # Procedure Body Verification Correctness Proof -/

namespace ProcBodyVerifyCorrect

open Core Core.ProcBodyVerify Imperative Lambda Transform Core.WF

/-! ## coreIsAtAssert helpers -/

private theorem coreIsAtAssert_not_terminal (ρ : Env Expression) (a : AssertId Expression) :
    ¬ coreIsAtAssert (.terminal ρ) a := by simp [coreIsAtAssert]

private theorem coreIsAtAssert_not_exiting (lbl : Option String) (ρ : Env Expression) (a : AssertId Expression) :
    ¬ coreIsAtAssert (.exiting lbl ρ) a := by simp [coreIsAtAssert]

/-! ## Input Environment Reconstruction, from the prefix statements of ProcBodyVerify

"Prefix statements" are the init + assume statements that ProcBodyVerify places
before the procedure body (param inits, old-var inits, precondition assumes).
"Input environment reconstruction" (prefixInitEnv) reverses the inits:
given the environment after the prefix has executed, it computes
what it was before by setting each init'd variable back to none.
The `procToVerifyStmt_structure` theorem uses the `prefixInitEnv` reconstruction
function to show that there exists an initial state that doesn't make the
prefix statements (`prefixStmt`) stuck.
-/

/-- Identify the variable initialized by a statement, if any. -/
private def stmtInitVar : Statement → Option Expression.Ident
  | .cmd (.cmd (.init x _ _ _)) => some x
  | _ => none

/-- Given prefix statements and a target environment `ρ`, compute the initial
    environment by undoing all `init` commands (setting their variables to `none`).
    Processes right-to-left: first undoes the tail, then the head. -/
private def prefixInitEnv : List Statement → Imperative.Env Expression → Imperative.Env Expression
  | [], ρ => ρ
  | s :: rest, ρ =>
      let ρ' := prefixInitEnv rest ρ
      match stmtInitVar s with
      | some x => { ρ' with store := fun y => if x = y then none else ρ'.store y }
      | none => ρ'

@[simp] private theorem prefixInitEnv_eval (stmts : List Statement) (ρ : Imperative.Env Expression) :
    (prefixInitEnv stmts ρ).eval = ρ.eval := by
  induction stmts with
  | nil => rfl
  | cons s rest ih => simp [prefixInitEnv]; cases stmtInitVar s <;> simp [ih]

@[simp] private theorem prefixInitEnv_hasFailure (stmts : List Statement) (ρ : Imperative.Env Expression) :
    (prefixInitEnv stmts ρ).hasFailure = ρ.hasFailure := by
  induction stmts with
  | nil => rfl
  | cons s rest ih => simp [prefixInitEnv]; cases stmtInitVar s <;> simp [ih]

private theorem prefixInitEnv_store_init (s : Statement) (rest : List Statement)
    (ρ : Imperative.Env Expression) (x : Expression.Ident)
    (hx : stmtInitVar s = some x) :
    (prefixInitEnv (s :: rest) ρ).store x = none := by
  simp [prefixInitEnv, hx]

private theorem prefixInitEnv_store_other (s : Statement) (rest : List Statement)
    (ρ : Imperative.Env Expression) (y : Expression.Ident) (x : Expression.Ident)
    (hx : stmtInitVar s = some x) (hne : x ≠ y) :
    (prefixInitEnv (s :: rest) ρ).store y = (prefixInitEnv rest ρ).store y := by
  simp [prefixInitEnv, hx, hne]

private theorem prefixInitEnv_store_noninit (s : Statement) (rest : List Statement)
    (ρ : Imperative.Env Expression) (hs : stmtInitVar s = none) :
    (prefixInitEnv (s :: rest) ρ).store = (prefixInitEnv rest ρ).store := by
  simp [prefixInitEnv, hs]

/-- Recursive predicate: each statement in the list can step correctly
    from its `prefixInitEnv` state. -/
private def PrefixStepsOK
    (π : String → Option Procedure) (φ : CoreEval → PureFunc Expression → CoreEval)
    : List Statement → Imperative.Env Expression → Prop
  | [], _ => True
  | s :: rest, ρ =>
    PrefixStepsOK π φ rest ρ ∧
    ∃ c, s = Stmt.cmd c ∧
      ∃ σ', EvalCommand π φ ρ.eval (prefixInitEnv (s :: rest) ρ).store c σ' false ∧
        σ' = (prefixInitEnv rest ρ).store

private theorem Env_eq {ρ₁ ρ₂ : Imperative.Env Expression}
    (h_s : ρ₁.store = ρ₂.store) (h_e : ρ₁.eval = ρ₂.eval) (h_f : ρ₁.hasFailure = ρ₂.hasFailure) :
    ρ₁ = ρ₂ := by
  cases ρ₁; cases ρ₂; simp_all

/-- If `PrefixStepsOK` holds and `hasFailure` is false,
    stepping from `prefixInitEnv stmts ρ` reaches `.terminal ρ`. -/
private theorem prefixInitEnv_steps
    (stmts : List Statement) (ρ : Imperative.Env Expression)
    (π : String → Option Procedure) (φ : CoreEval → PureFunc Expression → CoreEval)
    (h_hf : ρ.hasFailure = false)
    (h_ok : PrefixStepsOK π φ stmts ρ) :
    Imperative.StepStmtStar Expression (EvalCommand π φ) (EvalPureFunc φ)
      (.stmts stmts (prefixInitEnv stmts ρ)) (.terminal ρ) := by
  induction stmts with
  | nil =>
    simp [prefixInitEnv]
    exact .step _ _ _ .step_stmts_nil (.refl _)
  | cons s rest ih =>
    obtain ⟨h_ok_rest, c, rfl, σ', h_eval, h_σ'⟩ := h_ok
    have ih' := ih h_ok_rest
    have h_eval' : EvalCommand π φ (prefixInitEnv (Stmt.cmd c :: rest) ρ).eval
        (prefixInitEnv (Stmt.cmd c :: rest) ρ).store c σ' false := by
      rwa [prefixInitEnv_eval]
    have h_env_eq : { (prefixInitEnv (Stmt.cmd c :: rest) ρ) with
        store := σ',
        hasFailure := (prefixInitEnv (Stmt.cmd c :: rest) ρ).hasFailure || false } =
        prefixInitEnv rest ρ :=
      Env_eq h_σ'
        (by simp [prefixInitEnv_eval])
        (by simp [prefixInitEnv_hasFailure, h_hf])
    have h_one_step : StepStmtStar Expression (EvalCommand π φ) (EvalPureFunc φ)
        (.stmt (Stmt.cmd c) (prefixInitEnv (Stmt.cmd c :: rest) ρ))
        (.terminal (prefixInitEnv rest ρ)) :=
      .step _ _ _ (.step_cmd h_eval') (h_env_eq ▸ .refl _)
    exact ReflTrans_Transitive _ _ _ _
      (stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ)
        (Stmt.cmd c) rest (prefixInitEnv (Stmt.cmd c :: rest) ρ)
        (prefixInitEnv rest ρ) h_one_step)
      ih'

private theorem prefixInitEnv_append (a b : List Statement) (ρ : Imperative.Env Expression) :
    prefixInitEnv (a ++ b) ρ = prefixInitEnv a (prefixInitEnv b ρ) := by
  induction a with
  | nil => simp [prefixInitEnv]
  | cons s rest ih =>
    simp only [List.cons_append, prefixInitEnv]
    rw [ih]

private theorem PrefixStepsOK_append (π : String → Option Procedure)
    (φ : CoreEval → PureFunc Expression → CoreEval)
    (a b : List Statement) (ρ : Imperative.Env Expression) :
    PrefixStepsOK π φ (a ++ b) ρ ↔
      PrefixStepsOK π φ b ρ ∧ PrefixStepsOK π φ a (prefixInitEnv b ρ) := by
  induction a with
  | nil => simp [PrefixStepsOK]
  | cons s rest ih =>
    simp only [List.cons_append, PrefixStepsOK]
    rw [ih]
    constructor
    · rintro ⟨⟨hb, hrest⟩, c, hs, σ', heval, hσ'⟩
      refine ⟨hb, ⟨hrest, c, hs, σ', ?_, ?_⟩⟩
      · have h1 : (prefixInitEnv b ρ).eval = ρ.eval := prefixInitEnv_eval b ρ
        have h2 : prefixInitEnv (s :: rest) (prefixInitEnv b ρ) = prefixInitEnv (s :: (rest ++ b)) ρ := by
          show prefixInitEnv (s :: rest) (prefixInitEnv b ρ) = prefixInitEnv ((s :: rest) ++ b) ρ
          rw [← prefixInitEnv_append]
        rw [h1, h2]; exact heval
      · have h2 : prefixInitEnv rest (prefixInitEnv b ρ) = prefixInitEnv (rest ++ b) ρ := by
          rw [← prefixInitEnv_append]
        rw [h2]; exact hσ'
    · rintro ⟨hb, hrest, c, hs, σ', heval, hσ'⟩
      refine ⟨⟨hb, hrest⟩, c, hs, σ', ?_, ?_⟩
      · have h1 : (prefixInitEnv b ρ).eval = ρ.eval := prefixInitEnv_eval b ρ
        have h2 : prefixInitEnv (s :: rest) (prefixInitEnv b ρ) = prefixInitEnv (s :: (rest ++ b)) ρ := by
          show prefixInitEnv (s :: rest) (prefixInitEnv b ρ) = prefixInitEnv ((s :: rest) ++ b) ρ
          rw [← prefixInitEnv_append]
        rw [h1, h2] at heval; exact heval
      · have h2 : prefixInitEnv rest (prefixInitEnv b ρ) = prefixInitEnv (rest ++ b) ρ := by
          rw [← prefixInitEnv_append]
        rw [h2] at hσ'; exact hσ'

private theorem prefixInitEnv_store_not_init (stmts : List Statement)
    (ρ : Imperative.Env Expression) (x : Expression.Ident)
    (h : ∀ s ∈ stmts, stmtInitVar s ≠ some x) :
    (prefixInitEnv stmts ρ).store x = ρ.store x := by
  induction stmts with
  | nil => rfl
  | cons s rest ih =>
    have hs := h s List.mem_cons_self
    have hrest := ih (fun s' hs' => h s' (List.mem_cons_of_mem s hs'))
    simp [prefixInitEnv]
    cases hv : stmtInitVar s with
    | none => exact hrest
    | some y =>
      simp only
      have hne : y ≠ x := fun heq => hs (heq ▸ hv)
      simp [hne, hrest]

private theorem prefixInitEnv_noninit_list (stmts : List Statement)
    (ρ : Imperative.Env Expression)
    (h : ∀ s ∈ stmts, stmtInitVar s = none) :
    prefixInitEnv stmts ρ = ρ := by
  induction stmts with
  | nil => rfl
  | cons s rest ih =>
    have hs := h s List.mem_cons_self
    have hrest := ih (fun s' hs' => h s' (List.mem_cons_of_mem s hs'))
    simp [prefixInitEnv, hs, hrest]

/-- PrefixStepsOK for a list of assume statements, given preconditions hold. -/
private theorem PrefixStepsOK_assumes
    (π : String → Option Procedure) (φ : CoreEval → PureFunc Expression → CoreEval)
    (preconds : ListMap CoreLabel Procedure.Check)
    (ρ : Imperative.Env Expression)
    (h_preconds : ∀ (label : CoreLabel) (check : Procedure.Check),
      (label, check) ∈ preconds.toList →
      ρ.eval ρ.store check.expr = some HasBool.tt)
    (h_wfBool : WellFormedSemanticEvalBool ρ.eval) :
    PrefixStepsOK π φ (requiresToAssumes preconds) ρ := by
  suffices h : ∀ (items : List (CoreLabel × Procedure.Check)),
      (∀ (label : CoreLabel) (check : Procedure.Check),
        (label, check) ∈ items → ρ.eval ρ.store check.expr = some HasBool.tt) →
      PrefixStepsOK π φ (items.map fun (label, check) => Statement.assume label check.expr check.md) ρ from
    h _ h_preconds
  intro items h_items
  induction items with
  | nil => exact trivial
  | cons p rest ih =>
    obtain ⟨label, check⟩ := p
    simp only [List.map_cons]
    have h_noninit_all : ∀ s ∈ (rest.map fun x => Statement.assume x.1 x.2.expr x.2.md),
        stmtInitVar s = none := by
      intro s hs; simp only [List.mem_map] at hs
      obtain ⟨⟨l, c⟩, _, rfl⟩ := hs; rfl
    have h_env_eq : prefixInitEnv (rest.map fun x => Statement.assume x.1 x.2.expr x.2.md) ρ = ρ :=
      prefixInitEnv_noninit_list _ _ h_noninit_all
    unfold PrefixStepsOK
    have h_rest_ok : PrefixStepsOK π φ
        (rest.map fun x => Statement.assume x.1 x.2.expr x.2.md) ρ :=
      ih (fun l c hmem => h_items l c (List.mem_cons_of_mem (label, check) hmem))
    have h_store_eq : (prefixInitEnv (Statement.assume label check.expr check.md ::
        rest.map fun x => Statement.assume x.1 x.2.expr x.2.md) ρ).store = ρ.store := by
      rw [prefixInitEnv_store_noninit _ _ _ rfl, h_env_eq]
    exact ⟨h_rest_ok, _, rfl, _,
      by rw [h_store_eq]
         exact EvalCommand.cmd_sem (EvalCmd.eval_assume
           (h_items label check List.mem_cons_self) h_wfBool),
      by show _ = (prefixInitEnv _ ρ).store; rw [h_env_eq]⟩

/-- For a nondet init statement, if `x` is none in the pre-state and some in the target,
    and all other variables match, then PrefixStepsOK holds for the singleton. -/
private theorem PrefixStepsOK_nondet_init_cons
    (π : String → Option Procedure) (φ : CoreEval → PureFunc Expression → CoreEval)
    (x : Expression.Ident) (ty : Expression.Ty) (rest : List Statement)
    (ρ : Imperative.Env Expression)
    (h_wfVar : WellFormedSemanticEvalVar ρ.eval)
    (h_rest : PrefixStepsOK π φ rest ρ)
    (h_some : ((prefixInitEnv rest ρ).store x).isSome) :
    PrefixStepsOK π φ (Statement.init x ty .nondet #[] :: rest) ρ := by
  constructor
  · exact h_rest
  · refine ⟨_, rfl, (prefixInitEnv rest ρ).store, ?_, rfl⟩
    have h_none : (prefixInitEnv (Statement.init x ty .nondet #[] :: rest) ρ).store x = none :=
      prefixInitEnv_store_init _ _ _ _ rfl
    have h_some' := h_some
    rw [Option.isSome_iff_exists] at h_some'
    obtain ⟨v, hv⟩ := h_some'
    exact EvalCommand.cmd_sem (EvalCmd.eval_init_unconstrained
      (InitState.init h_none hv (fun y hne => by
        exact (prefixInitEnv_store_other _ _ _ y x rfl hne).symm))
      h_wfVar)

/-- PrefixStepsOK for a list of nondet init statements from a map. -/
private theorem PrefixStepsOK_nondet_init_map
    (π : String → Option Procedure) (φ : CoreEval → PureFunc Expression → CoreEval)
    (entries : List (Expression.Ident × Lambda.LMonoTy))
    (ρ : Imperative.Env Expression)
    (h_wfVar : WellFormedSemanticEvalVar ρ.eval)
    (h_defined : ∀ id ∈ entries.map Prod.fst,
      (ρ.store id).isSome)
    (h_nodup : (entries.map Prod.fst).Nodup)
    : PrefixStepsOK π φ
        (entries.map fun (id, ty) => Statement.init id (Lambda.LTy.forAll [] ty) .nondet #[]) ρ := by
  induction entries with
  | nil => exact trivial
  | cons e rest ih =>
    obtain ⟨id, ty⟩ := e
    simp only [List.map] at h_defined h_nodup ⊢
    rw [List.nodup_cons] at h_nodup
    apply PrefixStepsOK_nondet_init_cons π φ id (Lambda.LTy.forAll [] ty)
    · exact h_wfVar
    · exact ih (fun i hi => h_defined i (List.mem_cons_of_mem _ hi)) h_nodup.2
    · -- Need: ((prefixInitEnv (rest.map ...) ρ).store id).isSome
      rw [prefixInitEnv_store_not_init]
      · exact h_defined id (List.mem_cons_self)
      · intro s hs
        simp only [List.mem_map] at hs
        obtain ⟨⟨id', ty'⟩, hmem, rfl⟩ := hs
        simp [stmtInitVar]
        intro heq
        exact h_nodup.1 (heq ▸ List.mem_map_of_mem (f := Prod.fst) hmem)

/-- For a deterministic init `init oldG ty (.det (fvar id))`, if `id` has a value
    in the pre-state, `oldG` is none, and `oldG ≠ id`, then it steps correctly.
    The `fvar` uses `SourceRange.none` to match the synthesized init from `ProcBodyVerify`. -/
private theorem PrefixStepsOK_det_init_cons
    (π : String → Option Procedure) (φ : CoreEval → PureFunc Expression → CoreEval)
    (id : Expression.Ident) (oldG : Expression.Ident) (ty : Expression.Ty) (rest : List Statement)
    (ρ : Imperative.Env Expression)
    (h_wfVar : WellFormedSemanticEvalVar ρ.eval)
    (h_rest : PrefixStepsOK π φ rest ρ)
    (_h_id_some : ((prefixInitEnv rest ρ).store id).isSome)
    (h_old_some : ((prefixInitEnv rest ρ).store oldG).isSome)
    (h_id_eq_old : (prefixInitEnv rest ρ).store id = (prefixInitEnv rest ρ).store oldG)
    (h_ne : oldG ≠ id) :
    PrefixStepsOK π φ
      (Statement.init oldG ty (.det (LExpr.fvar Strata.SourceRange.none id none)) #[] :: rest) ρ := by
  constructor
  · exact h_rest
  · refine ⟨_, rfl, (prefixInitEnv rest ρ).store, ?_, rfl⟩
    have h_none : (prefixInitEnv (Statement.init oldG ty (.det (LExpr.fvar Strata.SourceRange.none id none)) #[] :: rest) ρ).store oldG = none :=
      prefixInitEnv_store_init _ _ _ _ rfl
    have h_id_val : (prefixInitEnv (Statement.init oldG ty (.det (LExpr.fvar Strata.SourceRange.none id none)) #[] :: rest) ρ).store id =
        (prefixInitEnv rest ρ).store id := by
      rw [prefixInitEnv_store_other _ _ _ id oldG rfl h_ne]
    rw [Option.isSome_iff_exists] at h_old_some
    obtain ⟨v, hv⟩ := h_old_some
    have h_getFvar : HasFvar.getFvar (LExpr.fvar Strata.SourceRange.none id none : Expression.Expr) = some id := by
      simp [HasFvar.getFvar]
    have h_eval : ρ.eval (prefixInitEnv (Statement.init oldG ty (.det (LExpr.fvar Strata.SourceRange.none id none)) #[] :: rest) ρ).store
        (LExpr.fvar Strata.SourceRange.none id none) = some v := by
      rw [h_wfVar _ _ _ h_getFvar, h_id_val, h_id_eq_old, hv]
    exact EvalCommand.cmd_sem (EvalCmd.eval_init h_eval
      (InitState.init h_none hv (fun y hne => by
        exact (prefixInitEnv_store_other _ _ _ y oldG rfl hne).symm))
      h_wfVar)

/-- PrefixStepsOK for a list of det init statements `init (mkOld id.name) ty (.det (fvar id))`. -/
private theorem PrefixStepsOK_det_init_map
    (π : String → Option Procedure) (φ : CoreEval → PureFunc Expression → CoreEval)
    (entries : List (Expression.Ident × Lambda.LMonoTy))
    (ρ : Imperative.Env Expression)
    (h_wfVar : WellFormedSemanticEvalVar ρ.eval)
    (h_defined : ∀ id ∈ entries.map Prod.fst,
      (ρ.store id).isSome)
    (h_old_defined : ∀ id ∈ entries.map Prod.fst,
      (ρ.store (CoreIdent.mkOld id.name)).isSome)
    (h_old_match : ∀ id ∈ entries.map Prod.fst,
      ρ.store id = ρ.store (CoreIdent.mkOld id.name))
    (h_nodup : (entries.map Prod.fst).Nodup)
    (h_not_old : ∀ id ∈ entries.map Prod.fst, ∀ x, id ≠ CoreIdent.mkOld x)
    (h_nodup_old : ((entries.map Prod.fst).map (fun id => CoreIdent.mkOld id.name)).Nodup)
    : PrefixStepsOK π φ
        (entries.map fun (id, ty) =>
          Statement.init (CoreIdent.mkOld id.name) (Lambda.LTy.forAll [] ty)
            (.det (LExpr.fvar Strata.SourceRange.none id none)) #[]) ρ := by
  induction entries with
  | nil => exact trivial
  | cons e rest ih =>
    obtain ⟨id, ty⟩ := e
    simp only [List.map] at h_defined h_old_defined h_old_match h_nodup h_not_old h_nodup_old ⊢
    rw [List.nodup_cons] at h_nodup h_nodup_old
    apply PrefixStepsOK_det_init_cons π φ id (CoreIdent.mkOld id.name)
      (Lambda.LTy.forAll [] ty) _ ρ h_wfVar
    · exact ih (fun i hi => h_defined i (List.mem_cons_of_mem _ hi))
              (fun i hi => h_old_defined i (List.mem_cons_of_mem _ hi))
              (fun i hi => h_old_match i (List.mem_cons_of_mem _ hi))
              h_nodup.2
              (fun i hi => h_not_old i (List.mem_cons_of_mem _ hi))
              h_nodup_old.2
    · -- id not init'd by rest's old inits: id is not old-prefixed
      rw [prefixInitEnv_store_not_init]
      · exact h_defined id List.mem_cons_self
      · intro s hs
        simp only [List.mem_map] at hs
        obtain ⟨⟨id', ty'⟩, hmem, rfl⟩ := hs
        simp [stmtInitVar]
        exact (h_not_old id List.mem_cons_self id'.name).symm
    · -- mkOld id.name not init'd by rest's old inits: nodup of mkOld ids
      rw [prefixInitEnv_store_not_init]
      · exact h_old_defined id List.mem_cons_self
      · intro s hs
        simp only [List.mem_map] at hs
        obtain ⟨⟨id', ty'⟩, hmem, rfl⟩ := hs
        simp [stmtInitVar]
        intro heq
        apply h_nodup_old.1
        rw [show CoreIdent.mkOld id.name = CoreIdent.mkOld id'.name from heq.symm]
        exact List.mem_map.mpr ⟨id', List.mem_map.mpr ⟨(id', ty'), hmem, rfl⟩, rfl⟩
    · -- id and mkOld id.name agree, even after undoing rest's old inits
      rw [prefixInitEnv_store_not_init, prefixInitEnv_store_not_init]
      · exact h_old_match id List.mem_cons_self
      · -- mkOld id.name not init'd by rest
        intro s hs
        simp only [List.mem_map] at hs
        obtain ⟨⟨id', ty'⟩, hmem, rfl⟩ := hs
        simp [stmtInitVar]
        intro heq
        apply h_nodup_old.1
        rw [show CoreIdent.mkOld id.name = CoreIdent.mkOld id'.name from heq.symm]
        exact List.mem_map.mpr ⟨id', List.mem_map.mpr ⟨(id', ty'), hmem, rfl⟩, rfl⟩
      · -- id not init'd by rest
        intro s hs
        simp only [List.mem_map] at hs
        obtain ⟨⟨id', ty'⟩, hmem, rfl⟩ := hs
        simp [stmtInitVar]
        exact (h_not_old id List.mem_cons_self id'.name).symm
    · exact (CoreIdent.ne_mkOld id).symm

private theorem mkOld_name_injective {a b : Expression.Ident}
    (h : CoreIdent.mkOld a.name = CoreIdent.mkOld b.name) : a = b := by
  have h1 := congrArg Lambda.Identifier.name h
  simp [CoreIdent.mkOld, CoreIdent.oldStr] at h1
  have h2 := congrArg String.toList h1
  simp at h2
  have h3 := String.ext h2
  cases a; cases b; simp_all

/-- If the original ids are Nodup, so are their mkOld images (since mkOld is injective). -/
private theorem nodup_mkOld_map (ids : List Expression.Ident)
    (h_nodup : ids.Nodup) :
    (ids.map (fun id => CoreIdent.mkOld id.name)).Nodup := by
  induction ids with
  | nil => exact List.nodup_nil
  | cons id rest ih =>
    rw [List.nodup_cons] at h_nodup
    simp only [List.map_cons]
    rw [List.nodup_cons]
    constructor
    · intro hmem
      simp only [List.mem_map] at hmem
      obtain ⟨id', hid'_mem, hid'_eq⟩ := hmem
      have : id = id' := mkOld_name_injective hid'_eq.symm
      exact h_nodup.1 (this ▸ hid'_mem)
    · exact ih h_nodup.2

/-- Helper: the mapM calls in procToVerifyStmt are effectively pure maps,
    since the body only uses `return` (no state mutation or error). -/
private theorem mapM_stateT_pure_eq {α β : Type} {σ : Type} {ε : Type}
    (f : α → β) (xs : List α) (s0 : σ) :
    (List.mapM (m := ExceptT ε (StateM σ)) (fun x => StateT.pure (Except.ok (f x))) xs) s0 =
    (Except.ok (xs.map f), s0) := by
  induction xs generalizing s0 with
  | nil => simp [List.mapM_nil, pure, ExceptT.pure]; rfl
  | cons a rest ih =>
    simp only [List.mapM_cons, bind, ExceptT.bind, ExceptT.mk,
      ExceptT.bindCont, pure, ExceptT.pure, StateT.bind, StateT.pure, List.map_cons]
    rw [ih]; rfl

/-! ## Verification Statement Structure -/

/-- Structure: the output of `procToVerifyStmt` is a block
    `prefix ++ [bodyBlock] ++ postAsserts`, and all prefix statements
    are `.cmd` (init/assume commands).
    Additionally, for any `ProcEnvWF` state `ρ₀`, there exists an initial
    state `ρ_init` from which the prefix steps to `ρ₀`. -/
theorem procToVerifyStmt_structure
    (proc : Procedure) (p : Program) (st st' : CoreTransformState)
    (verifyStmt : Statement)
    (h : (procToVerifyStmt proc).run st = (Except.ok verifyStmt, st'))
    (π : String → Option Procedure)
    (φ : CoreEval → PureFunc Expression → CoreEval)
    (h_wf_proc : WF.WFProcedureProp p proc) :
    ∃ (prefixStmts : List Statement),
      verifyStmt = Stmt.block s!"verify_{proc.header.name.name}"
        (prefixStmts ++ [Stmt.block s!"body_{proc.header.name.name}" proc.body #[]] ++
          ensuresToAsserts proc.spec.postconditions) #[] ∧
      (∀ s ∈ prefixStmts, ∃ c, s = Stmt.cmd c) ∧
      (∀ ρ₀, Core.Specification.ProcEnvWF proc ρ₀ →
        ∃ ρ_init,
          Imperative.StepStmtStar Expression (EvalCommand π φ) (EvalPureFunc φ)
            (.stmts prefixStmts ρ_init) (.terminal ρ₀)) := by
  unfold procToVerifyStmt at h
  simp only [bind, ExceptT.bind, ExceptT.mk, ExceptT.run, ExceptT.bindCont,
    pure, ExceptT.pure, StateT.bind] at h
  rw [mapM_stateT_pure_eq] at h
  have h_eq := (Prod.mk.inj h).1 |> Except.ok.inj
  -- Define the prefix components
  let inputInits := proc.header.inputs.toList.map fun (id, ty) =>
    Statement.init id (Lambda.LTy.forAll [] ty) .nondet #[]
  let outputOnlyInits := proc.header.getOutputOnlyParams.toList.map fun (id, ty) =>
    Statement.init id (Lambda.LTy.forAll [] ty) .nondet #[]
  let oldInoutInits := proc.header.getInoutParams.toList.map fun (id, ty) =>
    Statement.init (CoreIdent.mkOld id.name) (Lambda.LTy.forAll [] ty)
      (.det (LExpr.fvar Strata.SourceRange.none id none)) #[]
  let assumes := requiresToAssumes proc.spec.preconditions
  let prefixStmts := inputInits ++ outputOnlyInits ++ oldInoutInits ++ assumes
  refine ⟨prefixStmts, h_eq.symm, ?_, ?_⟩
  · intro s hs
    simp only [prefixStmts, List.mem_append] at hs
    rcases hs with ((hs | hs) | hs) | hs
    · -- inputInits
      simp only [inputInits, List.mem_map] at hs
      obtain ⟨⟨id, ty⟩, _, rfl⟩ := hs; exact ⟨_, rfl⟩
    · -- outputOnlyInits
      simp only [outputOnlyInits, List.mem_map] at hs
      obtain ⟨⟨id, ty⟩, _, rfl⟩ := hs; exact ⟨_, rfl⟩
    · -- oldInoutInits
      simp only [oldInoutInits, List.mem_map] at hs
      obtain ⟨⟨id, ty⟩, _, rfl⟩ := hs; exact ⟨_, rfl⟩
    · -- assumes
      simp only [assumes, requiresToAssumes, List.mem_map] at hs
      obtain ⟨⟨label, check⟩, _, rfl⟩ := hs; exact ⟨_, rfl⟩
  · intro ρ₀ h_wf
    refine ⟨prefixInitEnv _ ρ₀, prefixInitEnv_steps _ ρ₀ π φ h_wf.noFailure ?_⟩
    -- Split: (inputInits ++ outputOnlyInits ++ oldInoutInits) ++ assumes
    rw [show prefixStmts = (inputInits ++ outputOnlyInits ++ oldInoutInits) ++ assumes
        from by simp [prefixStmts, List.append_assoc]]
    rw [PrefixStepsOK_append]
    have h_assumes_id : prefixInitEnv assumes ρ₀ = ρ₀ := by
      apply prefixInitEnv_noninit_list
      intro s hs
      simp only [assumes, requiresToAssumes, List.mem_map] at hs
      obtain ⟨⟨l, c⟩, _, rfl⟩ := hs; simp [stmtInitVar]
    refine ⟨PrefixStepsOK_assumes π φ proc.spec.preconditions ρ₀
      h_wf.preconditionsHold h_wf.wfBool, ?_⟩
    rw [h_assumes_id]
    -- Split: (inputInits ++ outputOnlyInits) ++ oldInoutInits
    rw [show inputInits ++ outputOnlyInits ++ oldInoutInits =
        (inputInits ++ outputOnlyInits) ++ oldInoutInits
        from by simp [List.append_assoc]]
    rw [PrefixStepsOK_append]
    -- IO vars are not init'd in oldInoutInits (old inits only init mkOld variants)
    have h_io_not_in_old : ∀ x ∈ ListMap.keys proc.header.inputs ++ ListMap.keys proc.header.outputs,
        ∀ s ∈ oldInoutInits, stmtInitVar s ≠ some x := by
      intro x hx s hs hsx
      simp only [oldInoutInits, List.mem_map] at hs
      obtain ⟨⟨id, ty⟩, hmem, rfl⟩ := hs
      simp [stmtInitVar] at hsx
      exact absurd hsx.symm (h_wf_proc.ioNotOld x hx id.name)
    constructor
    · -- PrefixStepsOK for oldInoutInits at ρ₀
      apply PrefixStepsOK_det_init_map π φ _ _ h_wf.wfVar
      · -- inout params are defined in store (they are inputs)
        intro id hid
        rw [← ListMap.keys_eq_map_fst] at hid
        have h_in_inputs := getInoutParams_keys_subset_inputs proc.header id hid
        exact h_wf.storeDefined id (by
          unfold Specification.procVerifyInitIdents
          simp only [List.mem_append]; left; left; exact h_in_inputs)
      · -- mkOld of inout params are defined in store
        intro id hid
        rw [← ListMap.keys_eq_map_fst] at hid
        exact h_wf.storeDefined (CoreIdent.mkOld id.name) (by
          unfold Specification.procVerifyInitIdents
          simp only [List.mem_append]; right
          exact List.mem_map.mpr ⟨id, hid, rfl⟩)
      · -- inout params match their old snapshots
        intro id hid
        rw [← ListMap.keys_eq_map_fst] at hid
        exact h_wf.oldInoutMatchesInout id hid
      · -- keys of getInoutParams are nodup
        rw [← ListMap.keys_eq_map_fst]
        exact getInoutParams_nodup proc.header h_wf_proc.inputsNodup
      · -- inout params are not old-prefixed (they are inputs)
        intro id hid
        rw [← ListMap.keys_eq_map_fst] at hid
        have h_in_io := getInoutParams_keys_in_io proc.header id hid
        exact h_wf_proc.ioNotOld id h_in_io
      · -- mkOld images of inout params are nodup
        exact nodup_mkOld_map _ (by
          rw [← ListMap.keys_eq_map_fst]
          exact getInoutParams_nodup proc.header h_wf_proc.inputsNodup)
    · -- PrefixStepsOK for inputInits ++ outputOnlyInits at prefixInitEnv oldInoutInits ρ₀
      have h_old_env := prefixInitEnv_eval oldInoutInits ρ₀
      have h_wfVar_old : WellFormedSemanticEvalVar (prefixInitEnv oldInoutInits ρ₀).eval := by
        rw [h_old_env]; exact h_wf.wfVar
      rw [PrefixStepsOK_append]
      constructor
      · -- outputOnlyInits at prefixInitEnv oldInoutInits ρ₀
        apply PrefixStepsOK_nondet_init_map π φ _ _ h_wfVar_old
        · intro id hid
          rw [prefixInitEnv_store_not_init]
          · rw [← ListMap.keys_eq_map_fst] at hid
            have h_in_outputs := getOutputOnlyParams_keys_subset_outputs proc.header id hid
            exact h_wf.storeDefined id (by
              unfold Specification.procVerifyInitIdents
              simp only [List.mem_append]; left; right; exact h_in_outputs)
          · rw [← ListMap.keys_eq_map_fst] at hid
            have h_in_outputs := getOutputOnlyParams_keys_subset_outputs proc.header id hid
            exact h_io_not_in_old id (List.mem_append_right _ h_in_outputs)
        · rw [← ListMap.keys_eq_map_fst]
          exact getOutputOnlyParams_nodup proc.header h_wf_proc.outputsNodup
      · -- inputInits at prefixInitEnv outputOnlyInits (prefixInitEnv oldInoutInits ρ₀)
        have h_outenv := prefixInitEnv_eval outputOnlyInits (prefixInitEnv oldInoutInits ρ₀)
        have h_wfVar_out' : WellFormedSemanticEvalVar
            (prefixInitEnv outputOnlyInits (prefixInitEnv oldInoutInits ρ₀)).eval := by
          rw [h_outenv]; exact h_wfVar_old
        apply PrefixStepsOK_nondet_init_map π φ _ _ h_wfVar_out'
        · intro id hid
          rw [prefixInitEnv_store_not_init]
          · rw [prefixInitEnv_store_not_init]
            · rw [← ListMap.keys_eq_map_fst] at hid
              exact h_wf.storeDefined id (by
                unfold Specification.procVerifyInitIdents
                simp only [List.mem_append]; left; left; exact hid)
            · rw [← ListMap.keys_eq_map_fst] at hid
              exact h_io_not_in_old id (List.mem_append_left _ hid)
          · -- input id not init'd in outputOnlyInits: by construction,
            -- getOutputOnlyParams only contains ids NOT in inputs
            intro s hs heq_s
            simp only [outputOnlyInits, List.mem_map] at hs
            obtain ⟨⟨oid, oty⟩, hmem, rfl⟩ := hs
            simp [stmtInitVar] at heq_s
            rw [← ListMap.keys_eq_map_fst] at hid
            -- oid is in getOutputOnlyParams, so oid ∉ inputs
            have h_oid_keys : oid ∈ ListMap.keys proc.header.getOutputOnlyParams := by
              rw [ListMap.keys_eq_map_fst]
              simp only [ListMap.toList] at hmem
              exact List.mem_map_of_mem (f := Prod.fst) hmem
            have h_oid_not_in_inputs := getOutputOnlyParams_keys_disjoint_inputs proc.header oid h_oid_keys
            -- But heq_s says id = oid, so id ∉ inputs, contradiction
            exact h_oid_not_in_inputs (heq_s ▸ hid)
        · rw [← ListMap.keys_eq_map_fst]; exact h_wf_proc.inputsNodup

/-! ## Postcondition Assert Helpers -/

private theorem ensuresToAsserts_mem_is_assert
    {s : Statement} {pcs : ListMap CoreLabel Procedure.Check}
    (h : s ∈ ensuresToAsserts pcs) :
    ∃ l e md, s = Statement.assert l e md := by
  simp only [ensuresToAsserts, List.mem_filterMap] at h
  obtain ⟨⟨label, check⟩, _, h_eq⟩ := h
  split at h_eq
  · simp at h_eq
  · simp at h_eq; exact ⟨label, check.expr, check.md, h_eq.symm⟩

/-! ## Main Theorem -/

/-- If all asserts are valid in the verification statement produced by
    `procToVerifyStmt` (for initial environments satisfying `ProcEnvWF`),
    then `ProcedureCorrect` holds for the procedure. -/
theorem procBodyVerify_procedureCorrect
    (π : String → Option Procedure) (φ : CoreEval → PureFunc Expression → CoreEval)
    (proc : Procedure) (p : Program) (st : CoreTransformState)
    (verifyStmt : Statement) (st' : CoreTransformState)
    -- `h_transform`: procToVerifyStmt returned successfully.
    (h_transform : (procToVerifyStmt proc).run st = (Except.ok verifyStmt, st'))
    -- `h_correct`: all asserts in `verifyStmt` are valid for all initial states
    (h_correct : Specification.AllAssertsValid
      (Core.Specification.Lang.core π φ) verifyStmt)
    -- `h_wf_ext`: the evaluator extension `φ` is well-formed
    (h_wf_ext : Core.WFEvalExtension φ)
    -- `h_wf_proc`: the procedure is well-formed
    (h_wf_proc : WF.WFProcedureProp p proc) :
    -- Conclusion: ProcedureCorrect holds.
    Core.Specification.ProcedureCorrect π φ proc p := by

  obtain ⟨prefixStmts, h_eq, h_prefix_cmd, h_prefix_trace⟩ :=
    procToVerifyStmt_structure proc p st st' verifyStmt h_transform π φ h_wf_proc
  let verifyLabel := s!"verify_{proc.header.name.name}"
  let bodyLabel := s!"body_{proc.header.name.name}"
  let postAsserts := ensuresToAsserts proc.spec.postconditions

  /- Helper: embed a body trace (.stmts body ρ₀ →* cfg) into a verifyStmt trace
     (.stmt verifyStmt ρ_init →* cfg_wrapped), where cfg_wrapped has the same
     getEval, getStore, and coreIsAtAssert as cfg but is wrapped in the
     verifyStmt context (block verifyLabel > seq > block bodyLabel). -/
  have h_embed_body : ∀ ρ₀ (h_wf : Specification.ProcEnvWF proc ρ₀)
      (cfg : CoreConfig),
      CoreStepStar π φ (.stmts proc.body ρ₀) cfg →
      ∃ ρ_init,
        StepStmtStar Expression (EvalCommand π φ) (EvalPureFunc φ)
          (.stmt verifyStmt ρ_init)
          (.block verifyLabel (.seq (.block bodyLabel cfg) postAsserts)) := by
    intro ρ₀ h_wf cfg h_body
    obtain ⟨ρ_init, h_prefix⟩ := h_prefix_trace ρ₀ h_wf
    exact ⟨ρ_init, by
      rw [h_eq]
      exact ReflTrans_Transitive _ _ _ _
        (step_block_enter Expression (EvalCommand π φ) (EvalPureFunc φ) verifyLabel _ #[] ρ_init)
        (block_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ) _ _ verifyLabel
          (ReflTrans_Transitive _ _ _ _
            (by rw [List.append_assoc]
                exact stmts_prefix_terminal_append Expression (EvalCommand π φ) (EvalPureFunc φ)
                  prefixStmts _ ρ_init ρ₀ h_prefix)
            (ReflTrans_Transitive _ _ _ _
              (.step _ _ _ .step_stmts_cons (.refl _))
              (seq_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ) _ _ postAsserts
                (ReflTrans_Transitive _ _ _ _
                  (step_block_enter Expression (EvalCommand π φ) (EvalPureFunc φ) bodyLabel _ #[] ρ₀)
                  (block_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ) _ _ bodyLabel
                    (CoreStepStar_to_StepStmtStar h_body)))))))⟩

  /- Helper: coreIsAtAssert and getEval/getStore are preserved through
     the verifyStmt wrapping (block > seq > block). -/
  have h_wrapped_assert : ∀ (cfg : CoreConfig) (a : AssertId Expression),
      coreIsAtAssert cfg a →
      coreIsAtAssert (.block verifyLabel (.seq (.block bodyLabel cfg) postAsserts)) a := by
    intro cfg a h
    simp only [coreIsAtAssert]
    exact h

  have h_wrapped_eval : ∀ (cfg : CoreConfig),
      Config.getEval (.block verifyLabel (.seq (.block bodyLabel cfg) postAsserts)) =
      Config.getEval cfg := by
    intro cfg; simp [Config.getEval]

  have h_wrapped_store : ∀ (cfg : CoreConfig),
      Config.getStore (.block verifyLabel (.seq (.block bodyLabel cfg) postAsserts)) =
      Config.getStore cfg := by
    intro cfg; simp [Config.getStore]

  -- Unfold h_correct for easier application
  have h_correct' : ∀ (a : AssertId Expression) (ρ_init : Env Expression)
      (cfg : CoreConfig),
      StepStmtStar Expression (EvalCommand π φ) (EvalPureFunc φ)
        (.stmt verifyStmt ρ_init) cfg →
      coreIsAtAssert cfg a →
      cfg.getEval cfg.getStore a.expr = some HasBool.tt := by
    intro a ρ_init cfg h_star h_assert
    exact h_correct a ρ_init cfg trivial h_star h_assert

  -- Unified helper: all asserts reachable from proc.body are valid
  have body_asserts_valid : ∀ ρ₀ (h_wf : Specification.ProcEnvWF proc ρ₀)
      (a : AssertId Expression) (cfg : CoreConfig),
      CoreStepStar π φ (.stmts proc.body ρ₀) cfg →
      coreIsAtAssert cfg a →
      cfg.getEval cfg.getStore a.expr = some HasBool.tt := by
    intro ρ₀ h_wf a cfg h_body h_assert
    obtain ⟨_, h_vt⟩ := h_embed_body ρ₀ h_wf cfg h_body
    have h_v := h_correct' a _
      (.block verifyLabel (.seq (.block bodyLabel cfg) postAsserts))
      h_vt (h_wrapped_assert cfg a h_assert)
    rw [h_wrapped_eval, h_wrapped_store] at h_v
    exact h_v

  refine ⟨?_, ?_⟩

  · ----- Part 1: All asserts in proc.body are valid -----
    intro a
    unfold Specification.AssertValidInProcedure Specification.AssertValidWhen
    simp only [Specification.Lang.core, Specification.Lang.imperative]
    intro ρ₀ cfg (h_wf : Specification.ProcEnvWF proc ρ₀)
      (h_body : StepStmtStar Expression (EvalCommand π φ) (EvalPureFunc φ)
        (.stmt (Stmt.block "" proc.body #[]) ρ₀) cfg)
      (h_assert : coreIsAtAssert cfg a)
    -- Extract first step: .stmt (block "" body #[]) ρ₀ → .block "" (.stmts body ρ₀)
    have h_block_star : StepStmtStar Expression (EvalCommand π φ) (EvalPureFunc φ)
        (.block "" (.stmts proc.body ρ₀)) cfg := by
      cases h_body with
      | refl => simp [coreIsAtAssert] at h_assert
      | step _ _ _ hstep hrest => cases hstep; exact hrest
    -- Body never exits (from WFProcedureProp.bodyExitsCovered)
    have h_no_exit : ∀ lbl ρ', ¬ StepStmtStar Expression (EvalCommand π φ) (EvalPureFunc φ)
        (.stmts proc.body ρ₀) (.exiting lbl ρ') :=
      block_exitsCoveredByBlocks_noEscape Expression (EvalCommand π φ) (EvalPureFunc φ)
        proc.body h_wf_proc.bodyExitsCovered ρ₀
    -- cfg is not terminal or exiting (has an assert)
    have h_nt : ∀ ρ', cfg ≠ .terminal ρ' := by
      intro ρ' heq; subst heq; exact coreIsAtAssert_not_terminal ρ' a h_assert
    have h_nx : ∀ lbl ρ', cfg ≠ .exiting lbl ρ' := by
      intro lbl ρ' heq; subst heq; exact coreIsAtAssert_not_exiting lbl ρ' a h_assert
    -- Extract inner: cfg = .block "" inner where .stmts body ρ₀ →* inner
    obtain ⟨inner, rfl, h_inner_star⟩ :=
      block_star_extract_inner Expression (EvalCommand π φ) (EvalPureFunc φ) h_block_star h_no_exit h_nt h_nx
    -- coreIsAtAssert and getEval/getStore are transparent through block ""
    have h_assert_inner : coreIsAtAssert inner a := by
      simpa [coreIsAtAssert] using h_assert
    -- Convert to CoreStepStar and use body_asserts_valid
    have h_inner_core := StepStmtStar_to_CoreStepStar h_inner_star
    have h_valid := body_asserts_valid ρ₀ h_wf a inner h_inner_core h_assert_inner
    simpa [Config.getEval, Config.getStore] using h_valid

  · ----- Part 2: Postconditions + hasFailure on termination -----
    intro h_wf_proc ρ₀ ρ' h_wf h_term
    obtain ⟨ρ_init, h_prefix⟩ := h_prefix_trace ρ₀ h_wf
    -- h_valid: all asserts in body from ρ₀ evaluate to true
    have h_valid : ∀ (a : AssertId Expression) (cfg : CoreConfig),
        CoreStepStar π φ (.stmts proc.body ρ₀) cfg →
        coreIsAtAssert cfg a →
        cfg.getEval cfg.getStore a.expr = some HasBool.tt :=
      fun a cfg h h' => body_asserts_valid ρ₀ h_wf a cfg h h'
    -- hasFailure = false
    have h_nf' : ρ'.hasFailure = Bool.false :=
      Core.core_noFailure_preserved π φ
        (.stmts proc.body ρ₀) (.terminal ρ') h_valid h_wf.noFailure h_term
    -- wfBool preservation
    have h_wfb_term : WellFormedSemanticEvalBool ρ'.eval :=
      Core.core_wfBool_preserved π φ h_wf_ext
        (.stmts proc.body ρ₀) (.terminal ρ') h_wf.wfBool h_term

    have h_to_post : StepStmtStar Expression (EvalCommand π φ) (EvalPureFunc φ)
        (.stmt verifyStmt ρ_init) (.block verifyLabel (.stmts postAsserts ρ')) := by
      rw [h_eq]
      exact ReflTrans_Transitive _ _ _ _
        (step_block_enter Expression (EvalCommand π φ) (EvalPureFunc φ) verifyLabel _ #[] ρ_init)
        (block_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ) _ _ verifyLabel
          (ReflTrans_Transitive _ _ _ _
            (by rw [List.append_assoc]
                exact stmts_prefix_terminal_append Expression (EvalCommand π φ) (EvalPureFunc φ)
                  prefixStmts _ ρ_init ρ₀ h_prefix)
            (ReflTrans_Transitive _ _ _ _
              (.step _ _ _ .step_stmts_cons (.refl _))
              (ReflTrans_Transitive _ _ _ _
                (seq_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ) _ _ postAsserts
                  (ReflTrans_Transitive _ _ _ _
                    (step_block_enter Expression (EvalCommand π φ) (EvalPureFunc φ) bodyLabel _ #[] ρ₀)
                    (block_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ) _ _ bodyLabel
                      (CoreStepStar_to_StepStmtStar h_term))))
                (ReflTrans_Transitive _ _ _ _
                  (seq_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ) _ _ postAsserts
                    (.step _ _ _ .step_block_done (.refl _)))
                  (.step _ _ _ .step_seq_done (.refl _)))))))
    -- Show every postcondition assert evaluates to true
    -- by induction on the suffix of postAsserts
    have h_all_post_valid : ∀ s ∈ postAsserts, ∀ l e md,
        s = Statement.assert l e md → ρ'.eval ρ'.store e = some HasBool.tt := by
      suffices h_sfx :
          ∀ (sfx : List Statement),
            (∀ s ∈ sfx, ∃ l e md, s = Statement.assert l e md) →
            StepStmtStar Expression (EvalCommand π φ) (EvalPureFunc φ)
              (.stmt verifyStmt ρ_init) (.block verifyLabel (.stmts sfx ρ')) →
            ∀ s ∈ sfx, ∀ l e md,
              s = Statement.assert l e md →
              ρ'.eval ρ'.store e = some HasBool.tt by
        exact h_sfx postAsserts
          (fun s hs => ensuresToAsserts_mem_is_assert hs) h_to_post
      intro sfx h_all_assert h_trace
      induction sfx with
      | nil => intro _ h_mem; contradiction
      | cons hd tl ih =>
        intro s h_mem l e md h_s_eq
        have ⟨lh, eh, mdh, h_hd_eq⟩ := h_all_assert hd (.head _)
        subst h_hd_eq
        have h_at_head : coreIsAtAssert
            (.block verifyLabel (.stmts (Statement.assert lh eh mdh :: tl) ρ'))
            ⟨lh, eh⟩ := by
          simp only [coreIsAtAssert]; exact ⟨trivial, trivial⟩
        have h_head_eval := h_correct' ⟨lh, eh⟩ ρ_init _ h_trace h_at_head
        simp only [Config.getEval, Config.getStore] at h_head_eval
        cases h_mem with
        | head _ =>
          injection h_s_eq with h1; injection h1 with h2
          injection h2 with _ h3; subst h3; exact h_head_eval
        | tail _ h_in_tl =>
          have h_assert_step : StepStmtStar Expression (EvalCommand π φ) (EvalPureFunc φ)
              (.stmt (Statement.assert lh eh mdh) ρ') (.terminal ρ') := by
            have h1 : StepStmtStar Expression (EvalCommand π φ) (EvalPureFunc φ)
                (.stmt (Statement.assert lh eh mdh) ρ')
                (.terminal ⟨ρ'.store, ρ'.eval, ρ'.hasFailure || false⟩) :=
              .step _ _ _
                (.step_cmd (@EvalCommand.cmd_sem π φ ρ'.eval ρ'.store
                  (Cmd.assert lh eh mdh) ρ'.store false
                  (EvalCmd.eval_assert_pass h_head_eval h_wfb_term)))
                (.refl _)
            have h2 : (⟨ρ'.store, ρ'.eval, ρ'.hasFailure || false⟩ : Env Expression) = ρ' := by
              cases ρ'; simp [Bool.or_false]
            rw [h2] at h1; exact h1
          have h_trace_tl := ReflTrans_Transitive _ _ _ _ h_trace
            (block_inner_star Expression (EvalCommand π φ) (EvalPureFunc φ) _ _ verifyLabel
              (stmts_cons_step Expression (EvalCommand π φ) (EvalPureFunc φ)
                (Statement.assert lh eh mdh) tl ρ' ρ' h_assert_step))
          exact ih (fun s' hs' => h_all_assert s' (.tail _ hs'))
            h_trace_tl s h_in_tl l e md h_s_eq
    -- Prove postconditions hold and hasFailure is false
    constructor
    · -- Each non-free postcondition evaluates to true
      intro label check h_mem h_attr
      have h_in : Statement.assert label check.expr check.md ∈ postAsserts := by
        simp only [postAsserts, ensuresToAsserts, List.mem_filterMap]
        exact ⟨(label, check), h_mem, by simp [h_attr]⟩
      exact h_all_post_valid _ h_in label check.expr check.md rfl
    · exact h_nf'

end ProcBodyVerifyCorrect
