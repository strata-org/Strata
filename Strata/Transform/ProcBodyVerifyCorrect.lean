/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.ProcBodyVerify
public import Strata.Transform.CoreSpecificationProps
public import Strata.Languages.Core.Analysis.ProcedureCorrectnessProps
import Std.Tactic.BVDecide.Normalize.Prop
import Strata.Languages.Core.ProcedureWF
import Strata.Languages.Core.StatementSemanticsProps
import Strata.DL.Imperative.Logic.TraceInterpProps
import all Strata.Util.ListMap

public section

/-! # Procedure Body Verification Correctness Proof

`procToVerifyStmt` turns a procedure into one verification statement: its
parameters are initialized, its preconditions assumed, its body run, and its
non-free postconditions asserted. The theorems here say that validity of that
statement establishes the procedure's correctness.

## Key results

- `procBodyVerify_procedureCorrectOnTraces`: if every event trace of the
  verification statement is assertion-valid under a condition interpretation
  in which evaluator-true assumptions hold, the procedure satisfies
  `ProcedureAssertsValidOnTraces` under it. A call emits its callee's contract
  checks into the trace, so no assumption about calls is needed.
- `procToVerifyStmt_structure`: the verification statement is a prefix of
  initializations and assumptions, the body block, and the postcondition
  asserts, and the prefix can reach every well-formed entry environment.
-/

namespace ProcBodyVerifyCorrect

open Core Core.ProcBodyVerify Imperative Lambda Transform Core.WF

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


@[simp] private theorem prefixInitEnv_hasFailure (stmts : List Statement) (ρ : Imperative.Env Expression) :
    (prefixInitEnv stmts ρ).hasFailure = ρ.hasFailure := by
  induction stmts with
  | nil => rfl
  | cons s rest ih => simp [prefixInitEnv]; cases stmtInitVar s <;> simp [ih]

@[simp] private theorem prefixInitEnv_factory (stmts : List Statement) (ρ : Imperative.Env Expression) :
    (prefixInitEnv stmts ρ).factory = ρ.factory := by
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

/-- `prefixInitEnv` only ever clears bindings (sets them to `none`), so it
    preserves store well-formedness (value-only-ness). -/
private theorem prefixInitEnv_store_wf (stmts : List Statement)
    (ρ : Imperative.Env Expression) (fac : Expression.Factory)
    (h : Imperative.WellFormedStore ρ.store fac) :
    Imperative.WellFormedStore (prefixInitEnv stmts ρ).store fac := by
  induction stmts with
  | nil => exact h
  | cons s rest ih =>
    intro y w hy
    simp only [prefixInitEnv] at hy
    cases hsv : stmtInitVar s with
    | none => simp only [hsv] at hy; exact ih y w hy
    | some x =>
      simp only [hsv] at hy
      split at hy
      · exact absurd hy (by simp)
      · exact ih y w hy

/-- Recursive predicate: each statement in the list can step correctly
    from its `prefixInitEnv` state. -/
private def PrefixStepsOK
    (π : String → Option Procedure)
    : List Statement → Imperative.Env Expression → Prop
  | [], _ => True
  | s :: rest, ρ =>
    PrefixStepsOK π rest ρ ∧
    ∃ c, s = Stmt.cmd c ∧
      ∃ σ', EvalCommand π (prefixInitEnv (s :: rest) ρ).factory (prefixInitEnv (s :: rest) ρ).store c σ' false ∧
        σ' = (prefixInitEnv rest ρ).store

private theorem Env_eq {ρ₁ ρ₂ : Imperative.Env Expression}
    (h_s : ρ₁.store = ρ₂.store)
    (h_fac : ρ₁.factory = ρ₂.factory)
    (h_f : ρ₁.hasFailure = ρ₂.hasFailure) :
    ρ₁ = ρ₂ := by
  cases ρ₁; cases ρ₂; simp_all

/-- If `PrefixStepsOK` holds and `hasFailure` is false,
    stepping from `prefixInitEnv stmts ρ` reaches `.terminal ρ`. -/
private theorem prefixInitEnv_steps
    (stmts : List Statement) (ρ : Imperative.Env Expression)
    (π : String → Option Procedure)
    (h_hf : ρ.hasFailure = false)
    (h_ok : PrefixStepsOK π stmts ρ) :
    Imperative.StepStmtStar Expression (EvalCommand π)
      (.stmts stmts (prefixInitEnv stmts ρ)) (.terminal ρ) := by
  induction stmts with
  | nil =>
    simp [prefixInitEnv]
    exact .step _ _ _ .step_stmts_nil (.refl _)
  | cons s rest ih =>
    obtain ⟨h_ok_rest, c, rfl, σ', h_eval, h_σ'⟩ := h_ok
    have ih' := ih h_ok_rest
    have h_env_eq : { (prefixInitEnv (Stmt.cmd c :: rest) ρ) with
        store := σ',
        hasFailure := (prefixInitEnv (Stmt.cmd c :: rest) ρ).hasFailure || false } =
        prefixInitEnv rest ρ :=
      Env_eq h_σ' (by simp [prefixInitEnv_factory])
        (by simp [prefixInitEnv_hasFailure, h_hf])
    have h_one_step : StepStmtStar Expression (EvalCommand π)
        (.stmt (Stmt.cmd c) (prefixInitEnv (Stmt.cmd c :: rest) ρ))
        (.terminal (prefixInitEnv rest ρ)) :=
      .step _ _ _ (.step_cmd h_eval) (h_env_eq ▸ .refl _)
    exact ReflTrans_Transitive _ _ _ _
      (stmts_cons_step Expression (EvalCommand π)
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
    (a b : List Statement) (ρ : Imperative.Env Expression) :
    PrefixStepsOK π (a ++ b) ρ ↔
      PrefixStepsOK π b ρ ∧ PrefixStepsOK π a (prefixInitEnv b ρ) := by
  induction a with
  | nil => simp [PrefixStepsOK]
  | cons s rest ih =>
    simp only [List.cons_append, PrefixStepsOK]
    rw [ih]
    constructor
    · rintro ⟨⟨hb, hrest⟩, c, hs, σ', heval, hσ'⟩
      refine ⟨hb, ⟨hrest, c, hs, σ', ?_, ?_⟩⟩
      · have h2 : prefixInitEnv (s :: rest) (prefixInitEnv b ρ) = prefixInitEnv ((s :: rest) ++ b) ρ := by
          rw [← prefixInitEnv_append]
        rw [h2]; exact heval
      · have h2 : prefixInitEnv rest (prefixInitEnv b ρ) = prefixInitEnv (rest ++ b) ρ := by
          rw [← prefixInitEnv_append]
        rw [h2]; exact hσ'
    · rintro ⟨hb, hrest, c, hs, σ', heval, hσ'⟩
      refine ⟨⟨hb, hrest⟩, c, hs, σ', ?_, ?_⟩
      · have h2 : prefixInitEnv (s :: rest) (prefixInitEnv b ρ) = prefixInitEnv ((s :: rest) ++ b) ρ := by
          rw [← prefixInitEnv_append]
        rw [h2] at heval; exact heval
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
    (π : String → Option Procedure)
    (preconds : ListMap CoreLabel Procedure.Check)
    (ρ : Imperative.Env Expression)
    (h_preconds : ∀ (label : CoreLabel) (check : Procedure.Check),
      (label, check) ∈ preconds.toList →
      Expression.eval ρ.factory ρ.store check.expr = some HasBool.tt)
    (h_wfBool : WellFormedSemanticEvalBool (P := Expression) ρ.factory) :
    PrefixStepsOK π (requiresToAssumes preconds) ρ := by
  suffices h : ∀ (items : List (CoreLabel × Procedure.Check)),
      (∀ (label : CoreLabel) (check : Procedure.Check),
        (label, check) ∈ items → Expression.eval ρ.factory ρ.store check.expr = some HasBool.tt) →
      PrefixStepsOK π (items.map fun (label, check) => Statement.assume label check.expr check.md) ρ from
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
    have h_rest_ok : PrefixStepsOK π
        (rest.map fun x => Statement.assume x.1 x.2.expr x.2.md) ρ :=
      ih (fun l c hmem => h_items l c (List.mem_cons_of_mem (label, check) hmem))
    have h_store_eq : (prefixInitEnv (Statement.assume label check.expr check.md ::
        rest.map fun x => Statement.assume x.1 x.2.expr x.2.md) ρ).store = ρ.store := by
      rw [prefixInitEnv_store_noninit _ _ _ rfl, h_env_eq]
    exact ⟨h_rest_ok, _, rfl, _,
      by simp only [prefixInitEnv_factory]
         rw [h_store_eq]
         exact EvalCommand.cmd_sem (EvalCmd.eval_assume
           (h_items label check List.mem_cons_self) h_wfBool),
      by show _ = (prefixInitEnv _ ρ).store; rw [h_env_eq]⟩

/-- For a nondet init statement, if `x` is none in the pre-state and some in the target,
    and all other variables match, then PrefixStepsOK holds for the singleton. -/
private theorem PrefixStepsOK_nondet_init_cons
    (π : String → Option Procedure)
    (x : Expression.Ident) (ty : Expression.Ty) (rest : List Statement)
    (ρ : Imperative.Env Expression)
    (h_wfVar : WellFormedSemanticEvalVar (P := Expression) ρ.factory)
    (h_rest : PrefixStepsOK π rest ρ)
    (h_ty : ∃ v, (prefixInitEnv rest ρ).store x = some v ∧
      HasVal.valueOfTy ρ.factory v ty) :
    PrefixStepsOK π (Statement.init x ty .nondet #[] :: rest) ρ := by
  constructor
  · exact h_rest
  · refine ⟨_, rfl, (prefixInitEnv rest ρ).store, ?_, rfl⟩
    simp only [prefixInitEnv_factory]
    have h_none : (prefixInitEnv (Statement.init x ty .nondet #[] :: rest) ρ).store x = none :=
      prefixInitEnv_store_init _ _ _ _ rfl
    obtain ⟨v, hv, hvty⟩ := h_ty
    exact EvalCommand.cmd_sem (EvalCmd.eval_init_unconstrained
      (InitState.init h_none hv (fun y hne => by
        exact (prefixInitEnv_store_other _ _ _ y x rfl hne).symm))
      hvty
      h_wfVar)

/-- PrefixStepsOK for a list of nondet init statements from a map. -/
private theorem PrefixStepsOK_nondet_init_map
    (π : String → Option Procedure)
    (entries : List (Expression.Ident × Lambda.LMonoTy))
    (ρ : Imperative.Env Expression)
    (h_wfVar : WellFormedSemanticEvalVar (P := Expression) ρ.factory)
    (h_typed : ∀ id ty', (id, ty') ∈ entries →
      ∃ v, ρ.store id = some v ∧
        HasVal.valueOfTy ρ.factory v (Lambda.LTy.forAll [] ty'))
    (h_nodup : (entries.map Prod.fst).Nodup)
    : PrefixStepsOK π
        (entries.map fun (id, ty) => Statement.init id (Lambda.LTy.forAll [] ty) .nondet #[]) ρ := by
  induction entries with
  | nil => exact trivial
  | cons e rest ih =>
    obtain ⟨id, ty⟩ := e
    simp only [List.map] at h_nodup ⊢
    rw [List.nodup_cons] at h_nodup
    apply PrefixStepsOK_nondet_init_cons π id (Lambda.LTy.forAll [] ty)
    · exact h_wfVar
    · exact ih (fun i t hi => h_typed i t (List.mem_cons_of_mem _ hi)) h_nodup.2
    · -- typed value for id, transported across the rest's inits
      obtain ⟨v, hv, hvty⟩ := h_typed id ty List.mem_cons_self
      refine ⟨v, ?_, hvty⟩
      rw [prefixInitEnv_store_not_init]
      · exact hv
      · intro s hs
        simp only [List.mem_map] at hs
        obtain ⟨⟨id', ty'⟩, hmem, rfl⟩ := hs
        simp [stmtInitVar]
        intro heq
        exact h_nodup.1 (heq ▸ List.mem_map_of_mem (f := Prod.fst) hmem)

/-- For a deterministic init `init oldG ty (.det (fvar id))`, if `id` has a value
    in the pre-state, `oldG` is none, and `oldG ≠ id`, then it steps correctly. -/
private theorem PrefixStepsOK_det_init_cons
    (π : String → Option Procedure)
    (id : Expression.Ident) (oldG : Expression.Ident) (ty : Expression.Ty) (rest : List Statement)
    (ρ : Imperative.Env Expression)
    (h_wfStore : Imperative.WellFormedStore ρ.store ρ.factory)
    (h_wfVar : WellFormedSemanticEvalVar (P := Expression) ρ.factory)
    (h_rest : PrefixStepsOK π rest ρ)
    (h_ty : ∃ v, (prefixInitEnv rest ρ).store oldG = some v ∧
      HasVal.valueOfTy ρ.factory v ty)
    (h_id_eq_old : (prefixInitEnv rest ρ).store id = (prefixInitEnv rest ρ).store oldG)
    (h_ne : oldG ≠ id) :
    PrefixStepsOK π
      (Statement.init oldG ty (.det (LExpr.fvar () id none)) #[] :: rest) ρ := by
  constructor
  · exact h_rest
  · refine ⟨_, rfl, (prefixInitEnv rest ρ).store, ?_, rfl⟩
    simp only [prefixInitEnv_factory]
    have h_none : (prefixInitEnv (Statement.init oldG ty (.det (LExpr.fvar () id none)) #[] :: rest) ρ).store oldG = none :=
      prefixInitEnv_store_init _ _ _ _ rfl
    have h_id_val : (prefixInitEnv (Statement.init oldG ty (.det (LExpr.fvar () id none)) #[] :: rest) ρ).store id =
        (prefixInitEnv rest ρ).store id := by
      rw [prefixInitEnv_store_other _ _ _ id oldG rfl h_ne]
    obtain ⟨v, hv, hvty⟩ := h_ty
    have h_getFvar : HasFvar.getFvar (LExpr.fvar () id none : Expression.Expr) = some id := by
      simp [HasFvar.getFvar]
    have h_eval : Expression.eval ρ.factory (prefixInitEnv (Statement.init oldG ty (.det (LExpr.fvar () id none)) #[] :: rest) ρ).store
        (LExpr.fvar () id none) = some v := by
      have h_wfStore' := prefixInitEnv_store_wf
        (Statement.init oldG ty (.det (LExpr.fvar () id none)) #[] :: rest) ρ ρ.factory h_wfStore
      rw [h_wfVar _ _ _ h_wfStore' h_getFvar, h_id_val, h_id_eq_old, hv]
    exact EvalCommand.cmd_sem (EvalCmd.eval_init h_eval
      (InitState.init h_none hv (fun y hne => by
        exact (prefixInitEnv_store_other _ _ _ y oldG rfl hne).symm))
      hvty
      h_wfVar)

/-- PrefixStepsOK for a list of det init statements `init (mkOld id.name) ty (.det (fvar id))`. -/
private theorem PrefixStepsOK_det_init_map
    (π : String → Option Procedure)
    (entries : List (Expression.Ident × Lambda.LMonoTy))
    (ρ : Imperative.Env Expression)
    (h_wfStore : Imperative.WellFormedStore ρ.store ρ.factory)
    (h_wfVar : WellFormedSemanticEvalVar (P := Expression) ρ.factory)
    (h_defined : ∀ id ∈ entries.map Prod.fst,
      (ρ.store id).isSome)
    (h_old_typed : ∀ id ty', (id, ty') ∈ entries →
      ∃ v, ρ.store (CoreIdent.mkOld id.name) = some v ∧
        HasVal.valueOfTy ρ.factory v (Lambda.LTy.forAll [] ty'))
    (h_old_match : ∀ id ∈ entries.map Prod.fst,
      ρ.store id = ρ.store (CoreIdent.mkOld id.name))
    (h_nodup : (entries.map Prod.fst).Nodup)
    (h_not_old : ∀ id ∈ entries.map Prod.fst, ∀ x, id ≠ CoreIdent.mkOld x)
    (h_nodup_old : ((entries.map Prod.fst).map (fun id => CoreIdent.mkOld id.name)).Nodup)
    : PrefixStepsOK π
        (entries.map fun (id, ty) =>
          Statement.init (CoreIdent.mkOld id.name) (Lambda.LTy.forAll [] ty)
            (.det (LExpr.fvar () id none)) #[]) ρ := by
  induction entries with
  | nil => exact trivial
  | cons e rest ih =>
    obtain ⟨id, ty⟩ := e
    simp only [List.map] at h_defined h_old_match h_nodup h_not_old h_nodup_old ⊢
    rw [List.nodup_cons] at h_nodup h_nodup_old
    apply PrefixStepsOK_det_init_cons π id (CoreIdent.mkOld id.name)
      (Lambda.LTy.forAll [] ty) _ ρ h_wfStore h_wfVar
    · exact ih (fun i hi => h_defined i (List.mem_cons_of_mem _ hi))
              (fun i t hi => h_old_typed i t (List.mem_cons_of_mem _ hi))
              (fun i hi => h_old_match i (List.mem_cons_of_mem _ hi))
              h_nodup.2
              (fun i hi => h_not_old i (List.mem_cons_of_mem _ hi))
              h_nodup_old.2
    · -- typed old snapshot for mkOld id.name, transported across rest's old inits
      obtain ⟨v, hv, hvty⟩ := h_old_typed id ty List.mem_cons_self
      refine ⟨v, ?_, hvty⟩
      rw [prefixInitEnv_store_not_init]
      · exact hv
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

/-- if `procToVerifyStmt` succeeds, then the input procedure has `.structured` body -/
theorem procToVerifyStmt_is_structured
    (h : (procToVerifyStmt proc).run st = (Except.ok verifyStmt, st')) :
      ∃ ss, proc.body = .structured ss := by
    simp [ExceptT.run, procToVerifyStmt] at h
    cases hb: proc.body with
    | structured ss => simp
    | cfg blk =>
      simp [hb] at h
      cases h

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
    (h_wf_proc : WF.WFProcedureProp p proc) :
    ∃ (prefixStmts ss : List Statement),
      proc.body = .structured ss ∧
      verifyStmt = Stmt.block s!"verify_{proc.header.name.name}"
        (prefixStmts ++ [Stmt.block s!"body_{proc.header.name.name}" ss #[]] ++
          ensuresToAsserts proc.spec.postconditions) #[] ∧
      (∀ s ∈ prefixStmts, ∃ c, s = Stmt.cmd c) ∧
      (∀ params ρ₀, Core.Specification.ProcEnvWF params proc ρ₀ →
        ∃ ρ_init,
          Imperative.StepStmtStar Expression (EvalCommand π)
            (.stmts prefixStmts ρ_init) (.terminal ρ₀)) := by
  obtain ⟨ss, h_body_eq⟩ := procToVerifyStmt_is_structured h
  unfold procToVerifyStmt at h
  rw [h_body_eq] at h
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
      (.det (LExpr.fvar () id none)) #[]
  let assumes := requiresToAssumes proc.spec.preconditions
  let prefixStmts := inputInits ++ outputOnlyInits ++ oldInoutInits ++ assumes
  rw [h_body_eq]
  refine ⟨prefixStmts, ss, rfl, h_eq.symm, ?_, ?_⟩
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
  · intro _ ρ₀ h_wf
    -- Derive the typed-store witnesses directly from `ProcEnvWF`.
    have h_in_typed : ∀ id ty', (id, ty') ∈ proc.header.inputs.toList →
        ∃ v, ρ₀.store id = some v ∧
          HasVal.valueOfTy ρ₀.factory v (Lambda.LTy.forAll [] ty') :=
      fun id ty' hmem => h_wf.inputTyped hmem
    have h_out_typed : ∀ id ty', (id, ty') ∈ proc.header.getOutputOnlyParams.toList →
        ∃ v, ρ₀.store id = some v ∧
          HasVal.valueOfTy ρ₀.factory v (Lambda.LTy.forAll [] ty') :=
      fun id ty' hmem =>
        h_wf.outputTyped (getOutputOnlyParams_subset_outputs proc.header _ hmem)
    have h_oldinout_typed : ∀ id ty', (id, ty') ∈ proc.header.getInoutParams.toList →
        ∃ v, ρ₀.store (CoreIdent.mkOld id.name) = some v ∧
          HasVal.valueOfTy ρ₀.factory v (Lambda.LTy.forAll [] ty') :=
      fun id ty' hmem => h_wf.oldInoutTyped hmem
    refine ⟨prefixInitEnv _ ρ₀, prefixInitEnv_steps _ ρ₀ π h_wf.noFailure ?_⟩
    -- Split: (inputInits ++ outputOnlyInits ++ oldInoutInits) ++ assumes
    rw [show prefixStmts = (inputInits ++ outputOnlyInits ++ oldInoutInits) ++ assumes
        from by simp [prefixStmts, List.append_assoc]]
    rw [PrefixStepsOK_append]
    have h_assumes_id : prefixInitEnv assumes ρ₀ = ρ₀ := by
      apply prefixInitEnv_noninit_list
      intro s hs
      simp only [assumes, requiresToAssumes, List.mem_map] at hs
      obtain ⟨⟨l, c⟩, _, rfl⟩ := hs; simp [stmtInitVar]
    refine ⟨PrefixStepsOK_assumes π proc.spec.preconditions ρ₀
      h_wf.preconditionsHold h_wf.bool, ?_⟩
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
      apply PrefixStepsOK_det_init_map π _ _ h_wf.storeValues h_wf.var
      · -- inout params are defined in store (they are inputs)
        intro id hid
        obtain ⟨⟨id', ty'⟩, hmem, rfl⟩ := List.mem_map.mp hid
        obtain ⟨v, hv, _⟩ :=
          h_in_typed id' ty' (getInoutParams_subset_inputs proc.header _ hmem)
        rw [hv]; rfl
      · -- mkOld of inout params hold typed old snapshots
        exact h_oldinout_typed
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
      have h_wfVar_old : WellFormedSemanticEvalVar (P := Expression) ρ₀.factory := h_wf.var
      rw [PrefixStepsOK_append]
      constructor
      · -- outputOnlyInits at prefixInitEnv oldInoutInits ρ₀
        apply PrefixStepsOK_nondet_init_map π _ _
        · simp only [prefixInitEnv_factory]; exact h_wfVar_old
        · intro id ty' hmem
          obtain ⟨v, hv, hvty⟩ := h_out_typed id ty' hmem
          have hid_keys : id ∈ ListMap.keys proc.header.getOutputOnlyParams := by
            rw [ListMap.keys_eq_map_fst]
            exact List.mem_map_of_mem (f := Prod.fst) hmem
          have h_in_outputs := getOutputOnlyParams_keys_subset_outputs proc.header id hid_keys
          refine ⟨v, ?_, ?_⟩
          · rw [prefixInitEnv_store_not_init]
            · exact hv
            · exact h_io_not_in_old id (List.mem_append_right _ h_in_outputs)
          · simp only [prefixInitEnv_factory]; exact hvty
        · rw [← ListMap.keys_eq_map_fst]
          exact getOutputOnlyParams_nodup proc.header h_wf_proc.outputsNodup
      · -- inputInits at prefixInitEnv outputOnlyInits (prefixInitEnv oldInoutInits ρ₀)
        have h_wfVar_out' : WellFormedSemanticEvalVar (P := Expression) ρ₀.factory := h_wf.var
        apply PrefixStepsOK_nondet_init_map π _ _
        · simp only [prefixInitEnv_factory]; exact h_wfVar_out'
        · intro id ty' hmem_in
          obtain ⟨v, hv, hvty⟩ := h_in_typed id ty' hmem_in
          have hid_keys : id ∈ ListMap.keys proc.header.inputs := by
            rw [ListMap.keys_eq_map_fst]
            exact List.mem_map_of_mem (f := Prod.fst) hmem_in
          refine ⟨v, ?_, ?_⟩
          · rw [prefixInitEnv_store_not_init]
            · rw [prefixInitEnv_store_not_init]
              · exact hv
              · exact h_io_not_in_old id (List.mem_append_left _ hid_keys)
            · -- input id not init'd in outputOnlyInits: by construction,
              -- getOutputOnlyParams only contains ids NOT in inputs
              intro s hs heq_s
              simp only [outputOnlyInits, List.mem_map] at hs
              obtain ⟨⟨oid, oty⟩, hmem2, rfl⟩ := hs
              simp [stmtInitVar] at heq_s
              have h_oid_keys : oid ∈ ListMap.keys proc.header.getOutputOnlyParams := by
                rw [ListMap.keys_eq_map_fst]
                simp only [ListMap.toList] at hmem2
                exact List.mem_map_of_mem (f := Prod.fst) hmem2
              have h_oid_not_in_inputs := getOutputOnlyParams_keys_disjoint_inputs proc.header oid h_oid_keys
              exact h_oid_not_in_inputs (heq_s ▸ hid_keys)
          · simp only [prefixInitEnv_factory]; exact hvty
        · rw [← ListMap.keys_eq_map_fst]; exact h_wf_proc.inputsNodup

/-! ## Correctness on event traces -/

/-- Running the postcondition asserts emits the non-free postconditions as
    assertion events observed in the current environment. -/
private theorem ensuresToAsserts_runE
    (π : String → Option Procedure)
    (ρ : Env Expression) :
    ∀ (cs : ListMap CoreLabel Procedure.Check),
      CoreStepStarE π (.stmts (ensuresToAsserts cs) ρ)
        (defaultAssertEvents ρ.factory ρ.store cs) (.stmts [] ρ)
  | [] => by
    simp only [ensuresToAsserts, defaultAssertEvents, Imperative.Calls.defaultAssertEvents,
      ListMap.toList, List.filterMap_nil]
    exact .refl _
  | (label, check) :: rest => by
    have ih := ensuresToAsserts_runE π ρ rest
    cases hattr : check.attr with
    | Free =>
      simpa [ensuresToAsserts, defaultAssertEvents, Imperative.Calls.defaultAssertEvents,
        ListMap.toList, hattr] using ih
    | Default =>
      have hassert : CoreStepStarE π (.stmt (Statement.assert label check.expr check.md) ρ)
          [Event.assert ⟨ρ.factory, ρ.store, label, check.expr, check.md⟩] (.terminal ρ) := by
        have hstep : CoreStepE π (.stmt (.cmd (.cmd (.assert label check.expr check.md))) ρ)
            [Event.assert ⟨ρ.factory, ρ.store, label, check.expr, check.md⟩]
            (.terminal { ρ with store := ρ.store }) :=
          .step_cmd (.cmd_sem .eval_assert)
        simpa using ReflTransTrace.step _ _ _ _ _ hstep (ReflTransTrace.refl _)
      have := ReflTransTrace.trans _
        (Imperative.stmts_cons_stepE _ _ _ ρ ρ hassert) ih
      simpa [ensuresToAsserts, defaultAssertEvents, Imperative.Calls.defaultAssertEvents,
        ListMap.toList, hattr] using this

/-- An administrative event step as a one-step run. -/
private theorem adminRunE
    {π : String → Option Procedure}
    {c c' : CoreConfig}
    (h : StepStmt Expression (noCommandEvalE Expression Command) c c') :
    CoreStepStarE π c [] c' := by
  simpa using ReflTransTrace.step _ _ _ _ _ (StepStmtE.step_admin h) (ReflTransTrace.refl _)

/-- If every event trace of the verification statement produced by
    `procToVerifyStmt` is assertion-valid under `I`, then the procedure is
    correct on event traces under `I`.

    The verification statement reaches the body through initializations and
    the assumed preconditions. A run only passes an assumption that the
    evaluator makes true, so `h_assume` asks that such an assumption hold in
    every world of `I`; this is what lets validity of the whole statement give
    validity of the body's runs.

    `h_assume` does not hold for `DenoteBasedInterp`: it covers conditions
    captured under any factory, and the denotation reads those outside
    `Core.Factory` through an arbitrary predicate of the world, so some world
    refutes them. An instance for the denotation needs entry environments whose
    factory is `Core.Factory`, and the hypothesis stated only for the typed
    preconditions the verification statement assumes. -/
theorem procBodyVerify_procedureCorrectOnTraces
    (I : ConditionInterp Expression)
    (h_assume : ∀ c : EventArg Expression,
      Expression.eval c.factory c.store c.expr = some HasBool.tt → ∀ world, I.holds world c)
    (procName : String) (proc : Procedure) (p : Program)
    (st : CoreTransformState) (verifyStmt : Statement) (st' : CoreTransformState)
    (h_lookup : p.findProcByString? procName = some proc)
    (h_transform : (procToVerifyStmt proc).run st = (Except.ok verifyStmt, st'))
    (h_correct : Specification.AllAssertsValidOnTraces
      (Core.Logic.EventLang.core p.findProcByString?) I verifyStmt)
    (h_wf_proc : WF.WFProcedureProp p proc) (params : Core.Logic.InitEnvWFParams) :
    Core.Specification.ProcedureAssertsValidOnTraces I params procName p := by
  let π : String → Option Procedure := p.findProcByString?
  obtain ⟨prefixStmts, ss, h_body, h_eq, _, h_prefix_trace⟩ :=
    procToVerifyStmt_structure proc p st st' verifyStmt h_transform π h_wf_proc
  let vL := s!"verify_{proc.header.name.name}"
  let bL := s!"body_{proc.header.name.name}"
  let posts := ensuresToAsserts proc.spec.postconditions
  -- The verification statement reaches the start of the body, and every
  -- assumption it emits on the way holds.
  have h_start : ∀ ρ₀, Specification.ProcEnvWF params proc ρ₀ → ∃ (ρ_i : Env Expression) (tP : Trace Expression),
      CoreStepStarE π (.stmt verifyStmt ρ_i) tP
        (.block (.some vL) ρ_i.store
          (.seq (.block (.some bL) ρ₀.store (.stmts ss ρ₀)) posts)) ∧
      ∀ c, Event.assume c ∈ tP → ∀ world, I.holds world c := by
    intro ρ₀ hwf
    obtain ⟨ρ_init, h_prefix⟩ := h_prefix_trace _ ρ₀ hwf
    have hleg : StepStmtStar Expression (EvalCommand π)
        (.stmt verifyStmt ρ_init)
        (.block (.some vL) ρ_init.store
          (.seq (.block (.some bL) ρ₀.store (.stmts ss ρ₀)) posts)) := by
      rw [h_eq]
      exact ReflTrans_Transitive _ _ _ _
        (step_block_enter Expression (EvalCommand π) vL _ #[] ρ_init)
        (block_inner_star Expression (EvalCommand π) _ _ (.some vL)
          ρ_init.store
          (ReflTrans_Transitive _ _ _ _
            (by rw [List.append_assoc]
                exact stmts_prefix_terminal_append Expression (EvalCommand π)
                  prefixStmts _ ρ_init ρ₀ h_prefix)
            (ReflTrans_Transitive _ _ _ _
              (.step _ _ _ .step_stmts_cons (.refl _))
              (seq_inner_star Expression (EvalCommand π) _ _ posts
                (step_block_enter Expression (EvalCommand π) bL _ #[] ρ₀)))))
    obtain ⟨tP, hrun, hf⟩ := Core.Specification.coreStepStar_toEvent
      (StepStmtStar_to_CoreStepStar hleg) Bool.false
    have hρ₀ : ({ ρ₀ with hasFailure := Bool.false } : Env Expression) = ρ₀ := by
      have := hwf.noFailure; cases ρ₀; simp_all
    refine ⟨{ ρ_init with hasFailure := Bool.false }, tP, ?_, fun c hc => h_assume c (hf.assumes c hc)⟩
    simpa [Config.withFailure, hρ₀] using hrun
  -- A run of the body wrapped in its block is a run of the body itself.
  have h_inner : ∀ (ρ₀ : Env Expression) tr cfg,
      CoreStepStarE π (.stmt (Stmt.block "" ss #[]) ρ₀) tr cfg →
      tr = [] ∨ ∃ inner', CoreStepStarE π (.stmts ss ρ₀) tr inner' := by
    intro ρ₀ tr cfg h
    cases h with
    | refl => exact .inl rfl
    | step _ _ _ _ _ hstep hrest =>
      cases hstep with
      | step_admin hadmin =>
        cases hadmin
        simp only [List.nil_append]
        rcases Imperative.block_run_to_finalE hrest with
          ⟨_, _, hi⟩ | ⟨_, hi, _⟩ | ⟨_, _, _, hi, _⟩ | ⟨_, _, _, hi, _⟩
        all_goals exact .inr ⟨_, hi⟩
  refine
    { procedureExists := ⟨proc, h_lookup⟩
      assertsValid := ?_
      contract := ?_ }
  · ----- Part 1: every assertion a run of the body reaches is valid -----
    intro a
    refine ⟨proc, ss, h_lookup, h_body, ?_⟩
    intro ρ₀ cfg tr hpre hrun
    obtain ⟨hwf, _⟩ := hpre
    rcases h_inner ρ₀ tr cfg hrun with rfl | ⟨_, hi⟩
    · simp [Trace.AssertionValid, Trace.AssertionValidFrom, Trace.AssertionsValidFromP]
    · obtain ⟨ρ_i, tP, hs, hheld⟩ := h_start ρ₀ hwf
      have hfull := ReflTransTrace.trans _ hs
        (Imperative.block_inner_starE (Imperative.seq_inner_starE _
          (Imperative.block_inner_starE hi)))
      have hv := h_correct ρ_i _ _ trivial hfull
      exact Trace.AssertionsValidFromP.mono_keep _ (fun _ _ => trivial)
        (Trace.AssertionsValid.suffix _ tP tr hheld hv)
  · ----- Part 2: the body meets the contract -----
    intro proc' ss' hfind hb' ρ₀ ρ' tr hpre hrun
    obtain ⟨hwf, _⟩ := hpre
    have hproc : proc' = proc := Option.some.inj (hfind.symm.trans h_lookup)
    subst hproc
    have hss : ss' = ss := Imperative.Body.structured.inj (hb'.symm.trans h_body)
    subst hss
    -- A run of the one-element list `[block]` is a run of the block itself.
    have hstmt : CoreStepStarE π (.stmt (Stmt.block "" ss' #[]) ρ₀) tr (.terminal ρ') ∨
        ∃ lbl, CoreStepStarE π (.stmt (Stmt.block "" ss' #[]) ρ₀) tr (.exiting lbl ρ') := by
      rcases hrun with h | ⟨lbl, h⟩
      · rcases Imperative.stmts_cons_headE _ h with ⟨hc, _⟩ | h
        · cases hc
        · obtain ⟨ρ₁, tr₁, tr₂, rfl, h1, h2⟩ := Imperative.seq_reaches_terminalE _ h
          obtain ⟨rfl, hc | hc⟩ := Imperative.stmts_nil_runE _ h2
          · cases hc
          · cases hc
            exact .inl (by simpa using h1)
      · rcases Imperative.stmts_cons_headE _ h with ⟨hc, _⟩ | h
        · cases hc
        · rcases Imperative.seq_reaches_exitingE _ h with h1 | ⟨ρ₁, tr₁, tr₂, rfl, _, h2⟩
          · exact .inr ⟨lbl, h1⟩
          · obtain ⟨_, hc | hc⟩ := Imperative.stmts_nil_runE _ h2 <;> cases hc
    obtain ⟨ρ_inner, hdone, hρ'⟩ := Imperative.stmt_block_reaches_doneE hstmt
    have hterm : CoreStepStarE π (.stmts ss' ρ₀) tr (.terminal ρ_inner) := by
      rcases hdone with h | ⟨lbl, h⟩
      · exact h
      · exact absurd h (Imperative.stmts_exitsCoveredByBlocks_noEscapeE _ ss'
          (h_wf_proc.bodyExitsCovered ss' hb') ρ₀ lbl ρ_inner)
    subst hρ'
    obtain ⟨ρ_i, tP, hs, hheld⟩ := h_start ρ₀ hwf
    have hfull := ReflTransTrace.trans _ hs
      (ReflTransTrace.trans _
        (Imperative.block_inner_starE (Imperative.seq_inner_starE _
          (Imperative.block_inner_starE hterm)))
        (ReflTransTrace.trans _
          (Imperative.block_inner_starE (Imperative.seq_inner_starE _
            (adminRunE .step_block_done)))
          (ReflTransTrace.trans _
            (Imperative.block_inner_starE (adminRunE .step_seq_done))
            (Imperative.block_inner_starE (ensuresToAsserts_runE π _
              proc'.spec.postconditions)))))
    simp only [List.nil_append] at hfull
    have hv := h_correct ρ_i _ _ trivial hfull
    exact Trace.AssertionsValid.suffix _ tP _ hheld hv

end ProcBodyVerifyCorrect
