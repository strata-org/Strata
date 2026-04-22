/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.ProcBodyVerify
public import Strata.Transform.CoreSpecification
public import Strata.Languages.Core.WF
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

/-! ## Input Environment Reconstruction, from the prefix statements of ProcBodyVerify -/

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

/-- PrefixStepsOK for modifies init pairs: [init oldG nondet, init g := fvar oldG]. -/
private theorem PrefixStepsOK_modifies_pair
    (π : String → Option Procedure) (φ : CoreEval → PureFunc Expression → CoreEval)
    (g : Expression.Ident) (oldG : Expression.Ident) (gTy : Expression.Ty)
    (ρ : Imperative.Env Expression)
    (h_wfVar : WellFormedSemanticEvalVar ρ.eval)
    (h_g_def : (ρ.store g).isSome)
    (h_old_def : (ρ.store oldG).isSome)
    (h_old_eq : ρ.store g = ρ.store oldG)
    (h_ne : g ≠ oldG)
    : PrefixStepsOK π φ
        [Statement.init oldG gTy .nondet #[],
         Statement.init g gTy (.det (Lambda.LExpr.fvar Strata.SourceRange.none oldG none)) #[]] ρ := by
  constructor
  · constructor
    · exact trivial  -- PrefixStepsOK for []
    · refine ⟨_, rfl, ρ.store, ?_, rfl⟩
      have h_none_g : (prefixInitEnv [Statement.init g gTy (.det (Lambda.LExpr.fvar Strata.SourceRange.none oldG none)) #[]] ρ).store g = none :=
        prefixInitEnv_store_init _ _ _ _ rfl
      have h_old_val : (prefixInitEnv [Statement.init g gTy (.det (Lambda.LExpr.fvar Strata.SourceRange.none oldG none)) #[]] ρ).store oldG = ρ.store oldG := by
        rw [prefixInitEnv_store_other _ _ _ oldG g rfl h_ne]
        simp [prefixInitEnv]
      rw [Option.isSome_iff_exists] at h_g_def
      obtain ⟨v, hv⟩ := h_g_def
      have h_getFvar : HasFvar.getFvar (Lambda.LExpr.fvar Strata.SourceRange.none oldG none : Expression.Expr) = some oldG := by
        simp [HasFvar.getFvar]
      have h_eval : ρ.eval (prefixInitEnv [Statement.init g gTy (.det (Lambda.LExpr.fvar Strata.SourceRange.none oldG none)) #[]] ρ).store (Lambda.LExpr.fvar Strata.SourceRange.none oldG none) = some v := by
        rw [h_wfVar _ _ _ h_getFvar, h_old_val, ← h_old_eq, hv]
      exact EvalCommand.cmd_sem (EvalCmd.eval_init h_eval
        (InitState.init h_none_g hv (fun y hne => by
          have := prefixInitEnv_store_other
            (Statement.init g gTy (.det (Lambda.LExpr.fvar Strata.SourceRange.none oldG none)) #[])
            [] ρ y g rfl hne
          simp [prefixInitEnv] at this
          exact this.symm))
        h_wfVar)
  · refine ⟨_, rfl, _, ?_, rfl⟩
    have h_none_old : (prefixInitEnv [Statement.init oldG gTy .nondet #[], Statement.init g gTy (.det (Lambda.LExpr.fvar Strata.SourceRange.none oldG none)) #[]] ρ).store oldG = none :=
      prefixInitEnv_store_init _ _ _ _ rfl
    have h_target : (prefixInitEnv [Statement.init g gTy (.det (Lambda.LExpr.fvar Strata.SourceRange.none oldG none)) #[]] ρ).store oldG = ρ.store oldG := by
      rw [prefixInitEnv_store_other _ _ _ oldG g rfl h_ne]
      simp [prefixInitEnv]
    rw [Option.isSome_iff_exists] at h_old_def
    obtain ⟨w, hw⟩ := h_old_def
    exact EvalCommand.cmd_sem (EvalCmd.eval_init_unconstrained
      (InitState.init h_none_old (by rw [h_target, hw]) (fun y hne => by
        exact (prefixInitEnv_store_other _ _ _ y oldG rfl hne).symm))
      h_wfVar)

/-- For any variable `x` that is NOT init'd by any statement in `stmts`,
    `prefixInitEnv stmts ρ` agrees with `ρ` on `x`. Generalization of
    `prefixInitEnv_store_not_init` to an arbitrary predicate on init vars. -/
private theorem prefixInitEnv_store_defined_of_not_init
    (stmts : List Statement) (ρ : Imperative.Env Expression) (x : Expression.Ident)
    (h_not_init : ∀ s ∈ stmts, stmtInitVar s ≠ some x)
    (h_def : (ρ.store x).isSome) :
    ((prefixInitEnv stmts ρ).store x).isSome := by
  rw [prefixInitEnv_store_not_init stmts ρ x h_not_init]
  exact h_def



/-- Characterize the sublists produced by the `modifies` mapM in `procToVerifyStmt`:
    each sublist corresponds to some `g ∈ gs` and has the shape
    `[init (mkOld g) gTy .nondet, init g gTy (.det (fvar oldG))]`. -/
private theorem modifiesMapM_sublists
    (gs : List Expression.Ident) (p : Program)
    (mInits : List (List Statement))
    (s0 s1 : CoreTransformState)
    (heq : (List.mapM (fun (g : Expression.Ident) => do
      let oldG := CoreIdent.mkOld g.name
      let gTy ← getIdentTy! p g
      return [Statement.init oldG gTy .nondet #[],
              Statement.init g gTy (.det (Lambda.LExpr.fvar Strata.SourceRange.none oldG none)) #[]])
      gs).run s0 = (Except.ok mInits, s1)) :
    ∀ sub ∈ mInits, ∃ g gTy, g ∈ gs ∧
      sub = [Statement.init (CoreIdent.mkOld g.name) gTy .nondet #[],
             Statement.init g gTy (.det (Lambda.LExpr.fvar Strata.SourceRange.none (CoreIdent.mkOld g.name) none)) #[]] := by
  induction gs generalizing s0 s1 mInits with
  | nil =>
    simp only [List.mapM_nil, pure, ExceptT.pure] at heq
    have := (Prod.mk.inj heq).1 |> Except.ok.inj; subst this
    intro _ h; simp at h
  | cons g rest ih =>
    simp only [List.mapM_cons, bind, ExceptT.bind, ExceptT.mk, ExceptT.run,
      ExceptT.bindCont, pure, ExceptT.pure, StateT.bind] at heq
    split at heq
    · rename_i res₁ st₁ heq₁
      cases res₁ with
      | ok gTy =>
        simp only [bind, StateT.bind, ExceptT.bindCont] at heq
        split at heq
        · rename_i rest_res st₂ heq₂
          cases rest_res with
          | ok restInits =>
            dsimp at heq
            have heq_mi := (Prod.mk.inj heq).1 |> Except.ok.inj
            subst heq_mi
            intro sub h_sub_mem
            cases h_sub_mem with
            | head =>
              split at heq₁
              · rename_i ty_res ty_st heq_ty
                cases ty_res with
                | ok actualTy =>
                  simp only [StateT.pure] at heq₁
                  have := (Prod.mk.inj heq₁).1 |> Except.ok.inj
                  subst this
                  exact ⟨g, actualTy, List.mem_cons_self, rfl⟩
                | error e =>
                  simp only [StateT.pure] at heq₁
                  exact absurd (Prod.mk.inj heq₁).1 (by intro h; cases h)
            | tail _ h_in_rest =>
              obtain ⟨g', gTy', hg', rfl⟩ := @ih restInits st₁ st₂ heq₂ sub h_in_rest
              exact ⟨g', gTy', List.mem_cons_of_mem _ hg', rfl⟩
          | error e =>
            simp only [pure, StateT.pure] at heq
            exact absurd (Prod.mk.inj heq).1 (by intro h; cases h)
      | error e =>
        dsimp at heq; exact absurd (Prod.mk.inj heq).1 (by intro h; cases h)

/-! ## Verification Statement Structure -/

/-- Structure: the output of `procToVerifyStmt` is a block
    `prefix ++ [bodyBlock] ++ postAsserts`, and all prefix statements
    are `.cmd` (init/assume commands).
    Additionally, for any `ProcEnvWF` state `ρ₀`, there exists an initial
    state `ρ_init` from which the prefix steps to `ρ₀`. -/
theorem procToVerifyStmt_structure
    (proc : Procedure) (p : Program) (st st' : CoreTransformState)
    (verifyStmt : Statement)
    (h : (procToVerifyStmt proc p).run st = (Except.ok verifyStmt, st'))
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
  split at h
  · rename_i a st_mid heq
    cases a with
    | ok modifiesInits =>
      dsimp at h
      refine ⟨_, ((Prod.mk.inj h).1 |> Except.ok.inj).symm, ?_, ?_⟩
      · intro s hs
        simp only [List.mem_append] at hs
        rcases hs with ((hs | hs) | hs) | hs
        · -- inputInits: each is Statement.init
          simp only [List.mem_map] at hs
          obtain ⟨⟨id, ty⟩, _, rfl⟩ := hs
          exact ⟨_, rfl⟩
        · -- outputInits: each is Statement.init
          simp only [List.mem_map] at hs
          obtain ⟨⟨id, ty⟩, _, rfl⟩ := hs
          exact ⟨_, rfl⟩
        · -- modifiesInits.flatten: each is Statement.init
          rw [List.mem_flatten] at hs
          obtain ⟨sublist, h_sub_mem, h_s_mem⟩ := hs
          have h_form : ∀ sub ∈ modifiesInits, ∀ s' ∈ sub, ∃ c, s' = Stmt.cmd c := by
            intro sub hsub s' hs'
            obtain ⟨g, gTy, _, rfl⟩ := modifiesMapM_sublists _ _ _ _ _ heq sub hsub
            simp only [List.mem_cons, List.mem_nil_iff, or_false] at hs'
            rcases hs' with rfl | rfl <;> exact ⟨_, rfl⟩
          exact h_form sublist h_sub_mem s h_s_mem
        · -- assumes: each is Statement.assume = Stmt.cmd
          simp only [requiresToAssumes, List.mem_map] at hs
          obtain ⟨⟨label, check⟩, _, rfl⟩ := hs
          exact ⟨_, rfl⟩
      · intro ρ₀ h_wf
        refine ⟨prefixInitEnv _ ρ₀, prefixInitEnv_steps _ ρ₀ π φ h_wf.noFailure ?_⟩

        rw [show List.map (fun x => Statement.init x.1 (Lambda.LTy.forAll [] x.2) .nondet #[])
              proc.header.inputs.toList ++
            List.map (fun x => Statement.init x.1 (Lambda.LTy.forAll [] x.2) .nondet #[])
              proc.header.outputs.toList ++
            modifiesInits.flatten ++
            requiresToAssumes proc.spec.preconditions =
            (List.map (fun x => Statement.init x.1 (Lambda.LTy.forAll [] x.2) .nondet #[])
              proc.header.inputs.toList ++
            List.map (fun x => Statement.init x.1 (Lambda.LTy.forAll [] x.2) .nondet #[])
              proc.header.outputs.toList ++
            modifiesInits.flatten) ++
            requiresToAssumes proc.spec.preconditions from by simp [List.append_assoc]]
        rw [PrefixStepsOK_append]
        have h_assumes_id : prefixInitEnv (requiresToAssumes proc.spec.preconditions) ρ₀ = ρ₀ := by
          apply prefixInitEnv_noninit_list
          intro s hs
          simp only [requiresToAssumes, List.mem_map] at hs
          obtain ⟨⟨l, c⟩, _, rfl⟩ := hs
          simp [stmtInitVar]
        refine ⟨PrefixStepsOK_assumes π φ proc.spec.preconditions ρ₀
          h_wf.preconditionsHold h_wf.wfBool, ?_⟩
        rw [h_assumes_id]

        have h_modifies_init_vars : ∀ s ∈ modifiesInits.flatten,
            ∀ x, stmtInitVar s = some x →
            x ∈ proc.spec.modifies ∨
            x ∈ proc.spec.modifies.map (fun g => CoreIdent.mkOld g.name) := by
          intro s hs x hx
          rw [List.mem_flatten] at hs
          obtain ⟨sub, hsub, hs'⟩ := hs
          obtain ⟨g, gTy, hg, rfl⟩ := modifiesMapM_sublists _ _ _ _ _ heq sub hsub
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hs'
          rcases hs' with rfl | rfl
          · simp [stmtInitVar] at hx; subst hx
            right; exact List.mem_map_of_mem (f := fun (g' : Expression.Ident) => CoreIdent.mkOld g'.name) hg
          · simp [stmtInitVar] at hx; subst hx; left; exact hg

        rw [show List.map (fun x => Statement.init x.1 (Lambda.LTy.forAll [] x.2) .nondet #[])
              proc.header.inputs.toList ++
            List.map (fun x => Statement.init x.1 (Lambda.LTy.forAll [] x.2) .nondet #[])
              proc.header.outputs.toList ++
            modifiesInits.flatten =
            (List.map (fun x => Statement.init x.1 (Lambda.LTy.forAll [] x.2) .nondet #[])
              proc.header.inputs.toList ++
            List.map (fun x => Statement.init x.1 (Lambda.LTy.forAll [] x.2) .nondet #[])
              proc.header.outputs.toList) ++
            modifiesInits.flatten from by simp [List.append_assoc]]
        rw [PrefixStepsOK_append]

        -- Helper: input/output vars are not init'd in modifiesInits.flatten
        have h_io_not_in_modifies : ∀ x ∈ ListMap.keys proc.header.inputs ++ ListMap.keys proc.header.outputs,
            ∀ s ∈ modifiesInits.flatten, stmtInitVar s ≠ some x := by
          intro x hx s hs hsx
          have hmod := h_modifies_init_vars s hs x hsx
          rcases hmod with hmod | hmod
          · -- x ∈ modifies, x ∈ keys inputs ++ keys outputs: contradicts ioModDisjoint
            exact absurd hmod (h_wf_proc.ioModDisjoint hx)
          · -- x ∈ map mkOld modifies, x ∈ keys inputs ++ keys outputs: contradicts modOldDisjoint
            have hx' : x ∈ (ListMap.keys proc.header.inputs ++ ListMap.keys proc.header.outputs) ++ proc.spec.modifies :=
              List.mem_append_left _ hx
            exact absurd hmod (h_wf_proc.modOldDisjoint hx')

        constructor
        · -- PrefixStepsOK for modifiesInits.flatten ρ₀
          -- Joint induction proving PrefixStepsOK and init-var info
          suffices h_joint :
              ∀ (gs : List Expression.Ident)
                (mInits : List (List Statement))
                (s0 s1 : CoreTransformState),
                (List.mapM (fun (g : Expression.Ident) => do
                  let oldG := CoreIdent.mkOld g.name
                  let gTy ← getIdentTy! p g
                  return [Statement.init oldG gTy .nondet #[],
                          Statement.init g gTy (.det (LExpr.fvar Strata.SourceRange.none oldG none)) #[]])
                  gs).run s0 = (Except.ok mInits, s1) →
                (∀ g ∈ gs, g ∈ proc.spec.modifies) →
                gs.Nodup →
                PrefixStepsOK π φ mInits.flatten ρ₀ ∧
                (∀ s ∈ mInits.flatten, ∀ x, stmtInitVar s = some x →
                  x ∈ gs ∨ x ∈ gs.map (fun (g : Expression.Ident) => CoreIdent.mkOld g.name)) by
            have h_mod_nd : proc.spec.modifies.Nodup := h_wf_proc.modNodup
            exact (h_joint _ _ _ _ heq (fun g hg => hg) h_mod_nd).1
          intro gs
          induction gs with
          | nil =>
            intro mInits s0 s1 heq_gs _ _
            simp only [List.mapM_nil, pure, ExceptT.pure, ExceptT.run] at heq_gs
            have := (Prod.mk.inj heq_gs).1 |> Except.ok.inj; subst this
            exact ⟨trivial, fun _ h => by simp at h⟩
          | cons g rest ih =>
            intro mInits s0 s1 heq_gs h_sub_gs h_nd_gs
            simp only [List.mapM_cons, bind, ExceptT.bind, ExceptT.mk, ExceptT.run,
              ExceptT.bindCont, pure, ExceptT.pure, StateT.bind] at heq_gs
            split at heq_gs
            · rename_i res₁ s₁ heq₁
              cases res₁ with
              | ok gTy =>
                simp only [bind, StateT.bind, ExceptT.bindCont] at heq_gs
                split at heq_gs
                · rename_i rest_res s₂ heq₂
                  cases rest_res with
                  | ok restInits =>
                    dsimp at heq_gs
                    have heq_mi := (Prod.mk.inj heq_gs).1 |> Except.ok.inj
                    subst heq_mi
                    -- Get pair shape
                    split at heq₁
                    · rename_i ty_res ty_st heq_ty
                      cases ty_res with
                      | ok actualTy =>
                        simp only [StateT.pure] at heq₁
                        have h_pair := (Prod.mk.inj heq₁).1 |> Except.ok.inj
                        subst h_pair
                        -- Apply IH for rest
                        have h_ih := ih restInits s₁ s₂ heq₂
                          (fun g' hg' => h_sub_gs g' (List.mem_cons_of_mem g hg'))
                          (List.nodup_cons.mp h_nd_gs).2
                        -- Nodup facts
                        have h_g_not_rest : g ∉ rest := (List.nodup_cons.mp h_nd_gs).1
                        -- Helper: g ∈ modifies
                        have h_g_mod : g ∈ proc.spec.modifies := h_sub_gs g List.mem_cons_self
                        -- Helper: rest.map mkOld ⊆ proc.spec.modifies.map mkOld
                        have h_rest_map_sub : ∀ x ∈ rest.map (fun (g : Expression.Ident) => CoreIdent.mkOld g.name),
                            x ∈ proc.spec.modifies.map (fun (g : Expression.Ident) => CoreIdent.mkOld g.name) :=
                          fun x hx => by
                            simp only [List.mem_map] at hx ⊢
                            obtain ⟨g', hg'_mem, rfl⟩ := hx
                            exact ⟨g', h_sub_gs g' (List.mem_cons_of_mem _ hg'_mem), rfl⟩
                        -- g not init'd in restInits.flatten
                        have h_g_not_in_rest_inits : ∀ s ∈ restInits.flatten, stmtInitVar s ≠ some g := by
                          intro s' hs' heq_s
                          rcases h_ih.2 s' hs' g heq_s with hg | hg
                          · exact h_g_not_rest hg
                          · -- g ∈ rest.map mkOld ⊆ map mkOld modifies, but g ∈ modifies too: contradicts modOldDisjoint
                            have hg_in_old : g ∈ proc.spec.modifies.map (fun (g : Expression.Ident) => CoreIdent.mkOld g.name) :=
                              h_rest_map_sub g hg
                            have hg_io_mod : g ∈ (ListMap.keys proc.header.inputs ++ ListMap.keys proc.header.outputs) ++ proc.spec.modifies :=
                              List.mem_append_right _ h_g_mod
                            exact absurd hg_in_old (h_wf_proc.modOldDisjoint hg_io_mod)
                        have h_oldG_not_in_rest_inits : ∀ s ∈ restInits.flatten, stmtInitVar s ≠ some (CoreIdent.mkOld g.name) := by
                          intro s' hs' heq_s
                          rcases h_ih.2 s' hs' (CoreIdent.mkOld g.name) heq_s with hg | hg
                          · have h_mkOld_in_mod : CoreIdent.mkOld g.name ∈ proc.spec.modifies :=
                              h_sub_gs _ (List.mem_cons_of_mem _ hg)
                            have h_g_in_io_mod : g ∈ (ListMap.keys proc.header.inputs ++ ListMap.keys proc.header.outputs) ++ proc.spec.modifies :=
                              List.mem_append_right _ h_g_mod
                            have h_mkOld_in_map_mod : CoreIdent.mkOld g.name ∈ proc.spec.modifies.map (fun g' => CoreIdent.mkOld g'.name) :=
                              List.mem_map.mpr ⟨g, h_g_mod, rfl⟩
                            have h_io_mod_app : CoreIdent.mkOld g.name ∈ (ListMap.keys proc.header.inputs ++ ListMap.keys proc.header.outputs) ++ proc.spec.modifies :=
                              List.mem_append_right _ h_mkOld_in_mod
                            exact absurd h_mkOld_in_map_mod (h_wf_proc.modOldDisjoint h_io_mod_app)
                          · have h_nd_mkold : (proc.spec.modifies.map (fun (g' : Expression.Ident) => CoreIdent.mkOld g'.name)).Nodup :=
                              h_wf_proc.modOldNodup
                            simp only [List.mem_map] at hg
                            obtain ⟨g', hg'_mem, hg'_eq⟩ := hg
                            have : g = g' := List.nodup_map_injOn h_nd_mkold
                              (h_sub_gs g List.mem_cons_self)
                              (h_sub_gs g' (List.mem_cons_of_mem _ hg'_mem))
                              hg'_eq.symm
                            exact h_g_not_rest (this ▸ hg'_mem)
                        have h_g_store : (prefixInitEnv restInits.flatten ρ₀).store g = ρ₀.store g :=
                          prefixInitEnv_store_not_init _ _ _ h_g_not_in_rest_inits
                        have h_oldG_store : (prefixInitEnv restInits.flatten ρ₀).store (CoreIdent.mkOld g.name) = ρ₀.store (CoreIdent.mkOld g.name) :=
                          prefixInitEnv_store_not_init _ _ _ h_oldG_not_in_rest_inits
                        have h_g_in_vi : g ∈ Specification.procVerifyInitIdents proc := by
                          unfold Specification.procVerifyInitIdents
                          simp only [List.mem_append]; right; exact h_g_mod
                        have h_wfVar' : WellFormedSemanticEvalVar (prefixInitEnv restInits.flatten ρ₀).eval := by
                          rw [prefixInitEnv_eval]; exact h_wf.wfVar
                        have h_pair_ok := PrefixStepsOK_modifies_pair π φ g (CoreIdent.mkOld g.name) actualTy
                          (prefixInitEnv restInits.flatten ρ₀)
                          h_wfVar'
                          (by rw [h_g_store]; exact h_wf.storeDefined g h_g_in_vi)
                          (by rw [h_oldG_store]
                              have : (ρ₀.store (CoreIdent.mkOld g.name)).isSome := by
                                rw [← h_wf.oldModifiesMatchesCurrent g h_g_mod]; exact h_wf.storeDefined g h_g_in_vi
                              exact this)
                          (by rw [h_g_store, h_oldG_store]; exact h_wf.oldModifiesMatchesCurrent g h_g_mod)
                          (@CoreIdent.ne_mkOld g)
                        simp only [List.flatten_cons]
                        rw [PrefixStepsOK_append]
                        refine ⟨⟨h_ih.1, h_pair_ok⟩, ?_⟩
                        intro s' hs' x hx
                        simp only [List.mem_append] at hs'
                        rcases hs' with hs' | hs'
                        · -- s' in the pair
                          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hs'
                          rcases hs' with rfl | rfl
                          · simp [stmtInitVar] at hx; subst hx
                            right; exact List.mem_cons_self
                          · simp [stmtInitVar] at hx; subst hx
                            left; exact List.mem_cons_self
                        · -- s' in restInits.flatten
                          rcases h_ih.2 s' hs' x hx with h | h
                          · left; exact List.mem_cons_of_mem _ h
                          · right; simp only [List.map_cons]; exact List.mem_cons_of_mem _ h
                      | error e =>
                        simp only [StateT.pure] at heq₁
                        exact absurd (Prod.mk.inj heq₁).1 (by intro h; cases h)
                  | error e =>
                    simp only [pure, StateT.pure] at heq_gs
                    exact absurd (Prod.mk.inj heq_gs).1 (by intro h; cases h)
              | error e =>
                dsimp at heq_gs; exact absurd (Prod.mk.inj heq_gs).1 (by intro h; cases h)
        · -- PrefixStepsOK for inputInits ++ outputInits at prefixInitEnv modifiesInits.flatten ρ₀
          have h_modenv := prefixInitEnv_eval modifiesInits.flatten ρ₀
          have h_wfVar_mod : WellFormedSemanticEvalVar (prefixInitEnv modifiesInits.flatten ρ₀).eval := by
            rw [h_modenv]; exact h_wf.wfVar
          -- Split into inputs and outputs
          rw [PrefixStepsOK_append]
          constructor
          · -- outputInits at prefixInitEnv modifiesInits.flatten ρ₀
            apply PrefixStepsOK_nondet_init_map π φ _ _ h_wfVar_mod
            · -- all output ids defined
              intro id hid
              rw [prefixInitEnv_store_not_init]
              · have hid_keys : id ∈ ListMap.keys proc.header.outputs := by
                  rw [ListMap.keys_eq_map_fst]; exact hid
                have hid_vi : id ∈ Specification.procVerifyInitIdents proc := by
                  unfold Specification.procVerifyInitIdents
                  simp only [List.mem_append]
                  left; right; exact hid_keys
                exact h_wf.storeDefined id hid_vi
              · intro s hs heq_s
                have hid_io : id ∈ ListMap.keys proc.header.inputs ++ ListMap.keys proc.header.outputs :=
                  List.mem_append_right _ (by rw [ListMap.keys_eq_map_fst]; exact hid)
                exact h_io_not_in_modifies id hid_io s hs heq_s
            · -- nodup of output ids
              rw [← ListMap.keys_eq_map_fst]; exact h_wf_proc.outputsNodup
          · -- inputInits at prefixInitEnv outputInits (prefixInitEnv modifiesInits.flatten ρ₀)
            have h_outenv := prefixInitEnv_eval
              (List.map (fun x => Statement.init x.1 (Lambda.LTy.forAll [] x.2) .nondet #[])
                proc.header.outputs.toList)
              (prefixInitEnv modifiesInits.flatten ρ₀)
            have h_wfVar_out : WellFormedSemanticEvalVar
                (prefixInitEnv
                  (List.map (fun x => Statement.init x.1 (Lambda.LTy.forAll [] x.2) .nondet #[])
                    proc.header.outputs.toList)
                  (prefixInitEnv modifiesInits.flatten ρ₀)).eval := by
              rw [h_outenv]; exact h_wfVar_mod
            apply PrefixStepsOK_nondet_init_map π φ _ _ h_wfVar_out
            · -- all input ids defined
              intro id hid
              rw [prefixInitEnv_store_not_init]
              · rw [prefixInitEnv_store_not_init]
                · have hid_keys : id ∈ ListMap.keys proc.header.inputs := by
                    rw [ListMap.keys_eq_map_fst]; exact hid
                  have hid_vi : id ∈ Specification.procVerifyInitIdents proc := by
                    unfold Specification.procVerifyInitIdents
                    simp only [List.mem_append]
                    left; left; exact hid_keys
                  exact h_wf.storeDefined id hid_vi
                · intro s hs heq_s
                  have hid_io : id ∈ ListMap.keys proc.header.inputs ++ ListMap.keys proc.header.outputs :=
                    List.mem_append_left _ (by rw [ListMap.keys_eq_map_fst]; exact hid)
                  exact h_io_not_in_modifies id hid_io s hs heq_s
              · -- input id not init'd in outputInits
                intro s hs heq_s
                simp only [List.mem_map] at hs
                obtain ⟨⟨oid, oty⟩, hmem, rfl⟩ := hs
                simp [stmtInitVar] at heq_s
                -- heq_s : oid = id
                have hid_in : id ∈ ListMap.keys proc.header.inputs := by
                  rw [ListMap.keys_eq_map_fst]; exact hid
                have oid_in : id ∈ ListMap.keys proc.header.outputs := by
                  rw [ListMap.keys_eq_map_fst]; exact heq_s ▸ List.mem_map_of_mem (f := Prod.fst) hmem
                exact absurd oid_in (h_wf_proc.ioDisjoint hid_in)
            · -- nodup of input ids
              rw [← ListMap.keys_eq_map_fst]; exact h_wf_proc.inputsNodup
    | error e => dsimp at h; exact absurd (Prod.mk.inj h).1 (by intro h; cases h)

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

private theorem Block_noFuncDecl_of_forall (xs : List Statement)
    (h : ∀ s ∈ xs, Stmt.noFuncDecl s = true) : Block.noFuncDecl xs = true := by
  induction xs with
  | nil => simp [Block.noFuncDecl]
  | cons hd tl ih =>
    simp only [Block.noFuncDecl, Bool.and_eq_true]
    exact ⟨h hd (.head _), ih (fun s hs => h s (.tail _ hs))⟩

private theorem ensuresToAsserts_noFuncDecl (pcs : ListMap CoreLabel Procedure.Check) :
    Block.noFuncDecl (ensuresToAsserts pcs) = true := by
  apply Block_noFuncDecl_of_forall
  intro s hs
  have ⟨l, e, md, heq⟩ := ensuresToAsserts_mem_is_assert hs
  subst heq; simp [Stmt.noFuncDecl]

/-! ## Main Theorem -/

/-- If all asserts are valid in the verification statement produced by
    `procToVerifyStmt` (for initial environments satisfying `ProcEnvWF`),
    then `ProcedureCorrect` holds for the procedure. -/
theorem procBodyVerify_procedureCorrect
    (π : String → Option Procedure) (φ : CoreEval → PureFunc Expression → CoreEval)
    (proc : Procedure) (p : Program) (st : CoreTransformState)
    (verifyStmt : Statement) (st' : CoreTransformState)
    -- `h_transform`: procToVerifyStmt returned successfully.
    (h_transform : (procToVerifyStmt proc p).run st = (Except.ok verifyStmt, st'))
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
    -- postAsserts noFuncDecl
    have h_nofd_post : Block.noFuncDecl postAsserts = true :=
      ensuresToAsserts_noFuncDecl proc.spec.postconditions
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
