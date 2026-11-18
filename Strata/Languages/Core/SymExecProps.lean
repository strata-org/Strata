/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.SymExec
public import Strata.DL.Lambda.Denote.LExprSemanticsConsistent
public import Strata.DL.Lambda.Denote.Assumptions
public import Strata.DL.Imperative.InterpreterCFG
import all Strata.DL.Imperative.InterpreterCFG
import all Strata.DL.Lambda.Denote.LExprSemanticsConsistent
import all Strata.DL.Lambda.Denote.Assumptions
import all Strata.DL.Imperative.Interpreter

/-! # Properties of `Core.SymExec`

* `choosePrefix_fresh`: symbols never collide with the procedure's own names.
* `symEval_denote`: `symEval`'s result has the type and denotation of its input.
* `symEval_agrees_concrete`: `symEval` and the concrete evaluator agree up to denotation.
* `forkBranch_outcomes`: every outcome of `branch` extends the path condition by `g` or its
  negation, or keeps it when it decides `g`; at most two outcomes.
* `forkBranch_fork`: an undecided guard gives exactly the two branches.
* `forkBranch_model`: a model that satisfies the path condition agrees with some outcome of the
  fork, and every outcome it agrees with is the branch its guard takes under that model.
* `proj_stepInterp`: a `ForkM` step filtered by a model is a step of the deterministic run.
* `proj_stepInterpCFG`: the same for a step of a CFG.
-/

namespace Core.SymExec

open Imperative Lambda

public section

/-! ## Symbol prefixes -/

/-- A string starts only with prefixes no longer than itself. -/
private theorem length_le_of_startsWith {s p : String} (h : s.startsWith p = true) :
    p.length ≤ s.length := by
  rw [String.startsWith_string_iff] at h
  have := h.length_le
  simpa [String.length] using this

/-- The fold computing the longest name never decreases its accumulator. -/
private theorem le_foldl_max (l : List String) (a : Nat) :
    a ≤ l.foldl (fun m n => max m n.length) a := by
  induction l generalizing a with
  | nil => simp
  | cons y ys ih => exact Nat.le_trans (Nat.le_max_left _ _) (ih _)

/-- The fold computing the longest name bounds every name's length. -/
private theorem length_le_foldl_max (l : List String) (acc : Nat) :
    ∀ n ∈ l, n.length ≤ l.foldl (fun m n => max m n.length) acc := by
  induction l generalizing acc with
  | nil => simp
  | cons x xs ih =>
    intro n hn
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hn with rfl | hn
    · exact Nat.le_trans (Nat.le_max_right _ _) (le_foldl_max _ _)
    · exact ih _ n hn

/-- `choosePrefix.go` returns a prefix no name of `names` starts with, once the fuel and the
    candidate's length together exceed every name's length. -/
private theorem choosePrefix_go_fresh (names : List String) (bound : Nat)
    (hb : ∀ n ∈ names, n.length ≤ bound) :
    ∀ (k : Nat) (p : String), bound < p.length + k →
      ∀ n ∈ names, n.startsWith (choosePrefix.go names k p) = false := by
  intro k
  induction k with
  | zero =>
    intro p hp n hn
    simp only [choosePrefix.go]
    cases h : n.startsWith p with
    | false => exact h
    | true => have := length_le_of_startsWith h; have := hb n hn; omega
  | succ k ih =>
    intro p hp n hn
    generalize hq : choosePrefix.go names (k + 1) p = q
    by_cases hany : (names.any fun x => x.startsWith p) = true
    · have e : q = choosePrefix.go names k (p ++ "_") := by
        rw [← hq]; simp only [choosePrefix.go, hany, ite_true]
      subst e
      exact ih _ (by
        have h1 : "_".length = 1 := by decide
        rw [String.length_append]; omega) n hn
    · have e : q = p := by
        rw [← hq]; simp [choosePrefix.go, hany]
      subst e
      simp only [List.any_eq_true, not_exists, not_and, Bool.not_eq_true] at hany
      exact hany n hn

/-- No name of `names` starts with `choosePrefix names`: symbols never collide with them. -/
theorem choosePrefix_fresh (names : List String) :
    ∀ n ∈ names, n.startsWith (choosePrefix names) = false := by
  unfold choosePrefix
  exact choosePrefix_go_fresh names _ (length_le_foldl_max names 0) _ _ (by omega)

/-! ## The symbolic evaluator -/

/-- `symEval`'s result is the first component of `LExpr.eval` at the simplification fuel. -/
private theorem symEval_eq_some {cfg : ExploreCfg} {F : Lambda.Factory CoreLParams}
    {σ : RStore Expression} {e t : Expression.Expr} (h : symEval cfg F σ e = some t) :
    t = (LExpr.eval cfg.simpFuel F σ e).fst := by
  unfold symEval at h
  split at h
  · exact (Option.some.inj h).symm
  · cases h

/-- The conditions of evaluator soundness (`Lambda.eval_denote_soundAt`) for evaluating `e` on
    the store `σ` under the factory `F`, at the valuations `fv`, `vt`: the store is well formed
    and its typing makes `F` well formed, `F` is well formed, every stored term denotes the value
    `fv` gives its name, and `e`'s operators and free variables are annotated consistently. -/
def EvalSoundHyps (tc : TyConstrInterp) (op : OpInterp tc) (fv : FreeVarVal CoreLParams tc)
    (vt : TyVarVal) (F : Lambda.Factory CoreLParams) (σ : RStore Expression)
    (e : Expression.Expr) : Prop :=
  ∃ hEnvWF : Env.StepWF F σ, Factory.StepWFOn F hEnvWF.typed.tyMap ∧
    (∃ tf : @TypeFactory CoreLParams.IDMeta, Factory.WF F tf) ∧
    Env.InterpConsistentAt tc op fv vt σ ∧ OpsConsistent F e ∧
    fvars_annotated_by hEnvWF.typed.tyMap e

/-- `LExpr.eval` preserves type and denotation when the store and factory are well formed for
    evaluation, the valuation agrees with the stored terms, and `e`'s operators and free
    variables are consistently annotated (`EvalSoundHyps`). -/
private theorem eval_denote_of_hyps {tc : TyConstrInterp} {op : OpInterp tc}
    {fv : FreeVarVal CoreLParams tc} {vt : TyVarVal} {F : Lambda.Factory CoreLParams}
    {σ : RStore Expression} {e : Expression.Expr} {τ : LMonoTy} (n : Nat)
    (h₁ : LExpr.HasTypeA [] e τ) (hF : Factory.InterpConsistent tc op F)
    (hC : ConstrInterpConsistent tc op F) (hW : EvalSoundHyps tc op fv vt F σ e) :
    ∃ h₂ : LExpr.HasTypeA [] (LExpr.eval n F σ e).fst τ,
      LExpr.denote tc op fv vt .nil e τ h₁ =
        LExpr.denote tc op fv vt .nil (LExpr.eval n F σ e).fst τ h₂ := by
  obtain ⟨hEnvWF, hFWF, ⟨_, hFacWF⟩, hEnv, hOps, hAnnot⟩ := hW
  exact eval_denote_soundAt tc op fv vt (n := n) h₁ hEnvWF hFWF hFacWF hF hC hEnv hOps hAnnot

/-- At every free-variable valuation `fv` consistent with the symbolic store `σ` (each stored
    term denotes the value `fv` gives its name), the term `symEval` returns has the type and the
    denotation of the input expression. -/
theorem symEval_denote (tc : TyConstrInterp) (op : OpInterp tc) (fv : FreeVarVal CoreLParams tc)
    (vt : TyVarVal) {cfg : ExploreCfg} {F : Lambda.Factory CoreLParams} {σ : RStore Expression}
    {e t : Expression.Expr} {τ : LMonoTy}
    (h : symEval cfg F σ e = some t)
    (h₁ : LExpr.HasTypeA [] e τ)
    (hF : Factory.InterpConsistent tc op F)
    (hC : ConstrInterpConsistent tc op F)
    (hW : EvalSoundHyps tc op fv vt F σ e) :
    ∃ h₂ : LExpr.HasTypeA [] t τ,
      LExpr.denote tc op fv vt .nil e τ h₁ = LExpr.denote tc op fv vt .nil t τ h₂ := by
  obtain rfl := symEval_eq_some h
  exact eval_denote_of_hyps _ h₁ hF hC hW

/-- Let `fv` be a valuation consistent with both the symbolic store `σs` and a concrete store
    `σc`. If `symEval` returns `t` on `σs` and `LExpr.eval` (the concrete evaluator's core)
    evaluates `e` on `σc` to `v`, then `t` and `v` have the same denotation under `fv`. -/
theorem symEval_agrees_concrete (tc : TyConstrInterp) (op : OpInterp tc)
    (fv : FreeVarVal CoreLParams tc) (vt : TyVarVal) {cfg : ExploreCfg}
    {F : Lambda.Factory CoreLParams} {σs σc : RStore Expression}
    {e t v : Expression.Expr} {τ : LMonoTy} {n : Nat}
    (h : symEval cfg F σs e = some t)
    (hc : (LExpr.eval n F σc e).fst = v)
    (h₁ : LExpr.HasTypeA [] e τ)
    (hF : Factory.InterpConsistent tc op F)
    (hC : ConstrInterpConsistent tc op F)
    (hs : EvalSoundHyps tc op fv vt F σs e)
    (hcW : EvalSoundHyps tc op fv vt F σc e) :
    ∃ (ht : LExpr.HasTypeA [] t τ) (hv : LExpr.HasTypeA [] v τ),
      LExpr.denote tc op fv vt .nil t τ ht = LExpr.denote tc op fv vt .nil v τ hv := by
  obtain ⟨ht, hst⟩ := symEval_denote tc op fv vt h h₁ hF hC hs
  subst hc
  obtain ⟨hv, hcv⟩ := eval_denote_of_hyps n h₁ hF hC hcW
  exact ⟨ht, hv, hst.symm.trans hcv⟩

/-! ## Forking at a branch -/

/-- `ForkM`'s `branch` under the symbolic language data of configuration `c`. -/
abbrev forkBranch (c : ExploreCfg) (F : Lambda.Factory CoreLParams) (σ : RStore Expression)
    (g : Expression.Expr) : ForkM Bool :=
  @InterpEffects.branch Expression (symLang c) ForkM (forkEffects c) inferInstance F σ g

/-- The three cases of `forkBranch`, spelled out: a path condition that already contains `g`
    takes the then-branch alone, one that refutes `g` takes the else-branch alone, and
    otherwise the path forks into both, the path condition growing by `g` or by `negate g`.
    Rewriting with it turns a goal about one `branch` step into these cases. -/
private theorem forkBranch_eq (c : ExploreCfg) (F : Lambda.Factory CoreLParams)
    (σ : RStore Expression) (g : Expression.Expr) (cfg : ExploreCfg) (st : PathState) :
    forkBranch c F σ g cfg st =
      if pcContains (pcExprs st.pc) g then [(.ok true, st)]
      else if pcRefutes (pcExprs st.pc) g then [(.ok false, st)]
      else
        [(.ok true,
          { st with pc := (toString f!"<label_ite_cond_true: {g.eraseTypes}>", g) :: st.pc }),
         (.ok false, { st with pc := (toString f!"<label_ite_cond_false: !({g.eraseTypes})>",
            negate g) :: st.pc })] := rfl

/-- The shape of one `branch` outcome: the path condition grows by `g` (then-branch) or by
    `negate g` (else-branch), or stays when it already decides `g`; nothing else changes. -/
def BranchOutcome (st : PathState) (g : Expression.Expr) (o : Out Bool × PathState) : Prop :=
  (∃ l, o = (.ok true, { st with pc := (l, g) :: st.pc })) ∨
  (pcContains (pcExprs st.pc) g = true ∧ o = (.ok true, st)) ∨
  (∃ l, o = (.ok false, { st with pc := (l, negate g) :: st.pc })) ∨
  (pcRefutes (pcExprs st.pc) g = true ∧ o = (.ok false, st))

/-- Every outcome of `branch` has the shape `BranchOutcome`, and there are at most two. -/
theorem forkBranch_outcomes (c : ExploreCfg) (F : Lambda.Factory CoreLParams)
    (σ : RStore Expression) (g : Expression.Expr) (cfg : ExploreCfg) (st : PathState) :
    (∀ o ∈ forkBranch c F σ g cfg st, BranchOutcome st g o) ∧
      (forkBranch c F σ g cfg st).length ≤ 2 := by
  rw [forkBranch_eq]
  by_cases h1 : pcContains (pcExprs st.pc) g = true
  · simp only [h1, ite_true, List.mem_singleton, forall_eq, List.length_singleton]
    exact ⟨Or.inr (Or.inl ⟨h1, rfl⟩), by omega⟩
  · simp only [h1, Bool.false_eq_true, ite_false]
    by_cases h2 : pcRefutes (pcExprs st.pc) g = true
    · simp only [h2, ite_true, List.mem_singleton, forall_eq, List.length_singleton]
      exact ⟨Or.inr (Or.inr (Or.inr ⟨h2, rfl⟩)), by omega⟩
    · simp only [h2, Bool.false_eq_true, ite_false, List.mem_cons, List.mem_nil_iff, or_false,
        forall_eq_or_imp, forall_eq, List.length_cons, List.length_nil]
      exact ⟨⟨Or.inl ⟨_, rfl⟩, Or.inr (Or.inr (Or.inl ⟨_, rfl⟩))⟩, by omega⟩

/-- If the path condition neither contains nor refutes `g`, `branch` has exactly two outcomes:
    the then-branch under `g` and the else-branch under `negate g`. -/
theorem forkBranch_fork (c : ExploreCfg) (F : Lambda.Factory CoreLParams) (σ : RStore Expression)
    (g : Expression.Expr) (cfg : ExploreCfg) (st : PathState)
    (h1 : pcContains (pcExprs st.pc) g = false) (h2 : pcRefutes (pcExprs st.pc) g = false) :
    ∃ lt lf, forkBranch c F σ g cfg st =
      [(.ok true, { st with pc := (lt, g) :: st.pc }),
       (.ok false, { st with pc := (lf, negate g) :: st.pc })] := by
  rw [forkBranch_eq]; simp only [h1, h2, Bool.false_eq_true, ite_false]
  exact ⟨_, _, rfl⟩

/-- The path condition holds under a model, given as a truth predicate `holds` on conditions. -/
def PCHolds (holds : Expression.Expr → Prop) (st : PathState) : Prop :=
  ∀ p ∈ st.pc, holds p.2

/-- A model's truth predicate respects the syntactic negation `negate`. -/
def NegSound (holds : Expression.Expr → Prop) : Prop :=
  ∀ g, holds (negate g) ↔ ¬ holds g

/-- A model's truth predicate gives the same truth to expressions equal up to source locations
    (`LExpr.beqIgnoringMetadata`). -/
def LocInsensitive (holds : Expression.Expr → Prop) : Prop :=
  ∀ a b, a.beqIgnoringMetadata b = true → holds a → holds b

/-- A condition the path condition contains holds where the path condition holds. -/
private theorem holds_of_contains {holds : Expression.Expr → Prop} {st : PathState}
    {g : Expression.Expr} (hloc : LocInsensitive holds) (hpc : PCHolds holds st)
    (h : pcContains (pcExprs st.pc) g = true) : holds g := by
  simp only [pcContains, pcExprs, List.any_map, List.any_eq_true, Function.comp_apply] at h
  obtain ⟨p, hp, h⟩ := h
  exact hloc _ _ h (hpc p hp)

/-- A condition the path condition refutes fails where the path condition holds. -/
private theorem not_holds_of_refutes {holds : Expression.Expr → Prop} {st : PathState}
    {g : Expression.Expr} (hloc : LocInsensitive holds) (hn : NegSound holds)
    (hpc : PCHolds holds st) (h : pcRefutes (pcExprs st.pc) g = true) : ¬ holds g := by
  simp only [pcRefutes, pcExprs, List.any_map, List.any_eq_true, Function.comp_apply,
    Bool.or_eq_true] at h
  obtain ⟨p, hp, h | h⟩ := h
  · exact (hn g).1 (hloc _ _ h (hpc p hp))
  · intro hg; exact (hn _).1 (hloc _ _ h hg) (hpc p hp)

/-- A model that satisfies the path condition, whose truth predicate respects `negate` and
    ignores source locations (`LocInsensitive`), agrees with some outcome of the fork, and
    every outcome it agrees with takes the branch its guard takes under that model. -/
theorem forkBranch_model (c : ExploreCfg) (F : Lambda.Factory CoreLParams) (σ : RStore Expression)
    (g : Expression.Expr) (cfg : ExploreCfg) (st : PathState) (holds : Expression.Expr → Prop)
    [DecidablePred holds] (hloc : LocInsensitive holds) (hn : NegSound holds)
    (hpc : PCHolds holds st) :
    (∀ o ∈ forkBranch c F σ g cfg st, PCHolds holds o.2 → o.1 = .ok (decide (holds g))) ∧
    (∃ o ∈ forkBranch c F σ g cfg st, PCHolds holds o.2) := by
  constructor
  · intro o ho hpo
    rcases (forkBranch_outcomes c F σ g cfg st).1 o ho with
      ⟨l, he⟩ | ⟨h, he⟩ | ⟨l, he⟩ | ⟨h, he⟩ <;> subst he
    · have : holds g := hpo (l, g) (List.mem_cons_self ..)
      simp [this]
    · simp [holds_of_contains hloc hpc h]
    · have : holds (negate g) := hpo (l, negate g) (List.mem_cons_self ..)
      simp [(hn g).1 this]
    · simp [not_holds_of_refutes hloc hn hpc h]
  · by_cases h1 : pcContains (pcExprs st.pc) g = true
    · refine ⟨(.ok true, st), ?_, hpc⟩
      rw [forkBranch_eq]; simp [h1]
    · by_cases h2 : pcRefutes (pcExprs st.pc) g = true
      · refine ⟨(.ok false, st), ?_, hpc⟩
        rw [forkBranch_eq]; simp [h1, h2]
      · obtain ⟨lt, lf, he⟩ :=
          forkBranch_fork c F σ g cfg st (by simpa using h1) (by simpa using h2)
        rw [he]
        by_cases hg : holds g
        · refine ⟨_, List.mem_cons_self .., ?_⟩
          intro p hp
          rcases List.mem_cons.1 hp with rfl | hp
          · exact hg
          · exact hpc p hp
        · refine ⟨_, List.mem_cons_of_mem _ (List.mem_cons_self ..), ?_⟩
          intro p hp
          rcases List.mem_cons.1 hp with rfl | hp
          · exact (hn g).2 hg
          · exact hpc p hp

/-! ## The run filtered by a model

A model is given by its truth predicate `holds` on conditions. The filtered run keeps the first
outcome whose path condition holds; its codomain `FilterM` has at most one outcome. -/

section Filter

open Classical

variable (holds : Expression.Expr → Prop)

/-- The deterministic monad of a filtered run: at most one outcome. -/
abbrev FilterM (α : Type) : Type := ExploreCfg → PathState → Option (Out α × PathState)

/-- `FilterM`'s bind runs the continuation on an `ok` outcome and keeps any other. -/
instance : Monad FilterM where
  pure a := fun _ st => some (.ok a, st)
  bind x f := fun cfg st =>
    match x cfg st with
    | some (.ok a, st') => f a cfg st'
    | some (.stop r, st') => some (.stop r, st')
    | none => none

/-- `FilterM` throws a stop outcome. -/
instance : MonadExcept StopReason FilterM where
  throw r := fun _ st => some (.stop r, st)
  tryCatch x h := fun cfg st =>
    match x cfg st with
    | some (.stop r, st') => h r cfg st'
    | o => o

/-- The filtered run under a model: the first outcome whose path condition holds. -/
noncomputable def proj {α : Type} (x : ForkM α) : FilterM α :=
  fun cfg st => (x cfg st).find? (fun o => decide (PCHolds holds o.2))

/-- A computation only extends the path condition: an outcome whose path condition holds comes
    from a state whose path condition holds. -/
private def Mono {α : Type} (x : ForkM α) : Prop :=
  ∀ cfg st o, o ∈ x cfg st → PCHolds holds o.2 → PCHolds holds st

/-- At most one outcome of a computation keeps the path condition true. -/
private def Uniq {α : Type} (x : ForkM α) : Prop :=
  ∀ cfg st, (x cfg st).Pairwise (fun a b => ¬ (PCHolds holds a.2 ∧ PCHolds holds b.2))

/-- `ExtendsPcOneConsistent x`: `x` only extends the path condition and has at most one outcome
    consistent with the model; filtering commutes with bind on such computations. -/
private def ExtendsPcOneConsistent {α : Type} (x : ForkM α) : Prop := Mono holds x ∧ Uniq holds x

/-- The continuation of `ForkM`'s bind at one outcome. -/
private def bindCont {α β : Type} (f : α → ForkM β) (cfg : ExploreCfg) :
    Out α × PathState → List (Out β × PathState)
  | (.ok a, st') => f a cfg st'
  | (.stop r, st') => [(.stop r, st')]

/-- `ForkM`'s bind as a `flatMap` of `bindCont`. -/
private theorem forkM_bind_apply {α β : Type} (x : ForkM α) (f : α → ForkM β) (cfg : ExploreCfg)
    (st : PathState) : (x >>= f) cfg st = (x cfg st).flatMap (bindCont f cfg) := by
  show List.flatMap _ _ = _
  congr 1; funext o; rcases o with ⟨o, s⟩; cases o <;> rfl

variable {holds}

/-- `bindCont` of a path-condition-extending continuation extends the path condition. -/
private theorem bindCont_mono {α β : Type} {f : α → ForkM β} (hf : ∀ a, Mono holds (f a))
    (cfg : ExploreCfg) (o : Out α × PathState) :
    ∀ y ∈ bindCont f cfg o, PCHolds holds y.2 → PCHolds holds o.2 := by
  rcases o with ⟨o, s⟩
  cases o with
  | ok a => exact fun y hy hp => hf a cfg s y hy hp
  | stop r =>
    intro y hy hp
    simp only [bindCont, List.mem_cons, List.not_mem_nil, or_false] at hy
    subst hy; exact hp

/-- `bindCont` of a continuation with at most one consistent outcome has at most one. -/
private theorem bindCont_uniq {α β : Type} {f : α → ForkM β} (hf : ∀ a, Uniq holds (f a))
    (cfg : ExploreCfg) (o : Out α × PathState) :
    (bindCont f cfg o).Pairwise (fun a b => ¬ (PCHolds holds a.2 ∧ PCHolds holds b.2)) := by
  rcases o with ⟨o, s⟩
  cases o with
  | ok a => exact hf a cfg s
  | stop r => simp [bindCont]

/-- Binding computations that only extend the path condition and have at most one outcome
    consistent with the model gives such a computation (`ExtendsPcOneConsistent`). -/
private theorem extendsPcOneConsistent_bind {α β : Type} {x : ForkM α} {f : α → ForkM β}
    (hx : ExtendsPcOneConsistent holds x) (hf : ∀ a, ExtendsPcOneConsistent holds (f a)) :
    ExtendsPcOneConsistent holds (x >>= f) := by
  constructor
  · intro cfg st y hy hp
    rw [forkM_bind_apply, List.mem_flatMap] at hy
    obtain ⟨o, ho, hy⟩ := hy
    exact hx.1 cfg st o ho (bindCont_mono (fun a => (hf a).1) cfg o y hy hp)
  · intro cfg st
    rw [forkM_bind_apply, List.pairwise_flatMap]
    refine ⟨fun o _ => bindCont_uniq (fun a => (hf a).2) cfg o, ?_⟩
    refine (hx.2 cfg st).imp fun {o o'} h y hy y' hy' hb => h ⟨?_, ?_⟩
    · exact bindCont_mono (fun a => (hf a).1) cfg o y hy hb.1
    · exact bindCont_mono (fun a => (hf a).1) cfg o' y' hy' hb.2

/-- `pure` only extends the path condition and has one outcome (`ExtendsPcOneConsistent`). -/
private theorem extendsPcOneConsistent_pure {α : Type} (a : α) :
    ExtendsPcOneConsistent holds (pure a : ForkM α) :=
  ⟨fun _ _ o ho hp => by
    simp only [pure, List.mem_cons, List.not_mem_nil, or_false] at ho
    subst ho; exact hp,
   fun _ _ => by simp [pure]⟩

/-- `throw` only extends the path condition and has one outcome (`ExtendsPcOneConsistent`). -/
private theorem extendsPcOneConsistent_throw {α : Type} (r : StopReason) :
    ExtendsPcOneConsistent holds (throw r : ForkM α) :=
  ⟨fun _ _ o ho hp => by
    simp only [throw, List.mem_cons, List.not_mem_nil, or_false] at ho
    subst ho; exact hp,
   fun _ _ => by simp [throw]⟩

/-- No outcome of the continuation at an inconsistent outcome is consistent. -/
private theorem find?_bindCont_none {α β : Type} {f : α → ForkM β} (hf : ∀ a, Mono holds (f a))
    (cfg : ExploreCfg) (o : Out α × PathState) (ho : ¬ PCHolds holds o.2) :
    (bindCont f cfg o).find? (fun y => decide (PCHolds holds y.2)) = none := by
  rw [List.find?_eq_none]
  intro y hy hp
  exact ho (bindCont_mono hf cfg o y hy (by simpa using hp))

/-- Filtering commutes with bind on a computation with at most one consistent outcome and a
    continuation that only extends the path condition. -/
private theorem proj_bind {α β : Type} (x : ForkM α) (f : α → ForkM β) (hu : Uniq holds x)
    (hf : ∀ a, Mono holds (f a)) (cfg : ExploreCfg) (st : PathState) :
    proj holds (x >>= f) cfg st = (proj holds x >>= fun a => proj holds (f a)) cfg st := by
  have key : ∀ L : List (Out α × PathState),
      L.Pairwise (fun a b => ¬ (PCHolds holds a.2 ∧ PCHolds holds b.2)) →
      (L.flatMap (bindCont f cfg)).find? (fun y => decide (PCHolds holds y.2)) =
        (match L.find? (fun o => decide (PCHolds holds o.2)) with
         | some o => (bindCont f cfg o).find? (fun y => decide (PCHolds holds y.2))
         | none => none) := by
    intro L hL
    induction L with
    | nil => simp
    | cons o L ih =>
      rw [List.pairwise_cons] at hL
      rw [List.flatMap_cons, List.find?_append, List.find?_cons]
      by_cases ho : PCHolds holds o.2
      · simp only [ho, decide_true]
        have hrest :
            (L.flatMap (bindCont f cfg)).find? (fun y => decide (PCHolds holds y.2)) = none := by
          rw [List.find?_eq_none]
          intro y hy hp
          rw [List.mem_flatMap] at hy
          obtain ⟨o', ho', hy⟩ := hy
          exact hL.1 o' ho' ⟨ho, bindCont_mono hf cfg o' y hy (by simpa using hp)⟩
        rw [hrest, Option.or_none]
      · simp only [ho, decide_false, find?_bindCont_none hf cfg o ho, Option.none_or]
        exact ih hL.2
  show List.find? _ _ = _
  rw [show (x >>= f) cfg st = (x cfg st).flatMap (bindCont f cfg) from forkM_bind_apply x f cfg st,
    key _ (hu cfg st)]
  show _ = (match List.find? _ (x cfg st) with
    | some (.ok a, st') => _ | some (.stop r, st') => _
    | none => none)
  cases hfind : List.find? (fun o => decide (PCHolds holds o.2)) (x cfg st) with
  | none => rfl
  | some o =>
    have hs : PCHolds holds o.2 := by simpa using List.find?_some hfind
    rcases o with ⟨o, s⟩
    cases o with
    | ok a => rfl
    | stop r => simp [bindCont, show PCHolds holds s from hs]

variable (holds) in
/-- `x'` is the filtered run of `x` at every state whose path condition holds. -/
def ProjEq {α : Type} (x : ForkM α) (x' : FilterM α) : Prop :=
  ∀ cfg st, PCHolds holds st → proj holds x cfg st = x' cfg st

/-- `pure` is filtered to `pure`. -/
private theorem projEq_pure {α : Type} (a : α) : ProjEq holds (pure a : ForkM α) (pure a) := by
  intro cfg st hst
  show List.find? _ [((Out.ok a : Out α), st)] = some (Out.ok a, st)
  simp [hst]

/-- `throw` is filtered to `throw`. -/
private theorem projEq_throw {α : Type} (r : StopReason) :
    ProjEq holds (throw r : ForkM α) (throw r : FilterM α) := by
  intro cfg st hst
  show List.find? _ [((Out.stop r : Out α), st)] = some (Out.stop r, st)
  simp [hst]

/-- A computation agrees with its filtered run. -/
private theorem projEq_proj {α : Type} (x : ForkM α) : ProjEq holds x (proj holds x) :=
  fun _ _ _ => rfl

/-- Agreement is closed under bind, for a computation with at most one consistent outcome and a
    continuation that only extends the path condition. -/
private theorem projEq_bind {α β : Type} {x : ForkM α} {x' : FilterM α} {f : α → ForkM β}
    {f' : α → FilterM β} (hx : ProjEq holds x x') (hu : Uniq holds x)
    (hm : ∀ a, Mono holds (f a)) (hf : ∀ a, ProjEq holds (f a) (f' a)) :
    ProjEq holds (x >>= f) (x' >>= f') := by
  intro cfg st hst
  rw [proj_bind x f hu hm cfg st]
  show (match proj holds x cfg st with
    | some (.ok a, st') => _ | some (.stop r, st') => _
    | none => none) = (match x' cfg st with
    | some (.ok a, st') => _ | some (.stop r, st') => _
    | none => none)
  rw [← hx cfg st hst]
  cases hfind : proj holds x cfg st with
  | none => rfl
  | some o =>
    have hs : PCHolds holds o.2 := by
      simpa using List.find?_some (show List.find? _ (x cfg st) = some o from hfind)
    rcases o with ⟨o, s⟩
    cases o with
    | ok a => exact hf a cfg s hs
    | stop r => rfl

variable (holds) in
/-- The effects of the filtered run: each `ForkM` effect, filtered. -/
@[reducible] noncomputable def filterEffects (c : ExploreCfg) :
    @InterpEffects Expression (symLang c) FilterM :=
  letI := symLang c
  { choose := fun F σ ty => proj holds ((forkEffects c).choose F σ ty)
    emit := fun ev => proj holds ((forkEffects c).emit ev)
    branch := fun F σ g =>
      proj holds (@InterpEffects.branch Expression (symLang c) ForkM (forkEffects c) _ F σ g) }

variable (holds) in
/-- The filtered command stepper: each `symStepCmd` step, filtered. -/
noncomputable def filterStepCmd (c : ExploreCfg) :
    @StepCmdM Expression (symLang c) Command FilterM :=
  fun fuel env cmd => proj holds (symStepCmd c fuel env cmd)

/-- `FiltersTo x x'`: `x` is `ExtendsPcOneConsistent` (only extends the path condition, at most
    one outcome consistent with the model) and its filtered run under the model is `x'`. -/
private def FiltersTo {α : Type} (holds : Expression.Expr → Prop) (x : ForkM α) (x' : FilterM α) :
    Prop :=
  ExtendsPcOneConsistent holds x ∧ ProjEq holds x x'

/-- If `x` and every `f a` are `ExtendsPcOneConsistent` with filtered runs `x'` and `f' a`, then
    `x >>= f` is `ExtendsPcOneConsistent` with filtered run `x' >>= f'` (`FiltersTo`). -/
private theorem filtersTo_bind {α β : Type} {x : ForkM α} {x' : FilterM α} {f : α → ForkM β}
    {f' : α → FilterM β} (hx : FiltersTo holds x x') (hf : ∀ a, FiltersTo holds (f a) (f' a)) :
    FiltersTo holds (x >>= f) (x' >>= f') :=
  ⟨extendsPcOneConsistent_bind hx.1 fun a => (hf a).1,
   projEq_bind hx.2 hx.1.2 (fun a => (hf a).1.1) fun a => (hf a).2⟩

/-- `pure a` in `ForkM` is `ExtendsPcOneConsistent` and is filtered to `pure a` in `FilterM`
    (`FiltersTo`). -/
private theorem filtersTo_pure {α : Type} (a : α) : FiltersTo holds (pure a : ForkM α) (pure a) :=
  ⟨extendsPcOneConsistent_pure a, projEq_pure a⟩

/-- `throw r` in `ForkM` is `ExtendsPcOneConsistent` and is filtered to `throw r` in `FilterM`
    (`FiltersTo`). -/
private theorem filtersTo_throw {α : Type} (r : StopReason) :
    FiltersTo holds (throw r : ForkM α) (throw r) :=
  ⟨extendsPcOneConsistent_throw r, projEq_throw r⟩

/-- A computation that only extends the path condition and has at most one outcome consistent
    with the model (`ExtendsPcOneConsistent`) agrees with its filtered run (`FiltersTo`). -/
private theorem filtersTo_proj {α : Type} {x : ForkM α} (hx : ExtendsPcOneConsistent holds x) :
    FiltersTo holds x (proj holds x) :=
  ⟨hx, projEq_proj x⟩

/-- `branch` only extends the path condition, and under a model that never makes both a guard
    and its negation true, has at most one consistent outcome. -/
private theorem extendsPcOneConsistent_branch (c : ExploreCfg)
    (hn : ∀ g, holds (negate g) → ¬ holds g)
    (F : Lambda.Factory CoreLParams) (σ : RStore Expression) (g : Expression.Expr) :
    ExtendsPcOneConsistent holds
      (@InterpEffects.branch Expression (symLang c) ForkM (forkEffects c) _ F σ g) := by
  have he : ∀ cfg st, @InterpEffects.branch Expression (symLang c) ForkM (forkEffects c) _ F σ g
      cfg st =
      if pcContains (pcExprs st.pc) g then [(.ok true, st)]
      else if pcRefutes (pcExprs st.pc) g then [(.ok false, st)]
      else
        [(.ok true,
          { st with pc := (toString f!"<label_ite_cond_true: {g.eraseTypes}>", g) :: st.pc }),
         (.ok false, { st with pc := (toString f!"<label_ite_cond_false: !({g.eraseTypes})>",
            negate g) :: st.pc })] := fun _ _ => rfl
  constructor
  · intro cfg st o ho hp
    rw [he] at ho
    split at ho
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at ho; subst ho; exact hp
    · split at ho
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at ho; subst ho; exact hp
      · simp only [List.mem_cons, List.mem_nil_iff, or_false] at ho
        rcases ho with rfl | rfl <;> exact fun q hq => hp q (List.mem_cons_of_mem _ hq)
  · intro cfg st
    rw [he]
    split
    · simp
    · split
      · simp
      · simp only [List.pairwise_cons, List.mem_cons, or_false, forall_eq,
          List.not_mem_nil, false_imp_iff, implies_true, List.Pairwise.nil, and_true]
        rintro ⟨h1, h2⟩
        exact hn g (h2 _ (List.mem_cons_self ..)) (h1 _ (List.mem_cons_self ..))

/-- `choose` has one outcome and leaves the path condition. -/
private theorem extendsPcOneConsistent_choose (c : ExploreCfg) (name : String)
    (F : Lambda.Factory CoreLParams) (σ : RStore Expression) (ty : Expression.Ty) :
    ExtendsPcOneConsistent holds
      (@InterpEffects.choose Expression (symLang c) ForkM (forkEffects c name) F σ ty) := by
  constructor
  · intro cfg st o ho hp
    have he : @InterpEffects.choose Expression (symLang c) ForkM (forkEffects c name) F σ ty cfg
        st =
        match ty.toMonoType? with
        | some mty => [(.ok (mkSym cfg.pre st.next mty name),
            { st with next := st.next + 1,
                      choices := .sym (mkSym cfg.pre st.next mty name) :: st.choices })]
        | none => [(.stop .illTypedValue, st)] := rfl
    rw [he] at ho
    split at ho <;>
      (simp only [List.mem_cons, List.not_mem_nil, or_false] at ho; subst ho; exact hp)
  · intro cfg st
    show List.Pairwise _ (match ty.toMonoType? with
        | some mty => [((Out.ok (mkSym cfg.pre st.next mty name) : Out Expression.Expr),
            { st with next := st.next + 1,
                      choices := .sym (mkSym cfg.pre st.next mty name) :: st.choices })]
        | none => [(.stop .illTypedValue, st)])
    split <;> simp

/-- A computation with one outcome that only extends the path condition is
    `ExtendsPcOneConsistent`. -/
private theorem extendsPcOneConsistent_single {α : Type} {x : ForkM α}
    (h : ∀ cfg st, ∃ o, x cfg st = [o] ∧ (PCHolds holds o.2 → PCHolds holds st)) :
    ExtendsPcOneConsistent holds x := by
  constructor
  · intro cfg st o ho hp
    obtain ⟨o', he, hm⟩ := h cfg st
    rw [he, List.mem_singleton] at ho; subst ho; exact hm hp
  · intro cfg st
    obtain ⟨o', he, -⟩ := h cfg st
    rw [he]; simp

/-- `emit` only extends the path condition, with one outcome. -/
private theorem extendsPcOneConsistent_emit (c : ExploreCfg) (name : String)
    (ev : @IEvent Expression (symLang c)) :
    ExtendsPcOneConsistent holds
      (@InterpEffects.emit Expression (symLang c) ForkM (forkEffects c name) ev) := by
  have hEval : ∀ arg, ExtendsPcOneConsistent holds (evalCond arg) := fun arg =>
    extendsPcOneConsistent_single fun cfg st => by
    unfold evalCond; split <;> exact ⟨_, rfl, id⟩
  have hRec : ∀ k arg cnd, ExtendsPcOneConsistent holds (record k arg cnd) := fun k arg cnd =>
    extendsPcOneConsistent_single fun cfg st => ⟨_, rfl, fun h p hp => h p hp⟩
  have hAss : ∀ l cnd, ExtendsPcOneConsistent holds (assumeCond l cnd) := fun l cnd =>
    extendsPcOneConsistent_single fun cfg st => by
    unfold assumeCond; split
    · exact ⟨_, rfl, id⟩
    · exact ⟨_, rfl, fun h p hp => h p (List.mem_cons_of_mem _ hp)⟩
  cases ev with
  | assume arg => exact extendsPcOneConsistent_bind (hEval arg) fun cnd => hAss _ cnd
  | assert arg => exact extendsPcOneConsistent_bind (hEval arg) fun cnd => hRec _ arg cnd
  | cover arg => exact extendsPcOneConsistent_bind (hEval arg) fun cnd => hRec _ arg cnd

/-- Running computations that only extend the path condition and have at most one consistent
    outcome in sequence (`forM`) gives such a computation (`ExtendsPcOneConsistent`). -/
private theorem extendsPcOneConsistent_forM {α : Type} (f : α → ForkM PUnit)
    (hf : ∀ a, ExtendsPcOneConsistent holds (f a)) :
    ∀ l : List α, ExtendsPcOneConsistent holds (l.forM f)
  | [] => extendsPcOneConsistent_pure _
  | a :: as => extendsPcOneConsistent_bind (hf a) fun _ => extendsPcOneConsistent_forM f hf as

/-- Every command step of `symStepCmd` only extends the path condition and has at most one
    consistent outcome. -/
private theorem extendsPcOneConsistent_symStepCmd (c : ExploreCfg) (fuel : Nat)
    (env : @IEnv Expression (symLang c)) (cmd : Command) :
    ExtendsPcOneConsistent holds (symStepCmd c fuel env cmd) := by
  letI := symLang c
  cases cmd with
  | call _ _ _ => exact extendsPcOneConsistent_throw _
  | cmd base =>
    show ExtendsPcOneConsistent holds (stepBase c fuel env base >>= fun store => pure _)
    refine extendsPcOneConsistent_bind ?_ fun _ => extendsPcOneConsistent_pure _
    letI := forkEffects c (havocName base)
    unfold stepBase stepBaseCmdStore
    dsimp only
    repeat' (first
      | exact extendsPcOneConsistent_pure _
      | exact extendsPcOneConsistent_throw _
      | refine extendsPcOneConsistent_bind (extendsPcOneConsistent_choose c _ _ _ _) fun _ => ?_
      | refine extendsPcOneConsistent_bind
          (extendsPcOneConsistent_forM _ (extendsPcOneConsistent_emit c _) _) fun _ => ?_
      | refine extendsPcOneConsistent_bind ?_ fun _ => ?_
      | (split <;> try dsimp only))

/-- The guard resolution of the forking run. -/
private abbrev rgF (c : ExploreCfg) (fuel : Nat) (env : @IEnv Expression (symLang c))
    (g : ExprOrNondet Expression) : ForkM Bool :=
  @resolveGuard Expression ForkM _ _ (symLang c) _ (forkEffects c) _ fuel env g

variable (holds) in
/-- The guard resolution of the filtered run. -/
private noncomputable abbrev rgG (c : ExploreCfg) (fuel : Nat) (env : @IEnv Expression (symLang c))
    (g : ExprOrNondet Expression) : FilterM Bool :=
  @resolveGuard Expression FilterM _ _ (symLang c) _ (filterEffects holds c) _ fuel env g

/-- Guard resolution in `ForkM` only extends the path condition, has at most one outcome
    consistent with the model, and is filtered to guard resolution in `FilterM` (`FiltersTo`). -/
private theorem filtersTo_resolveGuard (c : ExploreCfg) (hn : ∀ g, holds (negate g) → ¬ holds g)
    (fuel : Nat) (env : @IEnv Expression (symLang c)) (g : ExprOrNondet Expression) :
    FiltersTo holds (rgF c fuel env g) (rgG holds c fuel env g) := by
  cases g with
  | det e =>
    unfold rgF rgG resolveGuard
    repeat' (first
      | exact filtersTo_pure _
      | exact filtersTo_throw _
      | exact filtersTo_proj (extendsPcOneConsistent_branch c hn _ _ _)
      | contradiction
      | split)
  | nondet =>
    unfold rgF rgG resolveGuard
    refine filtersTo_bind (filtersTo_proj (extendsPcOneConsistent_choose c _ _ _ _)) fun v => ?_
    repeat' (first
      | exact filtersTo_pure _
      | exact filtersTo_throw _
      | split)

/-- One `stepInterp` step in `ForkM` only extends the path condition, has at most one outcome
    consistent with the model, and is filtered to one step in `FilterM` (`FiltersTo`). -/
private theorem filtersTo_stepInterp (c : ExploreCfg) (hn : ∀ g, holds (negate g) → ¬ holds g)
    (fuel : Nat) (k : @IConfig Expression (symLang c) Command) :
    FiltersTo holds
      (@stepInterp Expression Command ForkM _ _ _ (symLang c) _ _ (forkEffects c) _
        (symStepCmd c) fuel k)
      (@stepInterp Expression Command FilterM _ _ _ (symLang c) _ _ (filterEffects holds c) _
        (filterStepCmd holds c) fuel k) := by
  induction k with
  | stmt stmt env =>
    cases stmt with
    | cmd cmd => exact filtersTo_proj (extendsPcOneConsistent_symStepCmd c fuel env cmd)
    | block => exact filtersTo_pure _
    | ite g t e md =>
      exact filtersTo_bind (filtersTo_resolveGuard c hn fuel env g) fun _ => filtersTo_pure _
    | loop g m i b md =>
      exact filtersTo_bind (filtersTo_resolveGuard c hn fuel env g) fun _ => filtersTo_pure _
    | exit => exact filtersTo_pure _
    | typeDecl => exact filtersTo_pure _
  | stmts ss env =>
    match ss with
    | [] => exact filtersTo_pure _
    | [_] => exact filtersTo_pure _
    | _ :: _ :: _ => exact filtersTo_pure _
  | terminal => exact filtersTo_pure _
  | exiting => exact filtersTo_pure _
  | seq inner rest ih =>
    cases inner with
    | terminal => exact filtersTo_pure _
    | exiting => exact filtersTo_pure _
    | _ => exact filtersTo_bind ih fun _ => filtersTo_pure _
  | seqs inner k ih =>
    cases inner with
    | terminal => cases k <;> exact filtersTo_pure _
    | exiting => cases k <;> exact filtersTo_pure _
    | _ => exact filtersTo_bind ih fun i => by cases i <;> exact filtersTo_pure _
  | block label frame inner ih =>
    cases inner with
    | terminal => exact filtersTo_pure _
    | exiting l env =>
      show FiltersTo holds (if label = some l then pure _ else pure _)
        (if label = some l then pure _ else pure _)
      by_cases h : label = some l <;> simp only [h, ↓reduceIte] <;> exact filtersTo_pure _
    | _ => exact filtersTo_bind ih fun _ => filtersTo_pure _

/-- Under a model that never makes both a guard and its negation true, one `stepInterp` step in
    `ForkM`, filtered, is one `stepInterp` step of the deterministic filtered run, at every state
    whose path condition holds. -/
theorem proj_stepInterp (c : ExploreCfg)
    (hn : ∀ g, holds (negate g) → ¬ holds g)
    (fuel : Nat) (k : @IConfig Expression (symLang c) Command) :
    ProjEq holds
      (@stepInterp Expression Command ForkM _ _ _ (symLang c) _ _ (forkEffects c) _
        (symStepCmd c) fuel k)
      (@stepInterp Expression Command FilterM _ _ _ (symLang c) _ _ (filterEffects holds c) _
        (filterStepCmd holds c) fuel k) :=
  (filtersTo_stepInterp c hn fuel k).2

/-- A command step over stores (`StepCmdM.toStore`) of `symStepCmd` in `ForkM` only extends the
    path condition, has at most one outcome consistent with the model, and is filtered to the
    one of `filterStepCmd` in `FilterM` (`FiltersTo`). -/
private theorem filtersTo_toStore (c : ExploreCfg) (fuel : Nat) (f : InterpLang.RFactory Expression)
    (σ : @IStore Expression (symLang c)) (cmd : Command) :
    FiltersTo holds
      (@StepCmdM.toStore Expression (symLang c) Command ForkM _ (symStepCmd c) fuel f σ cmd)
      (@StepCmdM.toStore Expression (symLang c) Command FilterM _ (filterStepCmd holds c)
        fuel f σ cmd) :=
  filtersTo_bind (filtersTo_proj (extendsPcOneConsistent_symStepCmd c fuel _ cmd))
    fun _ => filtersTo_pure _

/-- One CFG step of the forking run. -/
private abbrev cfgStepF (c : ExploreCfg) (fuel : Nat)
    (k : @ICFGConfig String Command Expression (symLang c)) :
    ForkM (@ICFGConfig String Command Expression (symLang c)) :=
  @stepInterpCFG Expression String Command ForkM _ _ (symLang c) _ (forkEffects c) _ _
    (@StepCmdM.toStore Expression (symLang c) Command ForkM _ (symStepCmd c)) fuel k

variable (holds) in
/-- One CFG step of the filtered run. -/
private noncomputable abbrev cfgStepG (c : ExploreCfg) (fuel : Nat)
    (k : @ICFGConfig String Command Expression (symLang c)) :
    FilterM (@ICFGConfig String Command Expression (symLang c)) :=
  @stepInterpCFG Expression String Command FilterM _ _ (symLang c) _ (filterEffects holds c) _ _
    (@StepCmdM.toStore Expression (symLang c) Command FilterM _ (filterStepCmd holds c)) fuel k

/-- One `stepInterpCFG` step in `ForkM` only extends the path condition, has at most one
    outcome consistent with the model, and is filtered to one step in `FilterM` (`FiltersTo`). -/
private theorem filtersTo_stepInterpCFG (c : ExploreCfg) (hn : ∀ g, holds (negate g) → ¬ holds g)
    (fuel : Nat) (k : @ICFGConfig String Command Expression (symLang c)) :
    FiltersTo holds (cfgStepF c fuel k) (cfgStepG holds c fuel k) := by
  cases k with
  | atBlock g t ρ =>
    simp only [cfgStepF, cfgStepG, stepInterpCFG]
    repeat' (first
      | exact filtersTo_pure _
      | exact filtersTo_throw _
      | contradiction
      | split)
  | inBlock g t cs tr ρ =>
    cases cs with
    | cons cmd cs =>
      exact filtersTo_bind (filtersTo_toStore c fuel _ _ cmd) fun _ => filtersTo_pure _
    | nil =>
      cases tr with
      | condGoto p lt lf md =>
        simp only [cfgStepF, cfgStepG, stepInterpCFG]
        repeat' (first
          | exact filtersTo_pure _
          | exact filtersTo_throw _
          | exact filtersTo_bind (filtersTo_proj (extendsPcOneConsistent_branch c hn _ _ _))
              fun _ => filtersTo_pure _
          | contradiction
          | split)
      | finish md => exact filtersTo_pure _
  | terminal ρ => exact filtersTo_pure _

/-- Under a model that never makes both a guard and its negation true, one `stepInterpCFG` step
    in `ForkM`, filtered, is one `stepInterpCFG` step of the deterministic filtered run, at every
    state whose path condition holds. -/
theorem proj_stepInterpCFG (c : ExploreCfg)
    (hn : ∀ g, holds (negate g) → ¬ holds g)
    (fuel : Nat) (k : @ICFGConfig String Command Expression (symLang c)) :
    ProjEq holds
      (@stepInterpCFG Expression String Command ForkM _ _ (symLang c) _ (forkEffects c) _ _
        (@StepCmdM.toStore Expression (symLang c) Command ForkM _ (symStepCmd c)) fuel k)
      (@stepInterpCFG Expression String Command FilterM _ _ (symLang c) _
        (filterEffects holds c) _ _
        (@StepCmdM.toStore Expression (symLang c) Command FilterM _ (filterStepCmd holds c))
        fuel k) :=
  (filtersTo_stepInterpCFG c hn fuel k).2

end Filter

end -- public section

end Core.SymExec
