/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import all Strata.DL.Lambda.LState
import all Strata.DL.Lambda.Factory
import all Strata.DL.Lambda.FactoryProps
import all Strata.DL.Lambda.FactoryWF
import all Strata.DL.Lambda.LExprEval
import all Strata.DL.Lambda.OperationalSemantics
import all Strata.DL.Lambda.OperationalSemanticsProps
import all Strata.DL.Lambda.LExprEvalSound
import all Strata.DL.Lambda.Denote.LExprDenote
import all Strata.DL.Lambda.Denote.Assumptions
import all Strata.DL.Lambda.Denote.LExprSemanticsConsistent
import all Strata.DL.Lambda.LExprWFProps
import Strata.DL.Lambda.OperationalSemanticsProps
import all Strata.DL.Lambda.LExprDenoteEval
import Strata.DL.Lambda.LExprDenoteEvalProps
import Strata.DL.Lambda.LExprTProps

/-!
## Rewrites that reduce, up to metadata

`eval_StepStar` relates `LExpr.eval` to the reduction relation `Step` only up to
metadata: the evaluator's output and the end of the reduction sequence agree after
`eraseMetadata`. This file packages that slack so that a rewriting pass can be shown
sound one rewrite at a time.

* the three `*_of_eraseMetadata_eq` lemmas transfer the properties the denotational
  lemmas assume across a difference in metadata;
* `ReachesModMeta F env e e'` says that `e` reduces to `e'` up to metadata, from every
  metadata variant of `e`. The second clause is what makes the relation transitive: the
  end of one reduction is only known up to metadata, and the next one has to start from
  it. Evaluating, expanding a call, and rebuilding a node from rewritten children all
  have this form;
* `Preserves` says that two expressions mean the same thing, and
  `ReachesModMeta.preserves` turns a reduction into it;
* `Preserves.denoteEval` carries it to Core's evaluator: in a store whose sorts the type map
  records, the second expression evaluates to what the first does.
-/

namespace Lambda

variable {T : LExprParams} [DecidableEq T.IDMeta]

/-! ### Transferring assumptions across metadata -/

omit [DecidableEq T.IDMeta] in
/-- Typing is preserved between two expressions that erase to the same metadata-free
form. -/
private theorem HasTypeA_of_eraseMetadata_eq [DecidableEq T.IDMeta] {Δ : List LMonoTy} {τ : LMonoTy}
    {e e' : LExpr T.mono}
    (h : e.eraseMetadata = e'.eraseMetadata) (ht : LExpr.HasTypeA Δ e τ) :
    LExpr.HasTypeA Δ e' τ := by
  rw [LExpr.HasTypeA_iff_typeCheck] at ht ⊢
  rw [replaceMetadata_typeCheck (e := e') (fun _ => ()), ← LExpr.eraseMetadata, ← h,
    LExpr.eraseMetadata, ← replaceMetadata_typeCheck]
  exact ht

/-- Structural cases shared by the two transfer lemmas below. -/
local macro "erase_cases" : tactic =>
  `(tactic| (intro e' h ho; cases e' <;>
      simp_all [LExpr.eraseMetadata, LExpr.replaceMetadata, OpsConsistent, fvars_annotated_by]))

omit [DecidableEq T.IDMeta] in
/-- Operator consistency transfers between two expressions that erase to the same
metadata-free form. -/
private theorem OpsConsistent_of_eraseMetadata_eq {F : @Factory T} :
    ∀ {e e' : LExpr T.mono}, e.eraseMetadata = e'.eraseMetadata →
      OpsConsistent F e → OpsConsistent F e' := by
  intro e
  induction e with
  | op m o ty =>
    intro e' h ho
    cases e' <;> simp only [LExpr.eraseMetadata, LExpr.replaceMetadata, LExpr.op.injEq,
      reduceCtorEq, true_and] at h
    obtain ⟨rfl, rfl⟩ := h
    cases ty <;> simpa [OpsConsistent, LFunc.opTypeSubst] using ho
  | _ => erase_cases

/-- Free-variable annotation against a type map transfers between two expressions that
erase to the same metadata-free form. -/
private theorem fvars_annotated_by_of_eraseMetadata_eq {tyMap : Map T.Identifier LMonoTy} :
    ∀ {e e' : LExpr T.mono}, e.eraseMetadata = e'.eraseMetadata →
      fvars_annotated_by tyMap e → fvars_annotated_by tyMap e' := by
  intro e
  induction e with
  | fvar m x ty =>
    intro e' h ho
    cases e' <;> simp only [LExpr.eraseMetadata, LExpr.replaceMetadata, LExpr.fvar.injEq,
      reduceCtorEq, true_and] at h
    obtain ⟨rfl, rfl⟩ := h
    cases ty <;> exact ho
  | _ => erase_cases

variable [Inhabited T.IDMeta]

/-! ### Reduction up to metadata -/

/-- `e` reduces to `e'` up to metadata, from any metadata variant of `e`. -/
def ReachesModMeta (F : @Factory T) (env : Env T) (e e' : LExpr T.mono) : Prop :=
  ∀ e₀ : LExpr T.mono, e₀.eraseMetadata = e.eraseMetadata →
    ∃ e₁, StepStar F env e₀ e₁ ∧ e₁.eraseMetadata = e'.eraseMetadata

namespace ReachesModMeta

variable {F : @Factory T} {env : Env T}

/-- Every expression reduces to itself up to metadata. -/
theorem refl (e : LExpr T.mono) : ReachesModMeta F env e e :=
  fun e₀ h => ⟨e₀, ReflTrans.refl _, h⟩

/-- Reduction up to metadata is transitive. -/
theorem trans {a b c : LExpr T.mono} (h₁ : ReachesModMeta F env a b)
    (h₂ : ReachesModMeta F env b c) : ReachesModMeta F env a c := by
  intro a₀ ha
  obtain ⟨b₀, hab, hb⟩ := h₁ a₀ ha
  obtain ⟨c₀, hbc, hc⟩ := h₂ b₀ hb
  exact ⟨c₀, ReflTrans_Transitive _ _ _ _ hab hbc, hc⟩

/-- A reduction up to metadata introduces no free variable: the free variables of the reduct
    satisfy every predicate those of the source and of the environment's values satisfy. -/
theorem namesIn [DecidableEq T.Metadata] [Subsingleton T.IDMeta] (hF : FactoryWF F)
    {S : T.Identifier → Prop} (henv : ∀ x r, env x = some r → r.NamesIn S)
    {e e' : LExpr T.mono} (h : ReachesModMeta F env e e') (he : e.NamesIn S) :
    e'.NamesIn S := by
  obtain ⟨e₁, hs, he₁⟩ := h e rfl
  have hnames := StepStar.namesIn hF henv hs he
  intro x ty hx
  rw [← LExpr.freeVars_of_eraseMetadata_eq _ _ he₁] at hx
  exact hnames x ty hx

/-- An evaluation result is reached from what was evaluated. -/
theorem of_eval [DecidableEq T.Metadata]
    [Std.ToFormat T.Metadata] [Std.ToFormat T.IDMeta]
    [Traceable LExpr.EvalProvenance T.Metadata]
    (hWF : FactoryWF F) (n : Nat) (e : LExpr T.mono) :
    ReachesModMeta F env e (LExpr.eval n F env e).fst := by
  intro e₀ h₀
  obtain ⟨e₁, hs, he⟩ := eval_StepStar F env e₀ _ n hWF rfl
  exact ⟨e₁, hs, he.trans (eval_eraseMetadata_invariant F env e₀ e n hWF h₀)⟩

/-- An expansion step, `Step.expand_fn`, from any metadata variant of the call. -/
theorem of_expand {e callee body : LExpr T.mono} {args : List (LExpr T.mono)} {fn : LFunc T}
    {ts : Subst}
    (hc : F.callOfLFunc e = some (callee, args, fn)) (hb : fn.body = some body)
    (hts : LFunc.computeTypeSubst fn callee args = some ts) :
    ReachesModMeta F env e
      (LExpr.substFvarsLifting (body.applyTypeSubst ts) (fn.inputs.keys.zip args)) := by
  intro e₀ h₀
  have hcg := callOfLFunc_eraseMetadata_congr F e₀ e false h₀
  cases hc₀ : F.callOfLFunc e₀ with
  | none => rw [hc₀] at hcg; rw [hc] at hcg; exact hcg.elim
  | some t =>
    obtain ⟨callee₀, args₀, fn₀⟩ := t
    rw [hc₀] at hcg; rw [hc] at hcg
    obtain ⟨rfl, hargs, hop⟩ := hcg
    refine ⟨_, ReflTrans.step _ _ _
      (Step.expand_fn e₀ callee₀ body _ args₀ fn₀ ts hc₀ hb ?_ rfl) (ReflTrans.refl _), ?_⟩
    · rw [computeTypeSubst_eraseMetadata_congr fn₀ callee₀ callee args₀ args hop hargs]
      exact hts
    · exact substFvarsLifting_zip_eraseMetadata_congr _ _ _ _ hargs

/-- Lift a reduction through a context that maps steps to steps. -/
private theorem stepStar_lift {f : LExpr T.mono → LExpr T.mono}
    (hf : ∀ x y, Step F env x y → Step F env (f x) (f y)) {a b : LExpr T.mono}
    (h : StepStar F env a b) : StepStar F env (f a) (f b) := by
  unfold StepStar at h ⊢
  induction h with
  | refl => exact ReflTrans.refl _
  | step x y z hxy _ ih => exact ReflTrans.step _ _ _ (hf x y hxy) ih

/-- Rebuilding an application from rewritten parts. -/
theorem app {m : T.Metadata} {f f' a a' : LExpr T.mono}
    (hf : ReachesModMeta F env f f') (ha : ReachesModMeta F env a a') :
    ReachesModMeta F env (.app m f a) (.app m f' a') := by
  intro e₀ h₀
  cases e₀ <;> simp only [LExpr.eraseMetadata, LExpr.replaceMetadata, LExpr.app.injEq,
      reduceCtorEq, true_and] at h₀
  rename_i m₀ f₀ a₀
  obtain ⟨f₁, hsf, hf₁⟩ := hf f₀ h₀.1
  obtain ⟨a₁, hsa, ha₁⟩ := ha a₀ h₀.2
  refine ⟨.app m₀ f₁ a₁, ReflTrans_Transitive _ _ _ _
    (stepStar_lift (f := fun x => .app m₀ x a₀)
      (fun x y h => Step.reduce_1 (m := m₀) (m' := m₀) x y a₀ h) hsf)
    (stepStar_lift (f := fun x => .app m₀ f₁ x)
      (fun x y h => Step.reduce_2 (m := m₀) (m' := m₀) f₁ x y h) hsa), ?_⟩
  simp only [LExpr.eraseMetadata, LExpr.replaceMetadata] at hf₁ ha₁ ⊢
  rw [hf₁, ha₁]

/-- Rebuilding an equality from rewritten sides. -/
theorem eq {m : T.Metadata} {a a' b b' : LExpr T.mono}
    (ha : ReachesModMeta F env a a') (hb : ReachesModMeta F env b b') :
    ReachesModMeta F env (.eq m a b) (.eq m a' b') := by
  intro e₀ h₀
  cases e₀ <;> simp only [LExpr.eraseMetadata, LExpr.replaceMetadata, LExpr.eq.injEq,
      reduceCtorEq, true_and] at h₀
  rename_i m₀ a₀ b₀
  obtain ⟨a₁, hsa, ha₁⟩ := ha a₀ h₀.1
  obtain ⟨b₁, hsb, hb₁⟩ := hb b₀ h₀.2
  refine ⟨.eq m₀ a₁ b₁, ReflTrans_Transitive _ _ _ _
    (stepStar_lift (f := fun x => .eq m₀ x b₀)
      (fun x y h => Step.eq_reduce_lhs (m := m₀) (m' := m₀) x y b₀ h) hsa)
    (stepStar_lift (f := fun x => .eq m₀ a₁ x)
      (fun x y h => Step.eq_reduce_rhs (m := m₀) (m' := m₀) a₁ x y h) hsb), ?_⟩
  simp only [LExpr.eraseMetadata, LExpr.replaceMetadata] at ha₁ hb₁ ⊢
  rw [ha₁, hb₁]

/-- Rebuilding a conditional expression from rewritten parts. -/
theorem ite {m : T.Metadata} {c c' t t' f f' : LExpr T.mono}
    (hc : ReachesModMeta F env c c') (ht : ReachesModMeta F env t t')
    (hf : ReachesModMeta F env f f') :
    ReachesModMeta F env (.ite m c t f) (.ite m c' t' f') := by
  intro e₀ h₀
  cases e₀ <;> simp only [LExpr.eraseMetadata, LExpr.replaceMetadata, LExpr.ite.injEq,
      reduceCtorEq, true_and] at h₀
  rename_i m₀ c₀ t₀ f₀
  obtain ⟨c₁, hsc, hc₁⟩ := hc c₀ h₀.1
  obtain ⟨t₁, hst, ht₁⟩ := ht t₀ h₀.2.1
  obtain ⟨f₁, hsf, hf₁⟩ := hf f₀ h₀.2.2
  refine ⟨.ite m₀ c₁ t₁ f₁, ReflTrans_Transitive _ _ _ _
    (stepStar_lift (f := fun x => .ite m₀ x t₀ f₀)
      (fun x y h => Step.ite_reduce_cond (m := m₀) (m' := m₀) x y t₀ f₀ h) hsc)
    (ReflTrans_Transitive _ _ _ _
      (stepStar_lift (f := fun x => .ite m₀ c₁ x f₀)
        (fun x y h => Step.ite_reduce_then_branch (m := m₀) (m' := m₀) c₁ x y f₀ h) hst)
      (stepStar_lift (f := fun x => .ite m₀ c₁ t₁ x)
        (fun x y h => Step.ite_reduce_else_branch (m := m₀) (m' := m₀) c₁ t₁ x y h) hsf)), ?_⟩
  simp only [LExpr.eraseMetadata, LExpr.replaceMetadata] at hc₁ ht₁ hf₁ ⊢
  rw [hc₁, ht₁, hf₁]

end ReachesModMeta

/-! ### Preservation of meaning -/

/-- `e'` means what `e` means. If `e` is well-formed (every operator annotated
consistently with the factory, every free variable annotated as `tyMap` says), so is
`e'`; `e'` has every type `e` has; and the two denote the same value at the type-variable
valuation `vt`. -/
def Preserves (F : @Factory T) (tyMap : Map T.Identifier LMonoTy)
    (tcInterp : TyConstrInterp) (opInterp : OpInterp tcInterp)
    (fvarVal : FreeVarVal T tcInterp) (vt : TyVarVal) (e e' : LExpr T.mono) : Prop :=
  OpsConsistent F e → fvars_annotated_by tyMap e →
    OpsConsistent F e' ∧ fvars_annotated_by tyMap e' ∧
    ∀ τ (h : LExpr.HasTypeA [] e τ), ∃ h' : LExpr.HasTypeA [] e' τ,
      LExpr.denote tcInterp opInterp fvarVal vt .nil e τ h =
        LExpr.denote tcInterp opInterp fvarVal vt .nil e' τ h'

namespace Preserves

variable {F : @Factory T} {tyMap : Map T.Identifier LMonoTy} {tcInterp : TyConstrInterp}
  {opInterp : OpInterp tcInterp} {fvarVal : FreeVarVal T tcInterp} {vt : TyVarVal}

omit [Inhabited T.IDMeta] in
/-- Meaning preservation is reflexive. -/
theorem refl (e : LExpr T.mono) : Preserves F tyMap tcInterp opInterp fvarVal vt e e :=
  fun ho ha => ⟨ho, ha, fun _ h => ⟨h, rfl⟩⟩

omit [Inhabited T.IDMeta] in
/-- Meaning-preservation is transitive. -/
theorem trans {a b c : LExpr T.mono}
    (h₁ : Preserves F tyMap tcInterp opInterp fvarVal vt a b)
    (h₂ : Preserves F tyMap tcInterp opInterp fvarVal vt b c) :
    Preserves F tyMap tcInterp opInterp fvarVal vt a c := by
  intro ho ha
  obtain ⟨hob, hab, hdb⟩ := h₁ ho ha
  obtain ⟨hoc, hac, hdc⟩ := h₂ hob hab
  refine ⟨hoc, hac, fun τ h => ?_⟩
  obtain ⟨hb, eb⟩ := hdb τ h
  obtain ⟨hc, ec⟩ := hdc τ hb
  exact ⟨hc, eb.trans ec⟩

end Preserves

/-! ### Preservation under Core's evaluator

`LExpr.denoteEval` annotates the free variables of an expression with the sorts of their
stored values before denoting it. An expression whose free variables already carry those
sorts is left unchanged by the annotation, and so is every expression it reduces to, as
long as the type map it is annotated against records the stored sorts. -/

omit [Inhabited T.IDMeta] in
/-- An expression annotated against a type map annotates every free variable. -/
theorem fvars_annotated_by_annotated {tyMap : Map T.Identifier LMonoTy} :
    ∀ {e : LExpr T.mono}, fvars_annotated_by tyMap e →
      ∀ x ty, (x, ty) ∈ LExpr.freeVars e → ∃ t, ty = some t ∧
        ∀ t', Map.find? tyMap x = some t' → t = t' := by
  intro e he x ty hx
  cases ty with
  | none =>
    exfalso
    induction e with
    | const | op | bvar => simp [LExpr.freeVars] at hx
    | fvar m y ty =>
      simp only [LExpr.freeVars, List.mem_singleton, Prod.mk.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx; exact he
    | abs _ _ _ _ ih => exact ih he hx
    | quant _ _ _ _ _ _ ih₁ ih₂ =>
      simp only [LExpr.freeVars, List.mem_append] at hx
      exact hx.elim (ih₁ he.1) (ih₂ he.2)
    | app _ _ _ ih₁ ih₂ =>
      simp only [LExpr.freeVars, List.mem_append] at hx
      exact hx.elim (ih₁ he.1) (ih₂ he.2)
    | eq _ _ _ ih₁ ih₂ =>
      simp only [LExpr.freeVars, List.mem_append] at hx
      exact hx.elim (ih₁ he.1) (ih₂ he.2)
    | ite _ _ _ _ ih₁ ih₂ ih₃ =>
      simp only [LExpr.freeVars, List.mem_append] at hx
      exact hx.elim (fun hx => hx.elim (ih₁ he.1) (ih₂ he.2.1)) (ih₃ he.2.2)
  | some t => exact ⟨t, rfl, fun t' ht' => fvars_annotated_by_freeVars tyMap e he x t t' hx ht'⟩

omit [Inhabited T.IDMeta] in
/-- An expression that annotates every free variable, with the type `tyMap` gives it when it gives
    one, is annotated against `tyMap`: the converse of `fvars_annotated_by_annotated`. -/
theorem fvars_annotated_by_of_annotated {tyMap : Map T.Identifier LMonoTy} :
    ∀ {e : LExpr T.mono}, (∀ x ty, (x, ty) ∈ LExpr.freeVars e → ∃ t, ty = some t ∧
      ∀ t', Map.find? tyMap x = some t' → t = t') → fvars_annotated_by tyMap e := by
  intro e h
  induction e with
  | const | op | bvar => trivial
  | fvar m y ty =>
    obtain ⟨t, rfl, ht⟩ := h y ty (by simp [LExpr.freeVars])
    exact ht
  | abs _ _ _ _ ih => exact ih (fun x ty hx => h x ty (by simpa [LExpr.freeVars] using hx))
  | quant _ _ _ _ _ _ ih₁ ih₂ | app _ _ _ ih₁ ih₂ | eq _ _ _ ih₁ ih₂ =>
    exact ⟨ih₁ (fun x ty hx => h x ty (by simp [LExpr.freeVars, hx])),
      ih₂ (fun x ty hx => h x ty (by simp [LExpr.freeVars, hx]))⟩
  | ite _ _ _ _ ih₁ ih₂ ih₃ =>
    exact ⟨ih₁ (fun x ty hx => h x ty (by simp [LExpr.freeVars, hx])),
      ih₂ (fun x ty hx => h x ty (by simp [LExpr.freeVars, hx])),
      ih₃ (fun x ty hx => h x ty (by simp [LExpr.freeVars, hx]))⟩

omit [DecidableEq T.IDMeta] [Inhabited T.IDMeta] in
/-- Equal terms have equal denotations, whatever typing proofs they come with. -/
private theorem denote_congr_term {tc : TyConstrInterp} {op : OpInterp tc}
    {fv : FreeVarVal T tc} {vt : TyVarVal} {a b : LExpr T.mono} {τ : LMonoTy} (hab : a = b)
    (ha : a.HasTypeA [] τ) (hb : b.HasTypeA [] τ) :
    LExpr.denote tc op fv vt .nil a τ ha = LExpr.denote tc op fv vt .nil b τ hb := by
  subst hab; rfl

omit [Inhabited T.IDMeta] in
/-- Under a type map that records the sorts of the stored values, an expression annotated
    against it is left unchanged by the store's annotation. -/
private theorem annotateFvars_ann_eq_self {tyMap : Map T.Identifier LMonoTy} {σ : ValStore T}
    {tc : TyConstrInterp}
    (hmap : ∀ x τ, Map.find? tyMap x = some τ →
      ∃ v, σ x = some v ∧ v.tc = tc ∧ v.sort.toMonoTy = τ)
    {e : LExpr T.mono} (hann : fvars_annotated_by tyMap e)
    (hcov : e.NamesIn (fun x => (Map.find? tyMap x).isSome)) :
    e.annotateFvars σ.ann = e := by
  apply LExpr.annotateFvars_eq_self_of_none
  intro x ty hx
  obtain ⟨t, rfl, ht⟩ := fvars_annotated_by_annotated hann x ty hx
  obtain ⟨t', ht'⟩ := Option.isSome_iff_exists.mp (hcov x _ hx)
  obtain ⟨v, hv, -, hs⟩ := hmap x t' ht'
  right
  simp only [ValStore.ann, hv, Option.map_some, hs, ht t' ht']

omit [Inhabited T.IDMeta] in
/-- Every free variable of an expression covered by such a type map is bound in the store,
    to a value of the model. -/
private theorem defines_of_cover {tyMap : Map T.Identifier LMonoTy} {σ : ValStore T}
    {tc : TyConstrInterp}
    (hmap : ∀ x τ, Map.find? tyMap x = some τ →
      ∃ v, σ x = some v ∧ v.tc = tc ∧ v.sort.toMonoTy = τ)
    {e : LExpr T.mono} (hcov : e.NamesIn (fun x => (Map.find? tyMap x).isSome)) :
    σ.Defines tc e := by
  intro x hx
  rw [getVars_eq_freeVars_idents] at hx
  obtain ⟨⟨_, ty⟩, hmem, rfl⟩ := List.mem_map.mp hx
  obtain ⟨t', ht'⟩ := Option.isSome_iff_exists.mp (hcov _ ty hmem)
  obtain ⟨v, hv, htc, -⟩ := hmap _ t' ht'
  exact ⟨v, hv, htc⟩

omit [Inhabited T.IDMeta] in
/-- **Preservation under Core's evaluator.** If `e` and `e'` mean the same thing under the
    valuation a store induces, and the type map they are annotated against records the
    stored sorts and covers both, then `e'` evaluates in the store to what `e` evaluates
    to. -/
theorem Preserves.denoteEval {M : ModeledFactory T} {σ : ValStore T}
    {F : @Factory T} {tyMap : Map T.Identifier LMonoTy} {e e' : LExpr T.mono}
    (hP : Preserves F tyMap M.model.tcInterp M.model.opInterp
      (@ValStore.fvarVal T M.model.tcInterp M.model.allInhabited σ) M.tyVarVal e e')
    (hops : OpsConsistent F e) (hann : fvars_annotated_by tyMap e)
    (hmap : ∀ x τ, Map.find? tyMap x = some τ →
      ∃ v, σ x = some v ∧ v.tc = M.model.tcInterp ∧ v.sort.toMonoTy = τ)
    (hcov : e.NamesIn (fun x => (Map.find? tyMap x).isSome))
    (hcov' : e'.NamesIn (fun x => (Map.find? tyMap x).isSome))
    {v : SemValue} (hv : e.denoteEval M σ = some v) : e'.denoteEval M σ = some v := by
  obtain ⟨-, τ, hτ, hg, rfl⟩ := LExpr.denoteEval_eq_some_iff.mp hv
  have he := annotateFvars_ann_eq_self hmap hann hcov
  obtain ⟨-, hann', hden⟩ := hP hops hann
  have he' := annotateFvars_ann_eq_self hmap hann' hcov'
  have h₀ : e.HasTypeA [] τ := he ▸ hτ
  obtain ⟨h', hd⟩ := hden τ h₀
  refine LExpr.denoteEval_eq_some_iff.mpr
    ⟨defines_of_cover hmap hcov', τ, he'.symm ▸ h', hg, ?_⟩
  unfold LExpr.denoteEvalResult
  congr 1
  exact (denote_congr_term he hτ h₀).trans (hd.trans
    (denote_congr_term he'.symm h' _))

/-- A reduction keeps operators consistent with the factory, when the environment's values
are, under the factory conditions of `Factory.StepWFOn` on bodies and evaluators. -/
theorem ReachesModMeta.opsConsistent {F : @Factory T} {env : Env T}
    (hEnvOps : ∀ x r, env x = some r → OpsConsistent F r)
    (hbody : Factory.BodyOpsConsistentOn F) (heval : Factory.EvalOpsConsistentOn F)
    {e e' : LExpr T.mono} (h : ReachesModMeta F env e e') (hops : OpsConsistent F e) :
    OpsConsistent F e' := by
  obtain ⟨e₁, hs, he⟩ := h e rfl
  refine OpsConsistent_of_eraseMetadata_eq he ?_
  clear h he
  unfold StepStar at hs
  induction hs with
  | refl => exact hops
  | step a b c hab _ ih => exact ih (Step.OpsConsistent_preservedOn hab hops hEnvOps hbody heval)

/-- A reduction keeps free variables annotated against a type map, when the environment's values
are, and inlined bodies and evaluator results are (`Factory.BodyInlineAnnotated`,
`Factory.EvalAnnotatedOn`). -/
theorem ReachesModMeta.annotated {F : @Factory T} {env : Env T}
    {tyMap : Map T.Identifier LMonoTy}
    (hEnvAnnot : ∀ x r, env x = some r → fvars_annotated_by tyMap r)
    (hbody : Factory.BodyInlineAnnotated F tyMap) (heval : Factory.EvalAnnotatedOn F tyMap)
    {e e' : LExpr T.mono} (h : ReachesModMeta F env e e') (hann : fvars_annotated_by tyMap e) :
    fvars_annotated_by tyMap e' := by
  obtain ⟨e₁, hs, he⟩ := h e rfl
  refine fvars_annotated_by_of_eraseMetadata_eq he ?_
  clear h he
  unfold StepStar at hs
  induction hs with
  | refl => exact hann
  | step a b c hab _ ih =>
    exact ih (Step.fvars_annotated_preservedOn hab hann hEnvAnnot hbody heval)

/-- A reduction up to metadata brings in only the factory's operators: the operators of the
    reduct satisfy every predicate those of the source, of the environment's values and the
    factory's functions satisfy, when the factory brings in only its own operators. -/
theorem ReachesModMeta.opsIn {F : @Factory T} {env : Env T} (hF : F.OpsClosed)
    {S : T.Identifier → Prop} (hFS : ∀ o : T.Identifier, o.name ∈ F → S o)
    (henv : ∀ x r, env x = some r → r.OpsIn S) {e e' : LExpr T.mono}
    (h : ReachesModMeta F env e e') (he : e.OpsIn S) : e'.OpsIn S := by
  obtain ⟨e₁, hs, he₁⟩ := h e rfl
  intro o ho
  rw [← LExpr.Proofs.getOps_replaceMetadata e' (fun _ => ()), ← LExpr.eraseMetadata, ← he₁,
    LExpr.eraseMetadata, LExpr.Proofs.getOps_replaceMetadata] at ho
  exact StepStar.opsIn hF hFS henv hs he o ho

/-- A reduction preserves meaning, under the assumptions the denotational semantics makes
of the environment it runs in and of the factory. -/
theorem ReachesModMeta.preserves {F : @Factory T} {env : Env T} {tf : @TypeFactory T.IDMeta}
    {tcInterp : TyConstrInterp} {opInterp : OpInterp tcInterp}
    {fvarVal : FreeVarVal T tcInterp} {vt : TyVarVal}
    (hEnvWF : Env.StepWF F env) (hFWF : Factory.StepWFOn F hEnvWF.typed.tyMap)
    (hFacWF : Factory.WF F tf) (hF : Factory.InterpConsistent tcInterp opInterp F)
    (hC : ConstrInterpConsistent tcInterp opInterp F)
    (hEnv : Env.InterpConsistentAt tcInterp opInterp fvarVal vt env)
    {e e' : LExpr T.mono} (h : ReachesModMeta F env e e') :
    Preserves F hEnvWF.typed.tyMap tcInterp opInterp fvarVal vt e e' := by
  intro hops hann
  obtain ⟨e₁, hs, he⟩ := h e rfl
  refine ⟨h.opsConsistent hEnvWF.ops hFWF.bodyOps hFWF.evalOps hops,
    h.annotated hEnvWF.annot hFWF.bodyAnnot hFWF.evalAnnot hann, fun τ ht => ?_⟩
  have ht₁ := (StepStar.type_preservedOn hs ht hEnvWF hFWF hops hann).1
  have ht' := HasTypeA_of_eraseMetadata_eq he ht₁
  refine ⟨ht', ?_⟩
  rw [StepStar.denote_preservedAt tcInterp opInterp fvarVal vt hs ht ht₁ hEnvWF hFWF hFacWF hF
    hC hEnv hops hann]
  rw [denote_replaceMetadata tcInterp opInterp fvarVal vt .nil (fun _ => ()) ht₁,
    denote_replaceMetadata tcInterp opInterp fvarVal vt .nil (fun _ => ()) ht']
  congr 1

end Lambda
