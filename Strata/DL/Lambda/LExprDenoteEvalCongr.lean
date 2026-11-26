/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Lambda.LExprDenoteEvalProps
import all Strata.DL.Lambda.LExprDenoteEval
import all Strata.DL.Lambda.LExprWF
import all Strata.DL.Lambda.Denote.LExprDenote
import all Strata.DL.Lambda.Denote.LExprAnnotated
import Strata.DL.Lambda.LExprDenoteEvalSubst
import all Strata.DL.Lambda.LExprDenoteBeta
import all Strata.DL.Lambda.Denote.LExprDenoteSubst
import Strata.DL.Lambda.LExprWFProps
import Strata.DL.Lambda.LExprDenoteEvalMeta
import all Strata.DL.Lambda.LExpr

/-! # Congruence of evaluation

An expression whose operator, abstraction and quantifier annotations are ground
(`LExpr.AnnGround`) has a ground type wherever it type checks in a store binding its free
variables (`LExpr.HasTypeA.isGround`).  So an application or an equality of such expressions
evaluates only when its parts do (`LExpr.denoteEval_app_parts`, `LExpr.denoteEval_eq_parts`);
a conditional does so in any case (`LExpr.denoteEval_ite_iff`).  Evaluation depends only on the
values of the parts: replacing them by expressions with the same values (both have none, or the
same one) keeps the value of the node (`LExpr.denoteEval_app_congr`, `LExpr.denoteEval_eq_congr`,
`LExpr.denoteEval_ite_congr`).  The proof of the case in which every part evaluates replaces the
parts by distinct variables holding their values (`LExpr.denoteEval_substFvarsBy_congr`).

Key definitions: `LExpr.AnnGround`.

Contracting a redex `(λ aty. b) v` whose argument evaluates to a value of the sort `aty` keeps
the value (`LExpr.denoteEval_subst_beta`), from the typing of the substitution
(`LExpr.typeCheck_substK`), its commutation with the annotation of free variables
(`LExpr.annotateFvars_substK`) and the denotation of a redex (`LExpr.denote_app_abs`).

Key theorems: `LExpr.HasTypeA.isGround`, `LExpr.denoteEval_substFvarsBy_congr`,
`LExpr.denoteEval_app_congr`, `LExpr.denoteEval_eq_congr`, `LExpr.denoteEval_ite_congr`,
`LExpr.typeCheck_substK`, `LExpr.annotateFvars_substK`, `LExpr.denote_app_abs`,
`LExpr.denoteEval_subst_beta`. -/

namespace Lambda

public section

variable {T : LExprParams}

/-- Every type annotation of an operator, an abstraction or a quantifier of `e` is ground.
    Annotations of free variables are not constrained: evaluation replaces them by the sorts of
    the stored values. -/
@[expose] def LExpr.AnnGround : LExpr T.mono → Prop
  | .const _ _ | .bvar _ _ | .fvar _ _ _ => True
  | .op _ _ ty => ∀ τ, ty = some τ → τ.IsGround
  | .abs _ _ ty e => (∀ τ, ty = some τ → τ.IsGround) ∧ LExpr.AnnGround e
  | .quant _ _ _ ty tr e => (∀ τ, ty = some τ → τ.IsGround) ∧ LExpr.AnnGround tr ∧
      LExpr.AnnGround e
  | .app _ f a => LExpr.AnnGround f ∧ LExpr.AnnGround a
  | .ite _ c t e => LExpr.AnnGround c ∧ LExpr.AnnGround t ∧ LExpr.AnnGround e
  | .eq _ a b => LExpr.AnnGround a ∧ LExpr.AnnGround b

/-- A function type is ground exactly when its domain and codomain are. -/
private theorem LMonoTy.IsGround.arrow_iff {a b : LMonoTy} :
    (LMonoTy.arrow a b).IsGround ↔ a.IsGround ∧ b.IsGround := by
  simp [LMonoTy.IsGround, LMonoTy.arrow, LMonoTy.substTyVars, LMonoTy.substTyVars.map,
    LSort.toMonoTy, LSort.toMonoTy.map]

/-- **Typing at ground types.**  An expression with ground annotations and ground annotations
    on its free variables has a ground type in a context of ground types. -/
theorem LExpr.HasTypeA.isGround {Δ : List LMonoTy} {e : LExpr T.mono} {τ : LMonoTy}
    (h : e.HasTypeA Δ τ) (hΔ : ∀ t ∈ Δ, t.IsGround) (hg : e.AnnGround)
    (hfv : ∀ x ty, (x, some ty) ∈ e.freeVars → ty.IsGround) : τ.IsGround := by
  induction h with
  | const => exact LConst.ty_isGround _
  | op => exact hg _ rfl
  | fvar => exact hfv _ _ (List.mem_singleton_self _)
  | bvar hi => exact hΔ _ (List.mem_of_getElem? hi)
  | abs _ ih =>
    refine LMonoTy.IsGround.arrow_iff.2 ⟨hg.1 _ rfl, ih ?_ hg.2 fun x ty hx => hfv x ty ?_⟩
    · exact fun t ht => (List.mem_cons.1 ht).elim (· ▸ hg.1 _ rfl) (hΔ t)
    · simpa [LExpr.freeVars] using hx
  | quant => rfl
  | app _ _ ihf _ =>
    exact (LMonoTy.IsGround.arrow_iff.1 (ihf hΔ hg.1 fun x ty hx =>
      hfv x ty (by simp [LExpr.freeVars, hx]))).2
  | ite _ _ _ _ iht _ =>
    exact iht hΔ hg.2.1 fun x ty hx => hfv x ty (by simp [LExpr.freeVars, hx])
  | eq => rfl

/-- Overwriting the annotations of free variables keeps the ground annotations of operators,
    abstractions and quantifiers. -/
private theorem LExpr.AnnGround.annotateFvars {e : LExpr T.mono}
    (ann : Identifier T.IDMeta → Option LMonoTy) (h : e.AnnGround) :
    (e.annotateFvars ann).AnnGround := by
  induction e with
  | const | bvar | fvar => trivial
  | op => exact h
  | abs _ _ _ _ ih => exact ⟨h.1, ih h.2⟩
  | quant _ _ _ _ _ _ iht ihe => exact ⟨h.1, iht h.2.1, ihe h.2.2⟩
  | app _ _ _ ihf iha => exact ⟨ihf h.1, iha h.2⟩
  | ite _ _ _ _ ihc iht ihe => exact ⟨ihc h.1, iht h.2.1, ihe h.2.2⟩
  | eq _ _ _ iha ihb => exact ⟨iha h.1, ihb h.2⟩

variable [DecidableEq T.IDMeta]

/-- In a store binding every free variable of `e`, the annotated `e` annotates each free
    variable with a ground type: the type of the sort of its value. -/
private theorem ValStore.Defines.annotated_ground {σ : ValStore T} {tc : TyConstrInterp}
    {e : LExpr T.mono} (hd : σ.Defines tc e) :
    ∀ x ty, (x, some ty) ∈ (e.annotateFvars σ.ann).freeVars → ty.IsGround := by
  intro x ty hx
  obtain ⟨⟨ty', hx'⟩, hann⟩ := LExpr.mem_freeVars_annotateFvars hx
  obtain ⟨v, hv, -⟩ := hd x (LExpr.mem_getVars_of_mem_freeVars hx')
  obtain rfl := Option.some.inj
    (hann _ (by simp [ValStore.ann, hv] : σ.ann x = some v.sort.toMonoTy))
  exact LSort.toMonoTy_isGround _


/-- **An application evaluates only when its parts do**, for a function with ground
    annotations. -/
theorem LExpr.denoteEval_app_parts {M : ModeledFactory T} {σ : ValStore T} {m : T.Metadata}
    {f a : LExpr T.mono} {v : SemValue} (hf : f.AnnGround)
    (h : (LExpr.app m f a).denoteEval M σ = some v) :
    (∃ w, f.denoteEval M σ = some w) ∧ ∃ w, a.denoteEval M σ = some w := by
  obtain ⟨hd, τ, hτ, -, -⟩ := LExpr.denoteEval_eq_some_iff.mp h
  cases hτ with
  | app hfT haT =>
    have hdf := hd.mono (e' := f) fun x ty hx => ⟨ty, by simp [LExpr.freeVars, hx]⟩
    have hgf := hfT.isGround (by simp) (hf.annotateFvars _) hdf.annotated_ground
    refine ⟨⟨_, LExpr.denoteEval_of_hasTypeA hdf hfT hgf⟩, ?_⟩
    have hda := hd.mono (e' := a) fun x ty hx => ⟨ty, by simp [LExpr.freeVars, hx]⟩
    exact ⟨_, LExpr.denoteEval_of_hasTypeA hda haT (LMonoTy.IsGround.arrow_iff.1 hgf).1⟩

/-- **An equality evaluates only when its sides do**, for a left side with ground
    annotations. -/
theorem LExpr.denoteEval_eq_parts {M : ModeledFactory T} {σ : ValStore T} {m : T.Metadata}
    {a b : LExpr T.mono} {v : SemValue} (ha : a.AnnGround)
    (h : (LExpr.eq m a b).denoteEval M σ = some v) :
    (∃ w, a.denoteEval M σ = some w) ∧ ∃ w, b.denoteEval M σ = some w := by
  obtain ⟨hd, τ, hτ, -, -⟩ := LExpr.denoteEval_eq_some_iff.mp h
  cases hτ with
  | eq haT hbT =>
    have hda := hd.mono (e' := a) fun x ty hx => ⟨ty, by simp [LExpr.freeVars, hx]⟩
    have hga := haT.isGround (by simp) (ha.annotateFvars _) hda.annotated_ground
    refine ⟨⟨_, LExpr.denoteEval_of_hasTypeA hda haT hga⟩, ?_⟩
    have hdb := hd.mono (e' := b) fun x ty hx => ⟨ty, by simp [LExpr.freeVars, hx]⟩
    exact ⟨_, LExpr.denoteEval_of_hasTypeA hdb hbT hga⟩

/-- **Substituting expressions with equal values.**  Two substitutions that send each free
    variable of `E` to expressions with the same value give `E` the same value. -/
theorem LExpr.denoteEval_substFvarsBy_congr {M : ModeledFactory T} {σ : ValStore T}
    (E : LExpr T.mono) (l₁ l₂ : Identifier T.IDMeta → Option (LExpr T.mono))
    (h : ∀ x ty, (x, ty) ∈ E.freeVars → ∃ r₁ r₂ w, l₁ x = some r₁ ∧ l₂ x = some r₂ ∧
      r₁.denoteEval M σ = some w ∧ r₂.denoteEval M σ = some w) :
    (E.substFvarsBy l₁).denoteEval M σ = (E.substFvarsBy l₂).denoteEval M σ := by
  let σh : ValStore T := fun x => (l₁ x).bind (·.denoteEval M σ)
  have key : ∀ l : Identifier T.IDMeta → Option (LExpr T.mono), (∀ x ty, (x, ty) ∈ E.freeVars →
      ∃ r w, l x = some r ∧ σh x = some w ∧ r.denoteEval M σ = some w) →
      (E.substFvarsBy l).denoteEval M σ = E.denoteEval M σh := fun l hl =>
    LExpr.denoteEval_substFvarsBy_of_denoteEval l E
      (fun x ty r hx h => (hl x ty hx).elim fun _ ⟨_, h1, hs, e⟩ => by
        cases h1.symm.trans h
        exact ⟨by simp [hs], e.trans hs.symm⟩)
      fun x ty hx h => (hl x ty hx).elim fun _ ⟨_, h1, _⟩ => by simp [h1] at h
  refine (key l₁ fun x ty hx => ?_).trans (key l₂ fun x ty hx => ?_).symm <;>
    obtain ⟨r₁, r₂, w, h1, h2, e1, e2⟩ := h x ty hx
  · exact ⟨r₁, w, h1, by simp [σh, h1, e1], e1⟩
  · exact ⟨r₂, w, h2, by simp [σh, h1, e1], e2⟩

/-- The two-place substitution sending `x` to `r` and `y` to `s`. -/
private abbrev look2 (x y : Identifier T.IDMeta) (r s : LExpr T.mono) :
    Identifier T.IDMeta → Option (LExpr T.mono) :=
  fun z => if z = x then some r else if z = y then some s else none

/-- An expression that evaluates only when a part with no value does has no value. -/
private theorem none_of_part {X Y : Option SemValue} (hp : ∀ v, X = some v → ∃ w, Y = some w)
    (hY : Y = none) : X = none :=
  Option.eq_none_iff_forall_ne_some.2 fun v h => (hp v h).elim fun _ hw => by simp [hY] at hw

/-- **Congruence of applications.**  Replacing the function and the argument of an application
    by expressions with the same values keeps its value, for functions with ground annotations.
    `x` and `y` are any two distinct identifiers. -/
theorem LExpr.denoteEval_app_congr [Inhabited T.IDMeta] {M : ModeledFactory T} {σ : ValStore T}
    {m : T.Metadata}
    (x y : Identifier T.IDMeta) (hxy : x ≠ y) {f f' a a' : LExpr T.mono}
    (hf : f.AnnGround) (hf' : f'.AnnGround)
    (hfe : f'.denoteEval M σ = f.denoteEval M σ) (hae : a'.denoteEval M σ = a.denoteEval M σ) :
    (LExpr.app m f' a').denoteEval M σ = (LExpr.app m f a).denoteEval M σ := by
  rcases hfv : f.denoteEval M σ with _ | wf
  · rw [none_of_part (fun _ h => (LExpr.denoteEval_app_parts hf' h).1) (hfe.trans hfv),
      none_of_part (fun _ h => (LExpr.denoteEval_app_parts hf h).1) hfv]
  rcases hav : a.denoteEval M σ with _ | wa
  · rw [none_of_part (fun _ h => (LExpr.denoteEval_app_parts hf' h).2) (hae.trans hav),
      none_of_part (fun _ h => (LExpr.denoteEval_app_parts hf h).2) hav]
  have h := LExpr.denoteEval_substFvarsBy_congr (M := M) (σ := σ)
    (.app m (.fvar m x none) (.fvar m y none)) (look2 x y f' a') (look2 x y f a)
    fun z ty hz => by
      simp only [LExpr.freeVars, List.mem_append, List.mem_singleton, Prod.mk.injEq] at hz
      rcases hz with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact ⟨f', f, wf, by simp [look2], by simp [look2], hfe.trans hfv, hfv⟩
      · exact ⟨a', a, wa, by simp [look2, hxy.symm], by simp [look2, hxy.symm], hae.trans hav, hav⟩
  have key : ∀ p q : LExpr T.mono,
      (LExpr.app m (LExpr.replaceMetadata1 m p) (LExpr.replaceMetadata1 m q)).denoteEval M σ =
        (LExpr.app m p q).denoteEval M σ := fun p q =>
    LExpr.denoteEval_eqModuloMeta (LExpr.eqModuloMeta_iff.2 (by
      have h1 := LExpr.eraseMetadata_replaceMetadata1 (T := T.mono) m p
      have h2 := LExpr.eraseMetadata_replaceMetadata1 (T := T.mono) m q
      simp only [LExpr.eraseMetadata] at h1 h2 ⊢
      simp only [LExpr.replaceMetadata, h1, h2]))
  rw [← key f' a', ← key f a]
  simpa [LExpr.substFvarsBy, look2, hxy.symm] using h

/-- **Congruence of equalities.**  Replacing the sides of an equality by expressions with the
    same values keeps its value, for left sides with ground annotations.  `x` and `y` are any
    two distinct identifiers. -/
theorem LExpr.denoteEval_eq_congr [Inhabited T.IDMeta] {M : ModeledFactory T} {σ : ValStore T}
    {m : T.Metadata}
    (x y : Identifier T.IDMeta) (hxy : x ≠ y) {a a' b b' : LExpr T.mono}
    (ha : a.AnnGround) (ha' : a'.AnnGround)
    (hae : a'.denoteEval M σ = a.denoteEval M σ) (hbe : b'.denoteEval M σ = b.denoteEval M σ) :
    (LExpr.eq m a' b').denoteEval M σ = (LExpr.eq m a b).denoteEval M σ := by
  rcases hav : a.denoteEval M σ with _ | wa
  · rw [none_of_part (fun _ h => (LExpr.denoteEval_eq_parts ha' h).1) (hae.trans hav),
      none_of_part (fun _ h => (LExpr.denoteEval_eq_parts ha h).1) hav]
  rcases hbv : b.denoteEval M σ with _ | wb
  · rw [none_of_part (fun _ h => (LExpr.denoteEval_eq_parts ha' h).2) (hbe.trans hbv),
      none_of_part (fun _ h => (LExpr.denoteEval_eq_parts ha h).2) hbv]
  have h := LExpr.denoteEval_substFvarsBy_congr (M := M) (σ := σ)
    (.eq m (.fvar m x none) (.fvar m y none)) (look2 x y a' b') (look2 x y a b)
    fun z ty hz => by
      simp only [LExpr.freeVars, List.mem_append, List.mem_singleton, Prod.mk.injEq] at hz
      rcases hz with ⟨rfl, -⟩ | ⟨rfl, -⟩
      · exact ⟨a', a, wa, by simp [look2], by simp [look2], hae.trans hav, hav⟩
      · exact ⟨b', b, wb, by simp [look2, hxy.symm], by simp [look2, hxy.symm], hbe.trans hbv, hbv⟩
  have key : ∀ p q : LExpr T.mono,
      (LExpr.eq m (LExpr.replaceMetadata1 m p) (LExpr.replaceMetadata1 m q)).denoteEval M σ =
        (LExpr.eq m p q).denoteEval M σ := fun p q =>
    LExpr.denoteEval_eqModuloMeta (LExpr.eqModuloMeta_iff.2 (by
      have h1 := LExpr.eraseMetadata_replaceMetadata1 (T := T.mono) m p
      have h2 := LExpr.eraseMetadata_replaceMetadata1 (T := T.mono) m q
      simp only [LExpr.eraseMetadata] at h1 h2 ⊢
      simp only [LExpr.replaceMetadata, h1, h2]))
  rw [← key a' b', ← key a b]
  simpa [LExpr.substFvarsBy, look2, hxy.symm] using h

/-- **Congruence of conditionals.**  Replacing the parts of a conditional by expressions with
    the same values keeps its value. -/
theorem LExpr.denoteEval_ite_congr {M : ModeledFactory T} {σ : ValStore T} {m : T.Metadata}
    {c c' t t' e e' : LExpr T.mono} (hc : c'.denoteEval M σ = c.denoteEval M σ)
    (ht : t'.denoteEval M σ = t.denoteEval M σ) (he : e'.denoteEval M σ = e.denoteEval M σ) :
    (LExpr.ite m c' t' e').denoteEval M σ = (LExpr.ite m c t e).denoteEval M σ := by
  exact Option.ext fun v => by rw [LExpr.denoteEval_ite_iff, LExpr.denoteEval_ite_iff, hc, ht, he]

/-! ## Contraction of a redex -/

section Beta

variable {T : LExprParams}

/-- **Typing of a substitution for a bound variable** (the substituted variable is the one of
    index `Δ₁.length`, under `Δ₁.length` binders): substituting an expression `v` without loose
    bound variables, of type `aty`, gives the type the body has with `aty` for that variable. -/
theorem LExpr.typeCheck_substK {v : LExpr T.mono} {aty : LMonoTy} (hlc : v.lcAt 0 = true)
    (hv : LExpr.typeCheck [] v = some aty) :
    ∀ (b : LExpr T.mono) (Δ₁ : List LMonoTy),
      LExpr.typeCheck Δ₁ (LExpr.substK Δ₁.length (fun _ => v) b) =
        LExpr.typeCheck (Δ₁ ++ [aty]) b
  | .const .., _ => rfl
  | .op _ _ ty, _ | .fvar _ _ ty, _ => by cases ty <;> rfl
  | .bvar m i, Δ₁ => by
    simp only [LExpr.substK]
    split
    · rename_i h
      obtain rfl : i = Δ₁.length := by simpa using h
      rw [typeCheck_of_lcAt_aux (Δ' := []) hlc (by omega), hv]
      simp [LExpr.typeCheck]
    · rename_i h
      have hi : i ≠ Δ₁.length := by simpa using h
      simp only [LExpr.typeCheck]
      rcases Nat.lt_or_gt_of_ne hi with hi | hi
      · rw [List.getElem?_append_left hi]
      · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by simp; omega)]
  | .abs _ _ none _, _ | .quant _ _ _ none _ _, _ => rfl
  | .abs m n (some t) e, Δ₁ => by
    have h := LExpr.typeCheck_substK hlc hv e (t :: Δ₁)
    simp only [List.length_cons, List.cons_append] at h
    simp only [LExpr.substK, LExpr.typeCheck, h]
  | .quant m k n (some t) tr e, Δ₁ => by
    have h₁ := LExpr.typeCheck_substK hlc hv tr (t :: Δ₁)
    have h₂ := LExpr.typeCheck_substK hlc hv e (t :: Δ₁)
    simp only [List.length_cons, List.cons_append] at h₁ h₂
    simp only [LExpr.substK, LExpr.typeCheck, h₁, h₂]
  | .app m f a, Δ₁ | .eq m f a, Δ₁ => by
    simp only [LExpr.substK, LExpr.typeCheck, LExpr.typeCheck_substK hlc hv f,
      LExpr.typeCheck_substK hlc hv a]
  | .ite m c t e, Δ₁ => by
    simp only [LExpr.substK, LExpr.typeCheck, LExpr.typeCheck_substK hlc hv c,
      LExpr.typeCheck_substK hlc hv t, LExpr.typeCheck_substK hlc hv e]

/-- **Annotating the free variables commutes with substituting for a bound variable.** -/
theorem LExpr.annotateFvars_substK (ann : Identifier T.IDMeta → Option LMonoTy)
    (v : LExpr T.mono) : ∀ (k : Nat) (b : LExpr T.mono),
      (LExpr.substK k (fun _ => v) b).annotateFvars ann =
        LExpr.substK k (fun _ => v.annotateFvars ann) (b.annotateFvars ann)
  | _, .const .. | _, .op .. | _, .fvar .. => rfl
  | k, .bvar m i => by
    simp only [LExpr.substK]
    split <;> simp_all [LExpr.annotateFvars, LExpr.substK]
  | k, .abs m n ty e => by
    simp only [LExpr.substK, LExpr.annotateFvars, LExpr.annotateFvars_substK ann v (k + 1) e]
  | k, .quant m q n ty tr e => by
    simp only [LExpr.substK, LExpr.annotateFvars, LExpr.annotateFvars_substK ann v (k + 1) tr,
      LExpr.annotateFvars_substK ann v (k + 1) e]
  | k, .app m f a | k, .eq m f a => by
    simp only [LExpr.substK, LExpr.annotateFvars, LExpr.annotateFvars_substK ann v k f,
      LExpr.annotateFvars_substK ann v k a]
  | k, .ite m c t e => by
    simp only [LExpr.substK, LExpr.annotateFvars, LExpr.annotateFvars_substK ann v k c,
      LExpr.annotateFvars_substK ann v k t, LExpr.annotateFvars_substK ann v k e]

/-- **Denotation of a redex**: an application of an abstraction denotes the body under the
    denotation of the argument for the bound variable. -/
theorem LExpr.denote_app_abs {tcInterp : TyConstrInterp} {opInterp : OpInterp tcInterp}
    {fvarVal : FreeVarVal T tcInterp} {vt : TyVarVal} {m ma : T.Metadata} {n : String}
    {b v : LExpr T.mono} {aty τ : LMonoTy}
    (h_app : LExpr.HasTypeA [] (.app m (.abs ma n (some aty) b) v) τ)
    (h_body : LExpr.HasTypeA [aty] b τ) (h_v : LExpr.HasTypeA [] v aty) :
    LExpr.denote tcInterp opInterp fvarVal vt .nil (.app m (.abs ma n (some aty) b) v) τ h_app =
      LExpr.denote tcInterp opInterp fvarVal vt
        (.cons (LExpr.denote tcInterp opInterp fvarVal vt .nil v aty h_v) .nil) b τ h_body := by
  rw [denote_app .nil (.abs h_body) h_v h_app, denote_abs .nil h_body]

/-- The free-variable occurrences of a substitution for a bound variable are those of the body
    and of the substituted expression. -/
theorem LExpr.mem_freeVars_substK {v : LExpr T.mono} :
    ∀ {k : Nat} {b : LExpr T.mono} {p},
      p ∈ (LExpr.substK k (fun _ => v) b).freeVars → p ∈ b.freeVars ∨ p ∈ v.freeVars :=
  fun h => (freeVars_substK_mem _ _ _ _ h).imp_right fun ⟨_, h⟩ => h


/-- The free-variable occurrences of the body are among those of a substitution for a bound
    variable. -/
theorem LExpr.freeVars_subset_substK {v : LExpr T.mono} :
    ∀ {k : Nat} {b : LExpr T.mono} {p},
      p ∈ b.freeVars → p ∈ (LExpr.substK k (fun _ => v) b).freeVars
  | _, .const .., _, h | _, .op .., _, h | _, .fvar .., _, h => h
  | _, .bvar .., _, h => by simp [LExpr.freeVars] at h
  | k, .abs m n ty e, p, h => LExpr.freeVars_subset_substK (b := e) h
  | k, .quant m _ _ _ f a, p, h | k, .app m f a, p, h | k, .eq m f a, p, h => by
    simp only [LExpr.substK, LExpr.freeVars, List.mem_append] at h ⊢
    exact h.imp LExpr.freeVars_subset_substK LExpr.freeVars_subset_substK
  | k, .ite m c t e, p, h => by
    simp only [LExpr.substK, LExpr.freeVars, List.mem_append] at h ⊢
    exact h.imp (·.imp LExpr.freeVars_subset_substK LExpr.freeVars_subset_substK)
      LExpr.freeVars_subset_substK

/-- Substituting an expression with ground annotations for a bound variable keeps the ground
    annotations. -/
theorem LExpr.AnnGround.substK {v : LExpr T.mono} (hv : v.AnnGround) :
    ∀ {k : Nat} {b : LExpr T.mono}, b.AnnGround → (LExpr.substK k (fun _ => v) b).AnnGround
  | _, .const .., h | _, .op .., h | _, .fvar .., h => h
  | k, .bvar m i, _ => by
    simp only [LExpr.substK]
    split <;> first | exact hv | trivial
  | _, .abs .., h => ⟨h.1, LExpr.AnnGround.substK hv h.2⟩
  | _, .quant .., h => ⟨h.1, LExpr.AnnGround.substK hv h.2.1, LExpr.AnnGround.substK hv h.2.2⟩
  | _, .app .., h | _, .eq .., h => ⟨LExpr.AnnGround.substK hv h.1, LExpr.AnnGround.substK hv h.2⟩
  | _, .ite .., h => ⟨LExpr.AnnGround.substK hv h.1, LExpr.AnnGround.substK hv h.2.1,
      LExpr.AnnGround.substK hv h.2.2⟩

/-- The operators of a substitution for a bound variable are those of the body and of the
    substituted expression. -/
theorem LExpr.mem_getOps_substK {v : LExpr T.mono} :
    ∀ {k : Nat} {b : LExpr T.mono} {o},
      o ∈ LExpr.getOps (LExpr.substK k (fun _ => v) b) → o ∈ LExpr.getOps b ∨ o ∈ LExpr.getOps v
  | _, .const .., _, h | _, .op .., _, h | _, .fvar .., _, h => .inl h
  | k, .bvar m i, o, h => by
    simp only [LExpr.substK] at h
    split at h <;> first | exact .inr h | exact .inl h
  | k, .abs m n ty e, o, h => LExpr.mem_getOps_substK (b := e) h
  | k, .quant m _ _ _ f a, o, h | k, .app m f a, o, h | k, .eq m f a, o, h => by
    simp only [LExpr.substK, LExpr.getOps, List.mem_append] at h ⊢
    exact h.elim (fun h => (LExpr.mem_getOps_substK h).imp_left .inl)
      fun h => (LExpr.mem_getOps_substK h).imp_left .inr
  | k, .ite m c t e, o, h => by
    simp only [LExpr.substK, LExpr.getOps, List.mem_append] at h ⊢
    rcases h with (h | h) | h
    · exact (LExpr.mem_getOps_substK h).imp_left (.inl ∘ .inl)
    · exact (LExpr.mem_getOps_substK h).imp_left (.inl ∘ .inr)
    · exact (LExpr.mem_getOps_substK h).imp_left .inr

variable [DecidableEq T.IDMeta]

/-- **Contracting a redex keeps the value** when the argument `v` evaluates to a value of the
    sort of the bound variable's annotation `aty` (so it has no loose bound variable): the
    contraction `b[v]` and the redex `(λ aty. b) v` both evaluate exactly when the body does
    with `v` for the bound variable, to its denotation. -/
theorem LExpr.denoteEval_subst_beta {M : ModeledFactory T} {σ : ValStore T} {m ma : T.Metadata}
    {n : String} {aty : LMonoTy} {b v : LExpr T.mono} {w : SemValue}
    (hw : v.denoteEval M σ = some w) (hs : w.sort.toMonoTy = aty) :
    (LExpr.subst (fun _ => v) b).denoteEval M σ =
      (LExpr.app m (.abs ma n (some aty) b) v).denoteEval M σ := by
  obtain ⟨hdv, τv, hTv, hgv, rfl⟩ := LExpr.denoteEval_eq_some_iff.mp hw
  have hτv : (τv.substTyVars M.tyVarVal).toMonoTy = τv := hgv.substTyVars_eq _ refTyVarVal ▸ hgv
  obtain rfl : τv = aty := hτv.symm.trans hs
  let v' := v.annotateFvars σ.ann
  let b' := b.annotateFvars σ.ann
  have hlc' : v'.lcAt 0 = true := HasTypeA_nil_lcAt hTv
  have hann : (LExpr.subst (fun _ => v) b).annotateFvars σ.ann = LExpr.subst (fun _ => v') b' :=
    LExpr.annotateFvars_substK σ.ann v 0 b
  have htc : LExpr.typeCheck [] (LExpr.subst (fun _ => v') b') = LExpr.typeCheck [τv] b' :=
    LExpr.typeCheck_substK hlc' (LExpr.HasTypeA_to_typeCheck hTv) b' []
  have hdef : σ.Defines M.model.tcInterp (LExpr.subst (fun _ => v) b) ↔
      σ.Defines M.model.tcInterp (LExpr.app m (.abs ma n (some τv) b) v) := by
    simp only [ValStore.Defines, getVars_eq_freeVars_idents, List.mem_map, Prod.exists,
      exists_and_right, exists_eq_right, forall_exists_index]
    refine ⟨fun hd x ty hx => ?_, fun hd x ty hx => hd x ty (by
      simpa only [LExpr.freeVars, List.mem_append] using LExpr.mem_freeVars_substK hx)⟩
    simp only [LExpr.freeVars, List.mem_append] at hx
    exact hx.elim (hd x ty <| LExpr.freeVars_subset_substK ·)
      (hdv x <| LExpr.mem_getVars_of_mem_freeVars ·)
  refine Option.ext fun u => ?_
  rw [LExpr.denoteEval_eq_some_iff, LExpr.denoteEval_eq_some_iff, hdef]
  refine and_congr_right fun _ => ?_
  letI := M.model.allInhabited
  constructor
  · rintro ⟨τ, hτ, hg, rfl⟩
    have hb : b'.HasTypeA [τv] τ :=
      LExpr.typeCheck_to_HasTypeA (htc ▸ hann ▸ LExpr.HasTypeA_to_typeCheck hτ)
    refine ⟨τ, .app (.abs hb) hTv, hg, ?_⟩
    unfold LExpr.denoteEvalResult
    congr 1
    rw [denote_eqE _ _ _ _ .nil hann hτ (hann ▸ hτ), subst_denote _ _ _ _ hb hTv _ hlc']
    exact (LExpr.denote_app_abs _ hb hTv).symm

  · rintro ⟨τ, hτ, hg, rfl⟩
    have hb : b'.HasTypeA [τv] τ := by
      cases hτ with | app hf ha => cases hf with | abs hb' => exact HasTypeA_unique ha hTv ▸ hb'
    have hτ' : ((LExpr.subst (fun _ => v) b).annotateFvars σ.ann).HasTypeA [] τ :=
      hann ▸ LExpr.typeCheck_to_HasTypeA (htc.trans (LExpr.HasTypeA_to_typeCheck hb))
    refine ⟨τ, hτ', hg, ?_⟩
    unfold LExpr.denoteEvalResult
    congr 1
    rw [denote_eqE _ _ _ _ .nil hann hτ' (hann ▸ hτ'), subst_denote _ _ _ _ hb hTv _ hlc']
    exact LExpr.denote_app_abs hτ hb hTv

end Beta

end -- public section

end Lambda
