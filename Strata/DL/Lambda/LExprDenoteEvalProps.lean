/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Lambda.LExprDenoteEval
public import Strata.DL.Lambda.LExprEval
import all Strata.DL.Lambda.LExprDenoteEval
import all Strata.DL.Lambda.Denote.LExprDenote
import all Strata.DL.Lambda.Denote.LExprDenoteProps
import all Strata.DL.Lambda.Denote.LExprAnnotated
import all Strata.DL.Lambda.LExprWF
import Strata.DL.Lambda.LExprWFProps
import Strata.DL.Lambda.OperationalSemanticsProps

/-!
## Laws of denotational evaluation

Properties of `LExpr.denoteEval` (`Strata.DL.Lambda.LExprDenoteEval`) and of the
definitions it uses.

- `LSort.toMonoTy_injective` — a sort is determined by its monomorphic type
- `LExpr.annotateFvars_congr`, `LExpr.annotateFvars_eq_self`,
  `LExpr.mem_freeVars_annotateFvars` — annotating free variables
- `LExpr.denoteEval_eq_some_iff` — characterization
- `LExpr.denoteEval_congr`, `LExpr.denoteEval_mono` — dependence on the store
- `LExpr.denoteEval_fvar`, `LExpr.denoteEval_fvar_none`, `LExpr.denoteEval_boolConst` —
  variables and Boolean literals
- `LExpr.denoteEval_mapFvarNames` — renaming free variables
- `LExpr.denoteEval_substFvarsBy` — substituting variables or Boolean literals holding the
  values of free variables
- `LExpr.denoteEval_of_hasTypeA` — a well-typed expression evaluates
- `LExpr.denoteEval_of_isValue` — a well-typed value (`isValue`) denotes one semantic
  value in every store
- `LExpr.denoteEval_ite_iff`, `LExpr.denoteEval_app_op_bool_iff`, `LExpr.denoteEval_app2_op`
  — conditionals and operator applications
- `LExpr.denoteEval_const`, `LExpr.denoteEval_eq_true`, `LExpr.denoteEval_eq_false` —
  literals and equality
-/

namespace Lambda

public section

/-! ### Sorts as monomorphic types -/

/-- Substituting any type-variable valuation into the monomorphic type naming a sort gives back that
    sort. -/
theorem LSort.toMonoTy_substTyVars (ρ : TyVarVal) (s : LSort) :
    (s.toMonoTy).substTyVars ρ = s := by
  induction s using LSort.ind with
  | htcons name args ih =>
    simp only [LSort.toMonoTy, LMonoTy.substTyVars, LSort.tcons.injEq, true_and]
    induction args with
    | nil => rfl
    | cons a as iha =>
      simp only [LSort.toMonoTy.map, LMonoTy.substTyVars.map, List.cons.injEq]
      exact ⟨ih a List.mem_cons_self, iha fun x hx => ih x (List.mem_cons_of_mem _ hx)⟩
  | hbitvec n => rfl

/-- A sort is determined by its monomorphic type. -/
theorem LSort.toMonoTy_injective {s t : LSort} (h : s.toMonoTy = t.toMonoTy) : s = t := by
  rw [← LSort.toMonoTy_substTyVars (fun _ => .bool) s, h, LSort.toMonoTy_substTyVars]

/-! ### Semantic values -/

/-- Reading a value at its own interpretation and sort returns it. -/
theorem SemValue.read_self (v : SemValue) : v.read v.tc v.sort = some v.val := by
  simp [SemValue.read]

/-- Reading the Boolean value `b` at the Boolean sort returns `b`. -/
theorem SemValue.read_ofBool (tc : TyConstrInterp) (b : Bool) :
    (SemValue.ofBool tc b).read tc .bool = some b :=
  SemValue.read_self _

/-- Equal Boolean values under one interpretation come from equal Booleans. -/
theorem SemValue.ofBool_injective {tc : TyConstrInterp} {b₁ b₂ : Bool}
    (h : SemValue.ofBool tc b₁ = SemValue.ofBool tc b₂) : b₁ = b₂ := by
  cases h; rfl

/-- Equal integer values under one interpretation come from equal integers. -/
theorem SemValue.ofInt_injective {tc : TyConstrInterp} {i₁ i₂ : Int}
    (h : SemValue.ofInt tc i₁ = SemValue.ofInt tc i₂) : i₁ = i₂ := by
  cases h; rfl

/-- Equal bitvector values of one width under one interpretation come from equal bitvectors. -/
theorem SemValue.ofBitVec_injective {tc : TyConstrInterp} {n : Nat} {w₁ w₂ : BitVec n}
    (h : SemValue.ofBitVec tc n w₁ = SemValue.ofBitVec tc n w₂) : w₁ = w₂ := by
  cases h; rfl

/-- A value whose sort is `bitvec n` is a width-`n` bitvector. -/
theorem SemValue.exists_ofBitVec {v : SemValue} {n : Nat} (hs : v.sort.toMonoTy = .bitvec n) :
    ∃ w, v = SemValue.ofBitVec v.tc n w := by
  obtain ⟨tc, s, val⟩ := v
  obtain rfl : s = .bitvec n := LSort.toMonoTy_injective (t := .bitvec n) hs
  exact ⟨val, rfl⟩

/-- A value whose sort is `int` is an integer. -/
theorem SemValue.exists_ofInt {v : SemValue} (hs : v.sort.toMonoTy = .int) :
    ∃ i, v = SemValue.ofInt v.tc i := by
  obtain ⟨tc, s, val⟩ := v
  obtain rfl : s = .int := LSort.toMonoTy_injective (t := .int) hs
  exact ⟨val, rfl⟩

/-! ### Annotating free variables -/

variable {T : LExprParams}

/-- A free variable of `e` is among its variable names. -/
theorem LExpr.mem_getVars_of_mem_freeVars {e : LExpr T.mono} {x : Identifier T.IDMeta}
    {ty : Option LMonoTy} (h : (x, ty) ∈ e.freeVars) : x ∈ LExpr.LExpr.getVars e := by
  rw [getVars_eq_freeVars_idents]
  exact List.mem_map.mpr ⟨_, h, rfl⟩

/-- Annotating with no annotations is the identity. -/
private theorem LExpr.annotateFvars_none (e : LExpr T.mono) :
    e.annotateFvars (fun _ => none) = e := by
  induction e <;> simp_all [annotateFvars]

/-- Annotations that agree on the free variables of `e` annotate `e` alike. -/
theorem LExpr.annotateFvars_congr [DecidableEq T.IDMeta]
    {ann₁ ann₂ : Identifier T.IDMeta → Option LMonoTy} (e : LExpr T.mono)
    (h : ∀ x ty, (x, ty) ∈ e.freeVars → ann₁ x = ann₂ x) :
    e.annotateFvars ann₁ = e.annotateFvars ann₂ := by
  induction e with
  | fvar m x ty => simp [annotateFvars, h x ty (by simp [LExpr.freeVars])]
  | const | op | bvar => rfl
  | abs m n ty e ih => simp only [annotateFvars]; rw [ih (by simpa [LExpr.freeVars] using h)]
  | quant m k n ty tr e ihtr ihe =>
    simp only [LExpr.freeVars, List.mem_append] at h
    simp only [annotateFvars]
    rw [ihtr (fun x ty hx => h x ty (.inl hx)), ihe (fun x ty hx => h x ty (.inr hx))]
  | app m f a ihf iha =>
    simp only [LExpr.freeVars, List.mem_append] at h
    simp only [annotateFvars]
    rw [ihf (fun x ty hx => h x ty (.inl hx)), iha (fun x ty hx => h x ty (.inr hx))]
  | ite m c t e ihc iht ihe =>
    simp only [LExpr.freeVars, List.mem_append] at h
    simp only [annotateFvars]
    rw [ihc (fun x ty hx => h x ty (.inl (.inl hx))), iht (fun x ty hx => h x ty (.inl (.inr hx))),
      ihe (fun x ty hx => h x ty (.inr hx))]
  | eq m a b iha ihb =>
    simp only [LExpr.freeVars, List.mem_append] at h
    simp only [annotateFvars]
    rw [iha (fun x ty hx => h x ty (.inl hx)), ihb (fun x ty hx => h x ty (.inr hx))]

/-- Annotating with annotations that every free-variable occurrence of `e` already carries
    leaves `e` unchanged. -/
theorem LExpr.annotateFvars_eq_self [DecidableEq T.IDMeta]
    {ann : Identifier T.IDMeta → Option LMonoTy} (e : LExpr T.mono)
    (h : ∀ x ty, (x, ty) ∈ e.freeVars → ∃ τ, ty = some τ ∧ ann x = some τ) :
    e.annotateFvars ann = e := by
  induction e with
  | fvar m x ty =>
    obtain ⟨τ, rfl, hx⟩ := h x ty (by simp [LExpr.freeVars])
    simp [annotateFvars, hx]
  | const | op | bvar => rfl
  | abs m n ty e ih => simp only [annotateFvars]; rw [ih (by simpa [LExpr.freeVars] using h)]
  | quant m k n ty tr e ihtr ihe =>
    simp only [LExpr.freeVars, List.mem_append] at h
    simp only [annotateFvars]
    rw [ihtr (fun x ty hx => h x ty (.inl hx)), ihe (fun x ty hx => h x ty (.inr hx))]
  | app m f a ihf iha =>
    simp only [LExpr.freeVars, List.mem_append] at h
    simp only [annotateFvars]
    rw [ihf (fun x ty hx => h x ty (.inl hx)), iha (fun x ty hx => h x ty (.inr hx))]
  | ite m c t e ihc iht ihe =>
    simp only [LExpr.freeVars, List.mem_append] at h
    simp only [annotateFvars]
    rw [ihc (fun x ty hx => h x ty (.inl (.inl hx))), iht (fun x ty hx => h x ty (.inl (.inr hx))),
      ihe (fun x ty hx => h x ty (.inr hx))]
  | eq m a b iha ihb =>
    simp only [LExpr.freeVars, List.mem_append] at h
    simp only [annotateFvars]
    rw [iha (fun x ty hx => h x ty (.inl hx)), ihb (fun x ty hx => h x ty (.inr hx))]

/-- Annotation keeps the free-variable names, and annotates every free variable `x`
whose `ann x` is defined with it. -/
theorem LExpr.mem_freeVars_annotateFvars [DecidableEq T.IDMeta]
    {ann : Identifier T.IDMeta → Option LMonoTy} {e : LExpr T.mono}
    {x : Identifier T.IDMeta} {ty : Option LMonoTy}
    (h : (x, ty) ∈ (e.annotateFvars ann).freeVars) :
    (∃ ty', (x, ty') ∈ e.freeVars) ∧ (∀ t, ann x = some t → ty = some t) := by
  induction e with
  | fvar m y ty' =>
    simp only [annotateFvars, LExpr.freeVars, List.mem_singleton, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨⟨ty', by simp [LExpr.freeVars]⟩, fun t ht => by simp [ht]⟩
  | const | op | bvar => simp [annotateFvars, LExpr.freeVars] at h
  | abs m n ty' e ih =>
    simp only [annotateFvars, LExpr.freeVars] at h
    simpa [LExpr.freeVars] using ih h
  | quant m k n ty' tr e ihtr ihe =>
    simp only [annotateFvars, LExpr.freeVars, List.mem_append] at h ⊢
    rcases h with h | h
    · obtain ⟨⟨t, h1⟩, h2⟩ := ihtr h; exact ⟨⟨t, .inl h1⟩, h2⟩
    · obtain ⟨⟨t, h1⟩, h2⟩ := ihe h; exact ⟨⟨t, .inr h1⟩, h2⟩
  | app m f a ihf iha =>
    simp only [annotateFvars, LExpr.freeVars, List.mem_append] at h ⊢
    rcases h with h | h
    · obtain ⟨⟨t, h1⟩, h2⟩ := ihf h; exact ⟨⟨t, .inl h1⟩, h2⟩
    · obtain ⟨⟨t, h1⟩, h2⟩ := iha h; exact ⟨⟨t, .inr h1⟩, h2⟩
  | ite m c t e ihc iht ihe =>
    simp only [annotateFvars, LExpr.freeVars, List.mem_append] at h ⊢
    rcases h with (h | h) | h
    · obtain ⟨⟨t, h1⟩, h2⟩ := ihc h; exact ⟨⟨t, .inl (.inl h1)⟩, h2⟩
    · obtain ⟨⟨t', h1⟩, h2⟩ := iht h; exact ⟨⟨t', .inl (.inr h1)⟩, h2⟩
    · obtain ⟨⟨t', h1⟩, h2⟩ := ihe h; exact ⟨⟨t', .inr h1⟩, h2⟩
  | eq m a b iha ihb =>
    simp only [annotateFvars, LExpr.freeVars, List.mem_append] at h ⊢
    rcases h with h | h
    · obtain ⟨⟨t, h1⟩, h2⟩ := iha h; exact ⟨⟨t, .inl h1⟩, h2⟩
    · obtain ⟨⟨t, h1⟩, h2⟩ := ihb h; exact ⟨⟨t, .inr h1⟩, h2⟩

/-! ### Evaluation -/

/-- The monomorphic type naming a sort is ground. -/
theorem LSort.toMonoTy_isGround (s : LSort) : s.toMonoTy.IsGround := by
  simp [LMonoTy.IsGround, LSort.toMonoTy_substTyVars]

/-- A ground type denotes the same sort under every type-variable valuation. -/
theorem LMonoTy.IsGround.substTyVars_eq {τ : LMonoTy} (h : τ.IsGround) (ρ ρ' : TyVarVal) :
    τ.substTyVars ρ = τ.substTyVars ρ' := by
  rw [← h, LSort.toMonoTy_substTyVars, LSort.toMonoTy_substTyVars]

/-! ### Characterization -/

section Laws

variable [DecidableEq T.IDMeta]

/-- **Characterization of evaluation.**  `e` evaluates to `v` exactly when the store binds
every free variable of `e` to a value of the model, the annotated `e` has a ground type `τ`,
and `v` is its denotation at `τ`. -/
theorem LExpr.denoteEval_eq_some_iff {M : ModeledFactory T} {σ : ValStore T}
    {e : LExpr T.mono} {v : SemValue} :
    e.denoteEval M σ = some v ↔
      σ.Defines M.model.tcInterp e ∧
        ∃ τ, ∃ h : (e.annotateFvars σ.ann).HasTypeA [] τ, τ.IsGround ∧
          v = e.denoteEvalResult M σ τ h := by
  unfold LExpr.denoteEval
  by_cases hd : σ.Defines M.model.tcInterp e
  · simp only [hd, ↓reduceIte]
    split
    · rename_i τ hτ
      split
      · rename_i hg
        simp only [Option.some.injEq, true_and]
        constructor
        · rintro rfl; exact ⟨τ, _, hg, rfl⟩
        · rintro ⟨τ', h', -, rfl⟩
          have := HasTypeA_unique (LExpr.typeCheck_to_HasTypeA hτ) h'
          subst this
          rfl
      · rename_i hg
        simp only [reduceCtorEq, false_iff, true_and, not_exists, not_and]
        intro τ' h' hg'
        have := HasTypeA_unique (LExpr.typeCheck_to_HasTypeA hτ) h'
        subst this
        exact absurd hg' hg
    · rename_i hτ
      simp only [reduceCtorEq, false_iff, not_and, not_exists]
      intro _ τ h'
      have := LExpr.HasTypeA_to_typeCheck h'
      simp_all
  · simp only [hd, ↓reduceIte]
    simp

/-- An evaluated value belongs to the model's interpretation. -/
theorem LExpr.denoteEval_tc {M : ModeledFactory T} {σ : ValStore T}
    {e : LExpr T.mono} {v : SemValue} (h : e.denoteEval M σ = some v) :
    v.tc = M.model.tcInterp := by
  obtain ⟨_, _, _, _, rfl⟩ := LExpr.denoteEval_eq_some_iff.mp h
  rfl

/-- If `e` evaluates, the store binds every free variable of `e` to a value of the model. -/
theorem LExpr.denoteEval_defines {M : ModeledFactory T} {σ : ValStore T}
    {e : LExpr T.mono} {v : SemValue} (h : e.denoteEval M σ = some v) :
    σ.Defines M.model.tcInterp e :=
  (LExpr.denoteEval_eq_some_iff.mp h).1

omit [DecidableEq T.IDMeta] in
/-- Two syntactically equal expressions have equal denotations under two free-variable
    valuations that agree on their free variables. -/
private theorem denote_ext_of_eq {tc : TyConstrInterp} {op : OpInterp tc} {vt : TyVarVal}
    {fv₁ fv₂ : FreeVarVal T tc} {e₁ e₂ : LExpr T.mono} {τ : LMonoTy} (he : e₁ = e₂)
    (hfv : ∀ name ty, (name, some ty) ∈ e₁.freeVars →
      fv₁ name (LMonoTy.substTyVars vt ty) = fv₂ name (LMonoTy.substTyVars vt ty))
    (h₁ : e₁.HasTypeA [] τ) (h₂ : e₂.HasTypeA [] τ) :
    LExpr.denote tc op fv₁ vt .nil e₁ τ h₁ = LExpr.denote tc op fv₂ vt .nil e₂ τ h₂ := by
  subst he
  exact denote_ext tc vt (fun _ _ _ => rfl) hfv (fun _ _ _ _ _ => rfl) h₁ h₂

/-- Evaluation depends only on the store's bindings of the free variables. -/
theorem LExpr.denoteEval_congr {M : ModeledFactory T} {σ σ' : ValStore T}
    (e : LExpr T.mono) (h : ∀ x ty, (x, ty) ∈ e.freeVars → σ x = σ' x) :
    e.denoteEval M σ = e.denoteEval M σ' := by
  have hann : e.annotateFvars σ.ann = e.annotateFvars σ'.ann :=
    LExpr.annotateFvars_congr e fun x ty hx => by simp [ValStore.ann, h x ty hx]
  have hdef : σ.Defines M.model.tcInterp e ↔ σ'.Defines M.model.tcInterp e := by
    simp only [ValStore.Defines, getVars_eq_freeVars_idents, List.mem_map, Prod.exists,
      exists_and_right, exists_eq_right, forall_exists_index]
    constructor
    · intro hd x ty hx; rw [← h x ty hx]; exact hd x ty hx
    · intro hd x ty hx; rw [h x ty hx]; exact hd x ty hx
  have hfv : ∀ (σ₁ σ₂ : ValStore T), (∀ x ty, (x, ty) ∈ e.freeVars → σ₁ x = σ₂ x) →
      ∀ ann name ty, (name, some ty) ∈ (e.annotateFvars ann).freeVars →
      haveI := M.model.allInhabited
      σ₁.fvarVal M.model.tcInterp name (LMonoTy.substTyVars M.tyVarVal ty) =
        σ₂.fvarVal M.model.tcInterp name (LMonoTy.substTyVars M.tyVarVal ty) := by
    intro σ₁ σ₂ h12 ann name ty hmem
    obtain ⟨⟨ty', hmem'⟩, -⟩ := LExpr.mem_freeVars_annotateFvars hmem
    simp [ValStore.fvarVal, h12 name ty' hmem']
  apply Option.ext
  intro v
  rw [LExpr.denoteEval_eq_some_iff, LExpr.denoteEval_eq_some_iff, hdef]
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨τ, hτ, hg, rfl⟩
    refine ⟨τ, hann ▸ hτ, hg, ?_⟩
    unfold LExpr.denoteEvalResult
    congr 1
    exact denote_ext_of_eq hann (hfv σ σ' h _) _ _
  · rintro ⟨τ, hτ, hg, rfl⟩
    refine ⟨τ, hann.symm ▸ hτ, hg, ?_⟩
    unfold LExpr.denoteEvalResult
    congr 1
    exact denote_ext_of_eq hann.symm (hfv σ' σ (fun x ty hx => (h x ty hx).symm) _) _ _

omit [DecidableEq T.IDMeta] in
/-- Denotations of equal expressions are heterogeneously equal. -/
private theorem denote_heq_of_eq {tc : TyConstrInterp} {op : OpInterp tc} {fv : FreeVarVal T tc}
    {vt : TyVarVal} {e₁ e₂ : LExpr T.mono} {τ : LMonoTy} (he : e₁ = e₂)
    (h₁ : e₁.HasTypeA [] τ) (h₂ : e₂.HasTypeA [] τ) :
    HEq (LExpr.denote tc op fv vt .nil e₁ τ h₁) (LExpr.denote tc op fv vt .nil e₂ τ h₂) := by
  subst he; rfl

/-- Two semantic values under one interpretation are equal when their sorts are equal and
their contents are heterogeneously equal. -/
theorem SemValue.mk_eq_mk {tc : TyConstrInterp} {s₁ s₂ : LSort} {v₁ : SortDenote tc s₁}
    {v₂ : SortDenote tc s₂} (hs : s₁ = s₂) (hv : HEq v₁ v₂) :
    SemValue.mk tc s₁ v₁ = SemValue.mk tc s₂ v₂ := by
  subst hs; cases hv; rfl

omit [DecidableEq T.IDMeta] in
/-- Reading a stored value at its own sort and interpretation returns it. -/
private theorem ValStore.fvarVal_heq {tc : TyConstrInterp} [TyConstrInterp.AllInhabited tc]
    {σ : ValStore T} {x : Identifier T.IDMeta} {s : LSort} {v : SortDenote tc s} {s' : LSort}
    (hx : σ x = some ⟨tc, s, v⟩) (hs : s = s') :
    HEq (σ.fvarVal tc x s') v := by
  subst hs
  simp only [ValStore.fvarVal, hx, Option.bind_some]
  simp only [SemValue.read, and_self, ↓reduceDIte, Option.getD_some]
  exact cast_heq _ _

/-- A free variable evaluates to its stored value. -/
theorem LExpr.denoteEval_fvar {M : ModeledFactory T} {σ : ValStore T}
    {m : T.Metadata} {x : Identifier T.IDMeta} {ty : Option LMonoTy} {v : SemValue}
    (hx : σ x = some v) (hv : v.tc = M.model.tcInterp) :
    (LExpr.fvar m x ty : LExpr T.mono).denoteEval M σ = some v := by
  obtain ⟨vtc, vs, vv⟩ := v
  simp only at hv
  subst hv
  rw [LExpr.denoteEval_eq_some_iff]
  have hann : (LExpr.fvar m x ty : LExpr T.mono).annotateFvars σ.ann =
      .fvar m x (some vs.toMonoTy) := by
    simp [LExpr.annotateFvars, ValStore.ann, hx]
  have hy : ∀ y ∈ LExpr.LExpr.getVars (LExpr.fvar m x ty : LExpr T.mono), y = x := by
    simp [getVars_eq_freeVars_idents, LExpr.freeVars]
  refine ⟨fun y hy' => ⟨_, (hy y hy') ▸ hx, rfl⟩, vs.toMonoTy, hann ▸ .fvar,
    LSort.toMonoTy_isGround vs, ?_⟩
  unfold LExpr.denoteEvalResult
  symm
  apply SemValue.mk_eq_mk (LSort.toMonoTy_substTyVars _ _)
  refine (denote_heq_of_eq hann _ .fvar).trans ?_
  rw [denote_fvar]
  letI := M.model.allInhabited
  exact ValStore.fvarVal_heq hx (LSort.toMonoTy_substTyVars _ _).symm

/-- A free variable that is unbound does not evaluate. -/
theorem LExpr.denoteEval_fvar_none {M : ModeledFactory T} {σ : ValStore T}
    {m : T.Metadata} {x : Identifier T.IDMeta} {ty : Option LMonoTy}
    (hx : σ x = none) :
    (LExpr.fvar m x ty : LExpr T.mono).denoteEval M σ = none := by
  apply Option.eq_none_iff_forall_ne_some.mpr
  intro v h
  obtain ⟨w, hw, -⟩ := LExpr.denoteEval_defines h x
      (by simp [getVars_eq_freeVars_idents, LExpr.freeVars])
  simp_all

/-- A Boolean literal evaluates to its value. -/
theorem LExpr.denoteEval_boolConst {M : ModeledFactory T} {σ : ValStore T}
    {m : T.Metadata} {b : Bool} :
    (LExpr.const m (.boolConst b) : LExpr T.mono).denoteEval M σ =
      some (SemValue.ofBool M.model.tcInterp b) := by
  rw [LExpr.denoteEval_eq_some_iff]
  exact ⟨fun y hy => by simp [getVars_eq_freeVars_idents, LExpr.freeVars] at hy, .bool, .const, rfl,
      rfl⟩

/-- Evaluation is monotone under store extension. -/
theorem LExpr.denoteEval_mono {M : ModeledFactory T} {σ σ' : ValStore T}
    {e : LExpr T.mono} {v : SemValue}
    (hext : ∀ x w, σ x = some w → σ' x = some w) (h : e.denoteEval M σ = some v) :
    e.denoteEval M σ' = some v := by
  rw [← h]
  symm
  apply LExpr.denoteEval_congr
  intro x ty hx
  obtain ⟨w, hw, -⟩ := LExpr.denoteEval_defines h x
    (LExpr.mem_getVars_of_mem_freeVars hx)
  rw [hw, hext x w hw]

end Laws

/-! ### Renaming free variables -/

/-- Renaming free variables does not change the result of type checking. -/
theorem typeCheck_mapFvarNames (g : Identifier T.IDMeta → Identifier T.IDMeta)
    (Δ : List LMonoTy) (e : LExpr T.mono) :
    LExpr.typeCheck Δ (e.mapFvarNames g) = LExpr.typeCheck Δ e := by
  induction e generalizing Δ with
  | const | op | bvar => rfl
  | fvar _ _ ty => cases ty <;> rfl
  | abs _ _ ty _ ih => cases ty <;> simp [LExpr.mapFvarNames, LExpr.typeCheck, ih]
  | quant _ _ _ ty _ _ ih1 ih2 => cases ty <;> simp [LExpr.mapFvarNames, LExpr.typeCheck, ih1, ih2]
  | app _ _ _ ih1 ih2 => simp [LExpr.mapFvarNames, LExpr.typeCheck, ih1, ih2]
  | ite _ _ _ _ ih1 ih2 ih3 => simp [LExpr.mapFvarNames, LExpr.typeCheck, ih1, ih2, ih3]
  | eq _ _ _ ih1 ih2 => simp [LExpr.mapFvarNames, LExpr.typeCheck, ih1, ih2]

/-- Renaming free variables preserves a typing derivation. -/
theorem LExpr.HasTypeA_mapFvarNames (g : Identifier T.IDMeta → Identifier T.IDMeta)
    {Δ : List LMonoTy} {e : LExpr T.mono} {τ : LMonoTy} (h : e.HasTypeA Δ τ) :
    (e.mapFvarNames g).HasTypeA Δ τ := by
  induction h with
  | const => exact .const
  | op => exact .op
  | fvar => exact .fvar
  | bvar h => exact .bvar h
  | abs _ ih => exact .abs ih
  | quant _ _ ih1 ih2 => exact .quant ih1 ih2
  | app _ _ ih1 ih2 => exact .app ih1 ih2
  | ite _ _ _ ih1 ih2 ih3 => exact .ite ih1 ih2 ih3
  | eq _ _ ih1 ih2 => exact .eq ih1 ih2

/-- Renaming the free variables of `e` by `g` and reading them through `fv` denotes
like reading `e`'s free variables through `fv ∘ g`. -/
private theorem Denotes.mapFvarNames {tc : TyConstrInterp} {op : OpInterp tc} {fv : FreeVarVal T tc}
    {vt : TyVarVal} (g : Identifier T.IDMeta → Identifier T.IDMeta)
    {Δ : List LMonoTy} {bv : BVarVal tc vt Δ} {e : LExpr T.mono} {τ : LMonoTy}
    {h : e.HasTypeA Δ τ} {v : TyDenote tc vt τ}
    (hd : Denotes tc op (fun x s => fv (g x) s) vt bv e τ h v) :
    Denotes tc op fv vt bv (e.mapFvarNames g) τ (LExpr.HasTypeA_mapFvarNames g h) v := by
  induction hd with
  | const => exact .const _
  | op => exact .op _
  | fvar => exact .fvar _
  | bvar => exact .bvar _
  | abs _ _ ih => exact .abs _ ih
  | app _ _ _ ih1 ih2 => exact .app _ ih1 ih2
  | ite_true _ _ _ ih1 ih2 => exact .ite_true _ ih1 ih2
  | ite_false _ _ _ ih1 ih2 => exact .ite_false _ ih1 ih2
  | eq_true _ _ _ ih1 ih2 => exact .eq_true _ ih1 ih2
  | eq_false _ _ _ hne ih1 ih2 => exact .eq_false _ ih1 ih2 hne
  | quant_all_true _ _ ih => exact .quant_all_true _ ih
  | quant_all_false _ w _ ih => exact .quant_all_false _ w ih
  | quant_exist_true _ w _ ih => exact .quant_exist_true _ w ih
  | quant_exist_false _ _ ih => exact .quant_exist_false _ ih

/-- The denotation of a renamed expression is the denotation of the original under the
valuation read through the renaming. -/
private theorem denote_mapFvarNames {tc : TyConstrInterp} {op : OpInterp tc} {fv : FreeVarVal T tc}
    {vt : TyVarVal} (g : Identifier T.IDMeta → Identifier T.IDMeta)
    {Δ : List LMonoTy} (bv : BVarVal tc vt Δ) {e : LExpr T.mono} {τ : LMonoTy}
    (h : e.HasTypeA Δ τ) (h' : (e.mapFvarNames g).HasTypeA Δ τ) :
    LExpr.denote tc op fv vt bv (e.mapFvarNames g) τ h' =
      LExpr.denote tc op (fun x s => fv (g x) s) vt bv e τ h :=
  (Denotes_denote (Denotes.mapFvarNames g (denote_Denotes _ _ _ _ bv e τ h))).symm

/-- The free variables of a renamed expression are the renamed free variables, with their
annotations. -/
theorem LExpr.freeVars_mapFvarNames [DecidableEq T.IDMeta]
    (g : Identifier T.IDMeta → Identifier T.IDMeta) (e : LExpr T.mono) :
    (e.mapFvarNames g).freeVars = e.freeVars.map fun p => (g p.1, p.2) := by
  induction e <;> simp_all [mapFvarNames, LExpr.freeVars]

/-- Annotating a renamed expression is renaming the expression annotated through the renaming. -/
theorem LExpr.annotateFvars_mapFvarNames (g : Identifier T.IDMeta → Identifier T.IDMeta)
    (ann : Identifier T.IDMeta → Option LMonoTy) (e : LExpr T.mono) :
    (e.mapFvarNames g).annotateFvars ann = (e.annotateFvars (ann ∘ g)).mapFvarNames g := by
  induction e <;> simp_all [mapFvarNames, annotateFvars]

/-- **Renaming law.**  Evaluating `e` with its free variables renamed by `g` is
evaluating `e` in the store read through `g`. -/
theorem LExpr.denoteEval_mapFvarNames [DecidableEq T.IDMeta] {M : ModeledFactory T}
    {σ : ValStore T} (g : Identifier T.IDMeta → Identifier T.IDMeta) (e : LExpr T.mono) :
    (e.mapFvarNames g).denoteEval M σ = e.denoteEval M (σ ∘ g) := by
  have hann : (e.mapFvarNames g).annotateFvars σ.ann =
      (e.annotateFvars (ValStore.ann (σ ∘ g))).mapFvarNames g :=
    LExpr.annotateFvars_mapFvarNames g σ.ann e
  have hdef : σ.Defines M.model.tcInterp (e.mapFvarNames g) ↔
      ValStore.Defines (σ ∘ g) M.model.tcInterp e := by
    simp only [ValStore.Defines, getVars_eq_freeVars_idents, LExpr.freeVars_mapFvarNames,
      List.map_map, List.mem_map, Function.comp_apply, Prod.exists, exists_and_right,
      forall_exists_index,
      and_imp, exists_eq_right]
    constructor
    · intro h x ty hx; exact h (g x) x ty hx rfl
    · intro h x y ty hy hgx; subst hgx; exact h y ty hy
  apply Option.ext
  intro v
  rw [LExpr.denoteEval_eq_some_iff, LExpr.denoteEval_eq_some_iff, hdef]
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨τ, hτ, hg, rfl⟩
    have hτ' : (e.annotateFvars (ValStore.ann (σ ∘ g))).HasTypeA [] τ := by
      rw [hann] at hτ
      exact (LExpr.HasTypeA_iff_typeCheck _ _ _).mpr
        (by rw [← LExpr.HasTypeA_to_typeCheck hτ]; exact (typeCheck_mapFvarNames g _ _).symm)
    refine ⟨τ, hτ', hg, ?_⟩
    unfold LExpr.denoteEvalResult
    congr 1
    refine eq_of_heq ((denote_heq_of_eq hann hτ (LExpr.HasTypeA_mapFvarNames g hτ')).trans ?_)
    rw [denote_mapFvarNames g .nil hτ']
    rfl
  · rintro ⟨τ, hτ, hg, rfl⟩
    have hτ' : ((e.mapFvarNames g).annotateFvars σ.ann).HasTypeA [] τ :=
      hann ▸ LExpr.HasTypeA_mapFvarNames g hτ
    refine ⟨τ, hτ', hg, ?_⟩
    unfold LExpr.denoteEvalResult
    congr 1
    symm
    refine eq_of_heq ((denote_heq_of_eq hann hτ' (LExpr.HasTypeA_mapFvarNames g hτ)).trans ?_)
    rw [denote_mapFvarNames g .nil hτ]
    rfl

/-! ### Substituting free variables -/

section Subst

/-- Substituting free variables by expressions whose type checks match their annotations does
not change the result of type checking. -/
theorem LExpr.typeCheck_substFvarsBy (look : Identifier T.IDMeta → Option (LExpr T.mono)) :
    ∀ (e : LExpr T.mono) (Δ : List LMonoTy),
      (∀ x tyo r, (x, tyo) ∈ e.freeVars → look x = some r → ∀ Δ', LExpr.typeCheck Δ' r = tyo) →
      LExpr.typeCheck Δ (e.substFvarsBy look) = LExpr.typeCheck Δ e := by
  intro e
  induction e with
  | const | op | bvar => intros; rfl
  | fvar m x tyo =>
    intro Δ hl
    simp only [LExpr.substFvarsBy]
    cases h : look x with
    | none => rfl
    | some r =>
      simp only
      rw [hl x tyo r (by simp [LExpr.freeVars]) h Δ]
      cases tyo <;> rfl
  | abs m n ty b ih =>
    intro Δ hl
    cases ty with
    | none => rfl
    | some aty =>
      simp only [LExpr.substFvarsBy, LExpr.typeCheck]
      rw [ih _ (fun x tyo r hx => hl x tyo r (by simpa [LExpr.freeVars] using hx))]
  | quant m k n ty tr b ihtr ihb =>
    intro Δ hl
    simp only [LExpr.freeVars, List.mem_append] at hl
    cases ty with
    | none => rfl
    | some qty =>
      simp only [LExpr.substFvarsBy, LExpr.typeCheck]
      rw [ihtr _ (fun x tyo r hx => hl x tyo r (.inl hx)),
          ihb _ (fun x tyo r hx => hl x tyo r (.inr hx))]
  | app m f a ihf iha =>
    intro Δ hl
    simp only [LExpr.freeVars, List.mem_append] at hl
    simp only [LExpr.substFvarsBy, LExpr.typeCheck]
    rw [ihf _ (fun x tyo r hx => hl x tyo r (.inl hx)),
        iha _ (fun x tyo r hx => hl x tyo r (.inr hx))]
  | ite m c t e ihc iht ihe =>
    intro Δ hl
    simp only [LExpr.freeVars, List.mem_append] at hl
    simp only [LExpr.substFvarsBy, LExpr.typeCheck]
    rw [ihc _ (fun x tyo r hx => hl x tyo r (.inl (.inl hx))),
      iht _ (fun x tyo r hx => hl x tyo r (.inl (.inr hx))),
      ihe _ (fun x tyo r hx => hl x tyo r (.inr hx))]
  | eq m a b iha ihb =>
    intro Δ hl
    simp only [LExpr.freeVars, List.mem_append] at hl
    simp only [LExpr.substFvarsBy, LExpr.typeCheck]
    rw [iha _ (fun x tyo r hx => hl x tyo r (.inl hx)),
        ihb _ (fun x tyo r hx => hl x tyo r (.inr hx))]

/-- Substituting free variables by expressions whose type checks match their annotations
preserves a typing derivation. -/
theorem LExpr.HasTypeA_substFvarsBy {look : Identifier T.IDMeta → Option (LExpr T.mono)}
    {e : LExpr T.mono} {Δ : List LMonoTy} {τ : LMonoTy}
    (hl : ∀ x tyo r, (x, tyo) ∈ e.freeVars → look x = some r → ∀ Δ', LExpr.typeCheck Δ' r = tyo)
    (h : e.HasTypeA Δ τ) : (e.substFvarsBy look).HasTypeA Δ τ :=
  LExpr.typeCheck_to_HasTypeA
    ((LExpr.typeCheck_substFvarsBy look e Δ hl).trans (LExpr.HasTypeA_to_typeCheck h))

/-- Transport a denotation along an equality of expressions. -/
private theorem Denotes.of_expr_eq {tc : TyConstrInterp} {op : OpInterp tc} {vt : TyVarVal}
    {fv : FreeVarVal T tc} {Δ : List LMonoTy} {bv : BVarVal tc vt Δ} {e₁ e₂ : LExpr T.mono}
    {τ : LMonoTy} {h₁ : e₁.HasTypeA Δ τ} {h₂ : e₂.HasTypeA Δ τ} {v : TyDenote tc vt τ}
    (he : e₁ = e₂) (hd : Denotes tc op fv vt bv e₂ τ h₂ v) : Denotes tc op fv vt bv e₁ τ h₁ v := by
  subst he; exact hd

/-- Substituting, for free variables, expressions that denote the variables' values
preserves the denotation. -/
private theorem Denotes.substFvarsBy {tc : TyConstrInterp} {op : OpInterp tc} {vt : TyVarVal}
    {fv fv' : FreeVarVal T tc} (look : Identifier T.IDMeta → Option (LExpr T.mono))
    {Δ : List LMonoTy} {bv : BVarVal tc vt Δ} {e : LExpr T.mono} {τ : LMonoTy}
    {h : e.HasTypeA Δ τ} {v : TyDenote tc vt τ}
    (hd : Denotes tc op fv vt bv e τ h v) :
    (∀ x tyo r, (x, tyo) ∈ e.freeVars → look x = some r → ∀ Δ', LExpr.typeCheck Δ' r = tyo) →
    (∀ x ty r, (x, some ty) ∈ e.freeVars → look x = some r →
      ∀ Δ' (bv' : BVarVal tc vt Δ') (hr : r.HasTypeA Δ' ty),
        Denotes tc op fv' vt bv' r ty hr (fv x (ty.substTyVars vt))) →
    (∀ x ty, (x, some ty) ∈ e.freeVars → look x = none →
      fv' x (ty.substTyVars vt) = fv x (ty.substTyVars vt)) →
    ∀ h' : (e.substFvarsBy look).HasTypeA Δ τ,
      Denotes tc op fv' vt bv (e.substFvarsBy look) τ h' v := by
  induction hd with
  | const => intros; exact .const _
  | op => intros; exact .op _
  | bvar => intros; exact .bvar _
  | fvar bv' =>
    rename_i m x ty _
    intro _ hden hfv h'
    cases hl : look x with
    | none =>
      have he : (LExpr.fvar m x (some ty) : LExpr T.mono).substFvarsBy look = .fvar m x
          (some ty) := by
        simp [LExpr.substFvarsBy, hl]
      refine Denotes.of_expr_eq he ?_ (h₂ := .fvar)
      rw [← hfv x ty (by simp [LExpr.freeVars]) hl]
      exact .fvar _
    | some r =>
      have he : (LExpr.fvar m x (some ty) : LExpr T.mono).substFvarsBy look = r := by
        simp [LExpr.substFvarsBy, hl]
      exact Denotes.of_expr_eq he (hden x ty r (by simp [LExpr.freeVars]) hl _ _ (he ▸ h'))
  | abs bv' hbody ih =>
    rename_i m name aty rty body h_body _ f
    intro htc hden hfv h'
    have htc' : ∀ x tyo r, (x, tyo) ∈ body.freeVars → look x = some r → ∀ Δ',
        LExpr.typeCheck Δ' r = tyo := fun x tyo r hx => htc x tyo r
            (by simpa [LExpr.freeVars] using hx)
    exact .abs _ fun x => ih x htc'
        (fun y ty r hy => hden y ty r (by simpa [LExpr.freeVars] using hy))
      (fun y ty hy => hfv y ty (by simpa [LExpr.freeVars] using hy))
      (LExpr.HasTypeA_substFvarsBy htc' h_body)
  | app bv' hfn harg ihfn iharg =>
    rename_i m fn arg aty τ h_fn h_arg _ vf va
    intro htc hden hfv h'
    simp only [LExpr.freeVars, List.mem_append] at htc hden hfv
    have htc1 : ∀ x tyo r, (x, tyo) ∈ fn.freeVars → look x = some r → ∀ Δ',
        LExpr.typeCheck Δ' r = tyo := fun x tyo r hx => htc x tyo r (.inl hx)
    have htc2 : ∀ x tyo r, (x, tyo) ∈ arg.freeVars → look x = some r → ∀ Δ',
        LExpr.typeCheck Δ' r = tyo := fun x tyo r hx => htc x tyo r (.inr hx)
    exact .app _
      (ihfn htc1 (fun x ty r hx => hden x ty r (.inl hx)) (fun x ty hx => hfv x ty (.inl hx))
        (LExpr.HasTypeA_substFvarsBy htc1 h_fn))
      (iharg htc2 (fun x ty r hx => hden x ty r (.inr hx)) (fun x ty hx => hfv x ty (.inr hx))
        (LExpr.HasTypeA_substFvarsBy htc2 h_arg))
  | ite_true bv' hc ht ihc iht =>
    rename_i m c t e τ h_c h_t _ v
    intro htc hden hfv h'
    simp only [LExpr.freeVars, List.mem_append] at htc hden hfv
    have htc1 : ∀ x tyo r, (x, tyo) ∈ c.freeVars → look x = some r → ∀ Δ',
        LExpr.typeCheck Δ' r = tyo := fun x tyo r hx => htc x tyo r (.inl (.inl hx))
    have htc2 : ∀ x tyo r, (x, tyo) ∈ t.freeVars → look x = some r → ∀ Δ',
        LExpr.typeCheck Δ' r = tyo := fun x tyo r hx => htc x tyo r (.inl (.inr hx))
    exact .ite_true _
      (ihc htc1 (fun x ty r hx => hden x ty r (.inl (.inl hx)))
        (fun x ty hx => hfv x ty (.inl (.inl hx))) (LExpr.HasTypeA_substFvarsBy htc1 h_c))
      (iht htc2 (fun x ty r hx => hden x ty r (.inl (.inr hx)))
        (fun x ty hx => hfv x ty (.inl (.inr hx))) (LExpr.HasTypeA_substFvarsBy htc2 h_t))
  | ite_false bv' hc he ihc ihe =>
    rename_i m c t e τ h_c h_e _ v
    intro htc hden hfv h'
    simp only [LExpr.freeVars, List.mem_append] at htc hden hfv
    have htc1 : ∀ x tyo r, (x, tyo) ∈ c.freeVars → look x = some r → ∀ Δ',
        LExpr.typeCheck Δ' r = tyo := fun x tyo r hx => htc x tyo r (.inl (.inl hx))
    have htc3 : ∀ x tyo r, (x, tyo) ∈ e.freeVars → look x = some r → ∀ Δ',
        LExpr.typeCheck Δ' r = tyo := fun x tyo r hx => htc x tyo r (.inr hx)
    exact .ite_false _
      (ihc htc1 (fun x ty r hx => hden x ty r (.inl (.inl hx)))
        (fun x ty hx => hfv x ty (.inl (.inl hx))) (LExpr.HasTypeA_substFvarsBy htc1 h_c))
      (ihe htc3 (fun x ty r hx => hden x ty r (.inr hx))
        (fun x ty hx => hfv x ty (.inr hx)) (LExpr.HasTypeA_substFvarsBy htc3 h_e))
  | eq_true bv' h1 h2 ih1 ih2 =>
    rename_i m e1 e2 τ' h_1 h_2 _ v
    intro htc hden hfv h'
    simp only [LExpr.freeVars, List.mem_append] at htc hden hfv
    have htc1 : ∀ x tyo r, (x, tyo) ∈ e1.freeVars → look x = some r → ∀ Δ',
        LExpr.typeCheck Δ' r = tyo := fun x tyo r hx => htc x tyo r (.inl hx)
    have htc2 : ∀ x tyo r, (x, tyo) ∈ e2.freeVars → look x = some r → ∀ Δ',
        LExpr.typeCheck Δ' r = tyo := fun x tyo r hx => htc x tyo r (.inr hx)
    exact .eq_true _
      (ih1 htc1 (fun x ty r hx => hden x ty r (.inl hx)) (fun x ty hx => hfv x ty (.inl hx))
        (LExpr.HasTypeA_substFvarsBy htc1 h_1))
      (ih2 htc2 (fun x ty r hx => hden x ty r (.inr hx)) (fun x ty hx => hfv x ty (.inr hx))
        (LExpr.HasTypeA_substFvarsBy htc2 h_2))
  | eq_false bv' h1 h2 hne ih1 ih2 =>
    rename_i m e1 e2 τ' h_1 h_2 _ v1 v2
    intro htc hden hfv h'
    simp only [LExpr.freeVars, List.mem_append] at htc hden hfv
    have htc1 : ∀ x tyo r, (x, tyo) ∈ e1.freeVars → look x = some r → ∀ Δ',
        LExpr.typeCheck Δ' r = tyo := fun x tyo r hx => htc x tyo r (.inl hx)
    have htc2 : ∀ x tyo r, (x, tyo) ∈ e2.freeVars → look x = some r → ∀ Δ',
        LExpr.typeCheck Δ' r = tyo := fun x tyo r hx => htc x tyo r (.inr hx)
    exact .eq_false _
      (ih1 htc1 (fun x ty r hx => hden x ty r (.inl hx)) (fun x ty hx => hfv x ty (.inl hx))
        (LExpr.HasTypeA_substFvarsBy htc1 h_1))
      (ih2 htc2 (fun x ty r hx => hden x ty r (.inr hx)) (fun x ty hx => hfv x ty (.inr hx))
        (LExpr.HasTypeA_substFvarsBy htc2 h_2)) hne
  | quant_all_true bv' hall ih =>
    rename_i m name qty tr body h_body _
    intro htc hden hfv h'
    simp only [LExpr.freeVars, List.mem_append] at htc hden hfv
    have htc2 : ∀ x tyo r, (x, tyo) ∈ body.freeVars → look x = some r → ∀ Δ',
        LExpr.typeCheck Δ' r = tyo := fun x tyo r hx => htc x tyo r (.inr hx)
    exact .quant_all_true _ fun x => ih x htc2 (fun y ty r hy => hden y ty r (.inr hy))
      (fun y ty hy => hfv y ty (.inr hy)) (LExpr.HasTypeA_substFvarsBy htc2 h_body)
  | quant_all_false bv' w hbody ih =>
    rename_i m name qty tr body h_body _
    intro htc hden hfv h'
    simp only [LExpr.freeVars, List.mem_append] at htc hden hfv
    have htc2 : ∀ x tyo r, (x, tyo) ∈ body.freeVars → look x = some r → ∀ Δ',
        LExpr.typeCheck Δ' r = tyo := fun x tyo r hx => htc x tyo r (.inr hx)
    exact .quant_all_false _ w (ih htc2 (fun y ty r hy => hden y ty r (.inr hy))
      (fun y ty hy => hfv y ty (.inr hy)) (LExpr.HasTypeA_substFvarsBy htc2 h_body))
  | quant_exist_true bv' w hbody ih =>
    rename_i m name qty tr body h_body _
    intro htc hden hfv h'
    simp only [LExpr.freeVars, List.mem_append] at htc hden hfv
    have htc2 : ∀ x tyo r, (x, tyo) ∈ body.freeVars → look x = some r → ∀ Δ',
        LExpr.typeCheck Δ' r = tyo := fun x tyo r hx => htc x tyo r (.inr hx)
    exact .quant_exist_true _ w (ih htc2 (fun y ty r hy => hden y ty r (.inr hy))
      (fun y ty hy => hfv y ty (.inr hy)) (LExpr.HasTypeA_substFvarsBy htc2 h_body))
  | quant_exist_false bv' hall ih =>
    rename_i m name qty tr body h_body _
    intro htc hden hfv h'
    simp only [LExpr.freeVars, List.mem_append] at htc hden hfv
    have htc2 : ∀ x tyo r, (x, tyo) ∈ body.freeVars → look x = some r → ∀ Δ',
        LExpr.typeCheck Δ' r = tyo := fun x tyo r hx => htc x tyo r (.inr hx)
    exact .quant_exist_false _ fun x => ih x htc2 (fun y ty r hy => hden y ty r (.inr hy))
      (fun y ty hy => hfv y ty (.inr hy)) (LExpr.HasTypeA_substFvarsBy htc2 h_body)

/-- Substituting free variables by expressions that denote their values (and leaving the
others at the same values) preserves the denotation. -/
theorem denote_substFvarsBy {tc : TyConstrInterp} {op : OpInterp tc} {vt : TyVarVal}
    {fv fv' : FreeVarVal T tc} (look : Identifier T.IDMeta → Option (LExpr T.mono))
    {Δ : List LMonoTy} (bv : BVarVal tc vt Δ) {e : LExpr T.mono} {τ : LMonoTy}
    (htc : ∀ x tyo r, (x, tyo) ∈ e.freeVars → look x = some r → ∀ Δ',
      LExpr.typeCheck Δ' r = tyo)
    (hden : ∀ x ty r, (x, some ty) ∈ e.freeVars → look x = some r →
      ∀ Δ' (bv' : BVarVal tc vt Δ') (hr : r.HasTypeA Δ' ty),
        LExpr.denote tc op fv' vt bv' r ty hr = fv x (ty.substTyVars vt))
    (hfv : ∀ x ty, (x, some ty) ∈ e.freeVars → look x = none →
      fv' x (ty.substTyVars vt) = fv x (ty.substTyVars vt))
    (h : e.HasTypeA Δ τ) (h' : (e.substFvarsBy look).HasTypeA Δ τ) :
    LExpr.denote tc op fv' vt bv (e.substFvarsBy look) τ h' = LExpr.denote tc op fv vt bv e τ h :=
  (Denotes_denote (Denotes.substFvarsBy look (denote_Denotes _ _ _ _ bv e τ h) htc
    (fun x ty r hx hl Δ' bv' hr =>
      (hden x ty r hx hl Δ' bv' hr) ▸ denote_Denotes _ _ _ _ bv' r ty hr)
    hfv h')).symm

/-- Annotating a substituted expression is substituting, by the annotated replacements, into
the expression annotated on its unsubstituted variables. -/
theorem LExpr.annotateFvars_substFvarsBy (look : Identifier T.IDMeta → Option (LExpr T.mono))
    (ann ann' : Identifier T.IDMeta → Option LMonoTy) (e : LExpr T.mono)
    (h : ∀ x ty, (x, ty) ∈ e.freeVars → look x = none → ann' x = ann x) :
    (e.substFvarsBy look).annotateFvars ann' =
      (e.annotateFvars ann).substFvarsBy fun x => (look x).map (·.annotateFvars ann') := by
  induction e with
  | const | op | bvar => rfl
  | fvar m x ty =>
    cases hl : look x with
    | none =>
      simp [LExpr.substFvarsBy, LExpr.annotateFvars, hl, h x ty (by simp [LExpr.freeVars]) hl]
    | some r => simp [LExpr.substFvarsBy, LExpr.annotateFvars, hl]
  | abs m n ty b ih =>
    simp only [LExpr.substFvarsBy, LExpr.annotateFvars]
    rw [ih (fun x ty hx => h x ty (by simpa [LExpr.freeVars] using hx))]
  | quant m k n ty tr b ihtr ihb =>
    simp only [LExpr.freeVars, List.mem_append] at h
    simp only [LExpr.substFvarsBy, LExpr.annotateFvars]
    rw [ihtr (fun x ty hx => h x ty (.inl hx)), ihb (fun x ty hx => h x ty (.inr hx))]
  | app m f a ihf iha =>
    simp only [LExpr.freeVars, List.mem_append] at h
    simp only [LExpr.substFvarsBy, LExpr.annotateFvars]
    rw [ihf (fun x ty hx => h x ty (.inl hx)), iha (fun x ty hx => h x ty (.inr hx))]
  | ite m c t e ihc iht ihe =>
    simp only [LExpr.freeVars, List.mem_append] at h
    simp only [LExpr.substFvarsBy, LExpr.annotateFvars]
    rw [ihc (fun x ty hx => h x ty (.inl (.inl hx))), iht (fun x ty hx => h x ty (.inl (.inr hx))),
      ihe (fun x ty hx => h x ty (.inr hx))]
  | eq m a b iha ihb =>
    simp only [LExpr.freeVars, List.mem_append] at h
    simp only [LExpr.substFvarsBy, LExpr.annotateFvars]
    rw [iha (fun x ty hx => h x ty (.inl hx)), ihb (fun x ty hx => h x ty (.inr hx))]

/-- A free variable of a substitution result is an unsubstituted free variable, or a free
variable of a substituted expression. -/
theorem LExpr.mem_freeVars_substFvarsBy {look : Identifier T.IDMeta → Option (LExpr T.mono)}
    {e : LExpr T.mono} {x : Identifier T.IDMeta} {ty : Option LMonoTy}
    (hx : (x, ty) ∈ (e.substFvarsBy look).freeVars) :
    ((x, ty) ∈ e.freeVars ∧ look x = none) ∨
      ∃ y tyy r, (y, tyy) ∈ e.freeVars ∧ look y = some r ∧ (x, ty) ∈ r.freeVars := by
  induction e with
  | const | op | bvar => simp [LExpr.substFvarsBy, LExpr.freeVars] at hx
  | fvar m y tyy =>
    cases hl : look y with
    | none =>
      simp only [LExpr.substFvarsBy, hl] at hx
      simp only [LExpr.freeVars, List.mem_singleton, Prod.mk.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      exact .inl ⟨by simp [LExpr.freeVars], hl⟩
    | some r =>
      simp only [LExpr.substFvarsBy, hl] at hx
      exact .inr ⟨y, tyy, r, by simp [LExpr.freeVars], hl, hx⟩
  | abs m n ty' b ih =>
    simp only [LExpr.substFvarsBy, LExpr.freeVars] at hx ⊢
    exact ih hx
  | quant m k n ty' tr b ihtr ihb =>
    simp only [LExpr.substFvarsBy, LExpr.freeVars, List.mem_append] at hx ⊢
    rcases hx with hx | hx
    · rcases ihtr hx with ⟨h1, h2⟩ | ⟨y, t, r, h1, h2, h3⟩
      · exact .inl ⟨.inl h1, h2⟩
      · exact .inr ⟨y, t, r, .inl h1, h2, h3⟩
    · rcases ihb hx with ⟨h1, h2⟩ | ⟨y, t, r, h1, h2, h3⟩
      · exact .inl ⟨.inr h1, h2⟩
      · exact .inr ⟨y, t, r, .inr h1, h2, h3⟩
  | app m f a ihf iha =>
    simp only [LExpr.substFvarsBy, LExpr.freeVars, List.mem_append] at hx ⊢
    rcases hx with hx | hx
    · rcases ihf hx with ⟨h1, h2⟩ | ⟨y, t, r, h1, h2, h3⟩
      · exact .inl ⟨.inl h1, h2⟩
      · exact .inr ⟨y, t, r, .inl h1, h2, h3⟩
    · rcases iha hx with ⟨h1, h2⟩ | ⟨y, t, r, h1, h2, h3⟩
      · exact .inl ⟨.inr h1, h2⟩
      · exact .inr ⟨y, t, r, .inr h1, h2, h3⟩
  | ite m c t e ihc iht ihe =>
    simp only [LExpr.substFvarsBy, LExpr.freeVars, List.mem_append] at hx ⊢
    rcases hx with (hx | hx) | hx
    · rcases ihc hx with ⟨h1, h2⟩ | ⟨y, t, r, h1, h2, h3⟩
      · exact .inl ⟨.inl (.inl h1), h2⟩
      · exact .inr ⟨y, t, r, .inl (.inl h1), h2, h3⟩
    · rcases iht hx with ⟨h1, h2⟩ | ⟨y, t', r, h1, h2, h3⟩
      · exact .inl ⟨.inl (.inr h1), h2⟩
      · exact .inr ⟨y, t', r, .inl (.inr h1), h2, h3⟩
    · rcases ihe hx with ⟨h1, h2⟩ | ⟨y, t', r, h1, h2, h3⟩
      · exact .inl ⟨.inr h1, h2⟩
      · exact .inr ⟨y, t', r, .inr h1, h2, h3⟩
  | eq m a b iha ihb =>
    simp only [LExpr.substFvarsBy, LExpr.freeVars, List.mem_append] at hx ⊢
    rcases hx with hx | hx
    · rcases iha hx with ⟨h1, h2⟩ | ⟨y, t, r, h1, h2, h3⟩
      · exact .inl ⟨.inl h1, h2⟩
      · exact .inr ⟨y, t, r, .inl h1, h2, h3⟩
    · rcases ihb hx with ⟨h1, h2⟩ | ⟨y, t, r, h1, h2, h3⟩
      · exact .inl ⟨.inr h1, h2⟩
      · exact .inr ⟨y, t, r, .inr h1, h2, h3⟩

/-- An unsubstituted free variable remains free after substitution; a free variable of
a substituted expression becomes free. -/
theorem LExpr.mem_freeVars_substFvarsBy_of {look : Identifier T.IDMeta → Option (LExpr T.mono)}
    {e : LExpr T.mono} {x : Identifier T.IDMeta} {ty : Option LMonoTy}
    (hx : (x, ty) ∈ e.freeVars) :
    (look x = none → (x, ty) ∈ (e.substFvarsBy look).freeVars) ∧
      ∀ r, look x = some r → ∀ p ∈ r.freeVars, p ∈ (e.substFvarsBy look).freeVars := by
  induction e with
  | const | op | bvar => simp [LExpr.freeVars] at hx
  | fvar m y tyy =>
    simp only [LExpr.freeVars, List.mem_singleton, Prod.mk.injEq] at hx
    obtain ⟨rfl, rfl⟩ := hx
    refine ⟨fun hl => by simp [LExpr.substFvarsBy, hl, LExpr.freeVars], fun r hl p hp => ?_⟩
    simpa [LExpr.substFvarsBy, hl] using hp
  | abs m n ty' b ih =>
    simp only [LExpr.substFvarsBy, LExpr.freeVars] at hx ⊢
    exact ih hx
  | quant m k n ty' tr b ihtr ihb =>
    simp only [LExpr.substFvarsBy, LExpr.freeVars, List.mem_append] at hx ⊢
    rcases hx with hx | hx
    · exact ⟨fun hl => .inl ((ihtr hx).1 hl), fun r hl p hp => .inl ((ihtr hx).2 r hl p hp)⟩
    · exact ⟨fun hl => .inr ((ihb hx).1 hl), fun r hl p hp => .inr ((ihb hx).2 r hl p hp)⟩
  | app m f a ihf iha =>
    simp only [LExpr.substFvarsBy, LExpr.freeVars, List.mem_append] at hx ⊢
    rcases hx with hx | hx
    · exact ⟨fun hl => .inl ((ihf hx).1 hl), fun r hl p hp => .inl ((ihf hx).2 r hl p hp)⟩
    · exact ⟨fun hl => .inr ((iha hx).1 hl), fun r hl p hp => .inr ((iha hx).2 r hl p hp)⟩
  | ite m c t e ihc iht ihe =>
    simp only [LExpr.substFvarsBy, LExpr.freeVars, List.mem_append] at hx ⊢
    rcases hx with (hx | hx) | hx
    · exact ⟨fun hl => .inl (.inl ((ihc hx).1 hl)),
        fun r hl p hp => .inl (.inl ((ihc hx).2 r hl p hp))⟩
    · exact ⟨fun hl => .inl (.inr ((iht hx).1 hl)),
        fun r hl p hp => .inl (.inr ((iht hx).2 r hl p hp))⟩
    · exact ⟨fun hl => .inr ((ihe hx).1 hl), fun r hl p hp => .inr ((ihe hx).2 r hl p hp)⟩
  | eq m a b iha ihb =>
    simp only [LExpr.substFvarsBy, LExpr.freeVars, List.mem_append] at hx ⊢
    rcases hx with hx | hx
    · exact ⟨fun hl => .inl ((iha hx).1 hl), fun r hl p hp => .inl ((iha hx).2 r hl p hp)⟩
    · exact ⟨fun hl => .inr ((ihb hx).1 hl), fun r hl p hp => .inr ((ihb hx).2 r hl p hp)⟩

end Subst

section EvalSubst

variable [DecidableEq T.IDMeta]

/-- **Substitution law.**  Substituting, for free variables of `e`, variables that hold the
same values or Boolean literals equal to their values, preserves evaluation, when the
remaining free variables have the same values. -/
theorem LExpr.denoteEval_substFvarsBy {M : ModeledFactory T} {σ σ' : ValStore T}
    (look : Identifier T.IDMeta → Option (LExpr T.mono)) (e : LExpr T.mono)
    (hlook : ∀ x ty r, (x, ty) ∈ e.freeVars → look x = some r →
      (∃ m y tyo, r = .fvar m y tyo ∧ σ' y = σ x) ∨
      (∃ m b, r = .const m (.boolConst b) ∧ σ x = some (SemValue.ofBool M.model.tcInterp b)))
    (hrest : ∀ x ty, (x, ty) ∈ e.freeVars → look x = none → σ' x = σ x) :
    (e.substFvarsBy look).denoteEval M σ' = e.denoteEval M σ := by
  have hdef : σ'.Defines M.model.tcInterp (e.substFvarsBy look) ↔ σ.Defines M.model.tcInterp e := by
    simp only [ValStore.Defines, getVars_eq_freeVars_idents, List.mem_map, Prod.exists,
      exists_and_right, exists_eq_right, forall_exists_index]
    constructor
    · intro hd x ty hx
      cases hl : look x with
      | none =>
        rw [← hrest x ty hx hl]
        exact hd x ty ((LExpr.mem_freeVars_substFvarsBy_of hx).1 hl)
      | some r =>
        rcases hlook x ty r hx hl with ⟨m, y, tyo, rfl, hy⟩ | ⟨m, b, rfl, hb⟩
        · rw [← hy]
          exact hd y tyo ((LExpr.mem_freeVars_substFvarsBy_of hx).2 _ hl _
            (by simp [LExpr.freeVars]))
        · exact ⟨_, hb, rfl⟩
    · intro hd x ty hx
      rcases LExpr.mem_freeVars_substFvarsBy hx with ⟨hx', hl⟩ | ⟨y, tyy, r, hy, hl, hr⟩
      · rw [hrest x ty hx' hl]; exact hd x ty hx'
      · rcases hlook y tyy r hy hl with ⟨m, z, tyo, rfl, hz⟩ | ⟨m, b, rfl, -⟩
        · simp only [LExpr.freeVars, List.mem_singleton, Prod.mk.injEq] at hr
          obtain ⟨rfl, -⟩ := hr
          rw [hz]; exact hd y tyy hy
        · simp [LExpr.freeVars] at hr
  apply Option.ext
  intro v
  rw [LExpr.denoteEval_eq_some_iff, LExpr.denoteEval_eq_some_iff, hdef]
  apply and_congr_right
  intro hd
  -- The annotated substitution result is the substitution into the annotated expression.
  let look' : Identifier T.IDMeta → Option (LExpr T.mono) :=
    fun x => (look x).map (·.annotateFvars σ'.ann)
  have hann :
      (e.substFvarsBy look).annotateFvars σ'.ann = (e.annotateFvars σ.ann).substFvarsBy look' :=
    LExpr.annotateFvars_substFvarsBy look σ.ann σ'.ann e fun x ty hx hl => by
      simp [ValStore.ann, hrest x ty hx hl]
  -- Every free variable of `e` is bound in `σ`.
  have hbound : ∀ x ty, (x, ty) ∈ e.freeVars → ∃ w, σ x = some w ∧ w.tc = M.model.tcInterp :=
    fun x ty hx => hd x (LExpr.mem_getVars_of_mem_freeVars hx)
  -- What substituted occurrences in the annotated expression look like.
  have hocc : ∀ x tyo r', (x, tyo) ∈ (e.annotateFvars σ.ann).freeVars → look' x = some r' →
      ∃ w, σ x = some w ∧ w.tc = M.model.tcInterp ∧ tyo = some w.sort.toMonoTy ∧
        ((∃ m y, r' = .fvar m y (some w.sort.toMonoTy) ∧ σ' y = σ x) ∨
          ∃ m b, r' = .const m (.boolConst b) ∧ w = SemValue.ofBool M.model.tcInterp b) := by
    intro x tyo r' hx hl
    obtain ⟨⟨ty', hx'⟩, hann'⟩ := LExpr.mem_freeVars_annotateFvars hx
    obtain ⟨w, hw, hwtc⟩ := hbound x ty' hx'
    have htyo : tyo = some w.sort.toMonoTy := hann' _ (by simp [ValStore.ann, hw])
    simp only [look', Option.map_eq_some_iff] at hl
    obtain ⟨r, hl, rfl⟩ := hl
    refine ⟨w, hw, hwtc, htyo, ?_⟩
    rcases hlook x ty' r hx' hl with ⟨m, y, tyo', rfl, hy⟩ | ⟨m, b, rfl, hb⟩
    · refine .inl ⟨m, y, ?_, hy⟩
      simp [LExpr.annotateFvars, ValStore.ann, hy, hw]
    · rw [hw] at hb
      exact .inr ⟨m, b, rfl, Option.some.inj hb⟩
  have htc : ∀ x tyo r', (x, tyo) ∈ (e.annotateFvars σ.ann).freeVars → look' x = some r' →
      ∀ Δ', LExpr.typeCheck Δ' r' = tyo := by
    intro x tyo r' hx hl Δ'
    obtain ⟨w, -, -, rfl, (⟨m, y, rfl, -⟩ | ⟨m, b, rfl, rfl⟩)⟩ := hocc x tyo r' hx hl <;> rfl
  have htyeq : LExpr.typeCheck [] ((e.substFvarsBy look).annotateFvars σ'.ann) =
      LExpr.typeCheck [] (e.annotateFvars σ.ann) := by
    rw [hann]; exact LExpr.typeCheck_substFvarsBy look' _ [] htc
  letI := M.model.allInhabited
  have hden : ∀ x ty r', (x, some ty) ∈ (e.annotateFvars σ.ann).freeVars → look' x = some r' →
      ∀ Δ' (bv' : BVarVal M.model.tcInterp M.tyVarVal Δ') (hr : r'.HasTypeA Δ' ty),
        LExpr.denote M.model.tcInterp M.model.opInterp (σ'.fvarVal M.model.tcInterp) M.tyVarVal
          bv' r' ty hr = σ.fvarVal M.model.tcInterp x (ty.substTyVars M.tyVarVal) := by
    intro x ty r' hx hl Δ' bv' hr
    obtain ⟨w, hw, hwtc, hty, hr'⟩ := hocc x _ r' hx hl
    simp only [Option.some.injEq] at hty
    subst hty
    rcases hr' with ⟨m, y, rfl, hy⟩ | ⟨m, b, rfl, rfl⟩
    · rw [denote_fvar]
      simp [ValStore.fvarVal, hy]
    · have : LExpr.denote M.model.tcInterp M.model.opInterp (σ'.fvarVal M.model.tcInterp)
          M.tyVarVal bv' (.const m (.boolConst b))
              (SemValue.ofBool M.model.tcInterp b).sort.toMonoTy
          hr = b := denote_boolConst _ _ _ _ bv' hr
      rw [this]
      show b = ((σ x).bind (·.read M.model.tcInterp LSort.bool)).getD default
      rw [hw, Option.bind_some, SemValue.read_ofBool]
      rfl
  have hfv : ∀ x ty, (x, some ty) ∈ (e.annotateFvars σ.ann).freeVars → look' x = none →
      σ'.fvarVal M.model.tcInterp x (ty.substTyVars M.tyVarVal) =
        σ.fvarVal M.model.tcInterp x (ty.substTyVars M.tyVarVal) := by
    intro x ty hx hl
    obtain ⟨⟨ty', hx'⟩, -⟩ := LExpr.mem_freeVars_annotateFvars hx
    simp only [look', Option.map_eq_none_iff] at hl
    simp [ValStore.fvarVal, hrest x ty' hx' hl]
  constructor
  · rintro ⟨τ, hτ, hg, rfl⟩
    have hτ' : (e.annotateFvars σ.ann).HasTypeA [] τ := LExpr.typeCheck_to_HasTypeA
      (htyeq ▸ LExpr.HasTypeA_to_typeCheck hτ)
    refine ⟨τ, hτ', hg, ?_⟩
    unfold LExpr.denoteEvalResult
    congr 1
    refine eq_of_heq ((denote_heq_of_eq hann hτ (LExpr.HasTypeA_substFvarsBy htc hτ')).trans ?_)
    exact heq_of_eq (denote_substFvarsBy look' .nil htc hden hfv hτ' _)
  · rintro ⟨τ, hτ, hg, rfl⟩
    have hτ' : ((e.substFvarsBy look).annotateFvars σ'.ann).HasTypeA [] τ :=
      LExpr.typeCheck_to_HasTypeA (htyeq.symm ▸ LExpr.HasTypeA_to_typeCheck hτ)
    refine ⟨τ, hτ', hg, ?_⟩
    unfold LExpr.denoteEvalResult
    congr 1
    symm
    refine eq_of_heq ((denote_heq_of_eq hann hτ' (LExpr.HasTypeA_substFvarsBy htc hτ)).trans ?_)
    exact heq_of_eq (denote_substFvarsBy look' .nil htc hden hfv hτ _)

end EvalSubst

/-! ### Compound expressions -/

section Compound

variable [DecidableEq T.IDMeta]

/-- A well-typed annotation at a ground type in a store binding every free variable
evaluates to its denotation. -/
theorem LExpr.denoteEval_of_hasTypeA {M : ModeledFactory T} {σ : ValStore T}
    {e : LExpr T.mono} {τ : LMonoTy} (hd : σ.Defines M.model.tcInterp e)
    (h : (e.annotateFvars σ.ann).HasTypeA [] τ) (hg : τ.IsGround) :
    e.denoteEval M σ = some (e.denoteEvalResult M σ τ h) :=
  LExpr.denoteEval_eq_some_iff.mpr ⟨hd, τ, h, hg, rfl⟩

/-- A store that binds every free variable of `e` binds those of an expression whose free
variables are among them. -/
theorem ValStore.Defines.mono {σ : ValStore T} {tc : TyConstrInterp} {e e' : LExpr T.mono}
    (hd : σ.Defines tc e) (h : ∀ x ty, (x, ty) ∈ e'.freeVars → ∃ ty', (x, ty') ∈ e.freeVars) :
    σ.Defines tc e' := by
  intro x hx
  simp only [getVars_eq_freeVars_idents, List.mem_map] at hx
  obtain ⟨⟨x', ty⟩, hx, rfl⟩ := hx
  obtain ⟨ty', hx'⟩ := h x' ty hx
  exact hd x' (LExpr.mem_getVars_of_mem_freeVars hx')

/-- A ground type is determined by its sort. -/
theorem LMonoTy.IsGround.eq_of_substTyVars_eq {τ₁ τ₂ : LMonoTy} {ρ : TyVarVal}
    (h₁ : τ₁.IsGround) (h₂ : τ₂.IsGround) (h : τ₁.substTyVars ρ = τ₂.substTyVars ρ) :
    τ₁ = τ₂ := by
  rw [← h₁, ← h₂, h₁.substTyVars_eq refTyVarVal ρ, h₂.substTyVars_eq refTyVarVal ρ, h]

/-- **Conditional law.**  A conditional evaluates exactly when its condition evaluates
to a Boolean and both branches evaluate to values of the same sort; it yields the
selected branch's value. -/
theorem LExpr.denoteEval_ite_iff {M : ModeledFactory T} {σ : ValStore T}
    {m : T.Metadata} {c t e : LExpr T.mono} {v : SemValue} :
    (LExpr.ite m c t e).denoteEval M σ = some v ↔
      ∃ b vt ve, c.denoteEval M σ = some (SemValue.ofBool M.model.tcInterp b) ∧
        t.denoteEval M σ = some vt ∧ e.denoteEval M σ = some ve ∧ vt.sort = ve.sort ∧
        v = if b then vt else ve := by
  letI := M.model.allInhabited
  have hsub : ∀ {d : LExpr T.mono}, (∀ x ty, (x, ty) ∈ d.freeVars →
      (x, ty) ∈ (LExpr.ite m c t e : LExpr T.mono).freeVars) →
      σ.Defines M.model.tcInterp (LExpr.ite m c t e) → σ.Defines M.model.tcInterp d :=
    fun hd' hd => hd.mono fun x ty hx => ⟨ty, hd' x ty hx⟩
  constructor
  · intro h
    obtain ⟨hd, τ, hτ, hg, rfl⟩ := LExpr.denoteEval_eq_some_iff.mp h
    obtain ⟨hc, ht, he⟩ := HasTypeA.ite_inv hτ
    have hdc := hsub (d := c) (fun x ty hx => by simp [LExpr.freeVars, hx]) hd
    have hdt := hsub (d := t) (fun x ty hx => by simp [LExpr.freeVars, hx]) hd
    have hde := hsub (d := e) (fun x ty hx => by simp [LExpr.freeVars, hx]) hd
    refine ⟨LExpr.denote M.model.tcInterp M.model.opInterp (σ.fvarVal M.model.tcInterp)
        M.tyVarVal .nil _ .bool hc, _, _, LExpr.denoteEval_of_hasTypeA hdc hc rfl,
      LExpr.denoteEval_of_hasTypeA hdt ht hg, LExpr.denoteEval_of_hasTypeA hde he hg, rfl, ?_⟩
    have hden := denote_Denotes M.model.tcInterp M.model.opInterp (σ.fvarVal M.model.tcInterp)
      M.tyVarVal .nil (c.annotateFvars σ.ann) .bool hc
    unfold LExpr.denoteEvalResult
    cases hb : (LExpr.denote M.model.tcInterp M.model.opInterp (σ.fvarVal M.model.tcInterp)
        M.tyVarVal .nil _ .bool hc : Bool)
    · rw [hb] at hden
      have hdenIte := Denotes_denote (Denotes.ite_false (h := hτ) .nil hden
        (denote_Denotes _ _ _ _ .nil _ _ he))
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact congrArg (SemValue.mk M.model.tcInterp _) hdenIte.symm
    · rw [hb] at hden
      have hdenIte := Denotes_denote (Denotes.ite_true (h := hτ) .nil hden
        (denote_Denotes _ _ _ _ .nil _ _ ht))
      simp only [↓reduceIte]
      exact congrArg (SemValue.mk M.model.tcInterp _) hdenIte.symm
  · rintro ⟨b, vt, ve, hc, ht, he, hs, rfl⟩
    obtain ⟨hdc, τc, hτc, hgc, hvc⟩ := LExpr.denoteEval_eq_some_iff.mp hc
    obtain ⟨hdt, τt, hτt, hgt, rfl⟩ := LExpr.denoteEval_eq_some_iff.mp ht
    obtain ⟨hde, τe, hτe, hge, rfl⟩ := LExpr.denoteEval_eq_some_iff.mp he
    have hτcb : τc = .bool := by
      have : τc.substTyVars M.tyVarVal = LSort.bool := by
        have := congrArg SemValue.sort hvc
        exact this.symm
      exact hgc.eq_of_substTyVars_eq rfl this
    subst hτcb
    have hτte : τt = τe := hgt.eq_of_substTyVars_eq hge hs
    subst hτte
    have hτ : ((LExpr.ite m c t e : LExpr T.mono).annotateFvars σ.ann).HasTypeA [] τt :=
      .ite hτc hτt hτe
    have hd : σ.Defines M.model.tcInterp (LExpr.ite m c t e) := by
      intro x hx
      simp only [getVars_eq_freeVars_idents, LExpr.freeVars, List.map_append, List.mem_append] at hx
      rcases hx with (hx | hx) | hx
      · exact hdc x (by rwa [getVars_eq_freeVars_idents])
      · exact hdt x (by rwa [getVars_eq_freeVars_idents])
      · exact hde x (by rwa [getVars_eq_freeVars_idents])
    rw [LExpr.denoteEval_of_hasTypeA hd hτ hgt]
    have hbv : (LExpr.denote M.model.tcInterp M.model.opInterp (σ.fvarVal M.model.tcInterp)
        M.tyVarVal .nil _ .bool hτc : Bool) = b := by
      unfold LExpr.denoteEvalResult SemValue.ofBool at hvc
      obtain ⟨-, -, hv⟩ := SemValue.mk.inj hvc
      exact (eq_of_heq hv).symm
    have hden := denote_Denotes M.model.tcInterp M.model.opInterp (σ.fvarVal M.model.tcInterp)
      M.tyVarVal .nil (c.annotateFvars σ.ann) .bool hτc
    rw [hbv] at hden
    unfold LExpr.denoteEvalResult
    cases b
    · have hdenIte := Denotes_denote (Denotes.ite_false (h := hτ) .nil hden
        (denote_Denotes _ _ _ _ .nil _ _ hτe))
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact congrArg (fun x => some (SemValue.mk M.model.tcInterp _ x)) hdenIte.symm
    · have hdenIte := Denotes_denote (Denotes.ite_true (h := hτ) .nil hden
        (denote_Denotes _ _ _ _ .nil _ _ hτt))
      simp only [↓reduceIte]
      exact congrArg (fun x => some (SemValue.mk M.model.tcInterp _ x)) hdenIte.symm

/-- An expression evaluates to the element `w` of a ground type `τ`'s sort exactly when its
annotation is well-typed at `τ` and denotes `w`. -/
theorem LExpr.denoteEval_eq_mk_iff {M : ModeledFactory T} {σ : ValStore T}
    {e : LExpr T.mono} {τ : LMonoTy} (hg : τ.IsGround)
    {w : SortDenote M.model.tcInterp (τ.substTyVars M.tyVarVal)} :
    e.denoteEval M σ = some ⟨M.model.tcInterp, τ.substTyVars M.tyVarVal, w⟩ ↔
      σ.Defines M.model.tcInterp e ∧ ∃ h : (e.annotateFvars σ.ann).HasTypeA [] τ,
        (letI := M.model.allInhabited
         LExpr.denote M.model.tcInterp M.model.opInterp (σ.fvarVal M.model.tcInterp)
          M.tyVarVal .nil _ τ h) = w := by
  rw [LExpr.denoteEval_eq_some_iff]
  apply and_congr_right
  intro _
  constructor
  · rintro ⟨τ', hτ', hg', hv⟩
    unfold LExpr.denoteEvalResult at hv
    obtain ⟨-, hs, hv⟩ := SemValue.mk.inj hv
    obtain rfl : τ' = τ := hg'.eq_of_substTyVars_eq hg hs.symm
    exact ⟨hτ', (eq_of_heq hv).symm⟩
  · rintro ⟨h, hw⟩
    refine ⟨τ, h, hg, ?_⟩
    unfold LExpr.denoteEvalResult
    rw [← hw]

/-- An expression evaluates to a Boolean exactly when its annotation is well-typed at
`bool` and denotes that Boolean. -/
theorem LExpr.denoteEval_eq_ofBool_iff {M : ModeledFactory T} {σ : ValStore T}
    {e : LExpr T.mono} {b : Bool} :
    e.denoteEval M σ = some (SemValue.ofBool M.model.tcInterp b) ↔
      σ.Defines M.model.tcInterp e ∧ ∃ h : (e.annotateFvars σ.ann).HasTypeA [] .bool,
        (letI := M.model.allInhabited
         LExpr.denote M.model.tcInterp M.model.opInterp (σ.fvarVal M.model.tcInterp)
          M.tyVarVal .nil _ .bool h : Bool) = b :=
  LExpr.denoteEval_eq_mk_iff (τ := .bool) rfl

/-- **Unary Boolean operator law.**  An operator annotated `bool → bool` applied to a
Boolean-valued argument evaluates to the operator's interpretation at the argument. -/
theorem LExpr.denoteEval_app_op_bool_iff {M : ModeledFactory T} {σ : ValStore T}
    {m m' : T.Metadata} {o : Identifier T.IDMeta} {e : LExpr T.mono} {b' : Bool} :
    (LExpr.app m (.op m' o (some (LMonoTy.arrow .bool .bool))) e).denoteEval M σ =
        some (SemValue.ofBool M.model.tcInterp b') ↔
      ∃ b, e.denoteEval M σ = some (SemValue.ofBool M.model.tcInterp b) ∧
        b' = (M.model.opInterp o.name (LSort.mkArrow .bool [.bool]) : Bool → Bool) b := by
  letI := M.model.allInhabited
  have hdef : σ.Defines M.model.tcInterp
      (LExpr.app m (.op m' o (some (LMonoTy.arrow .bool .bool))) e) ↔
      σ.Defines M.model.tcInterp e := by
    simp [ValStore.Defines, getVars_eq_freeVars_idents, LExpr.freeVars]
  rw [LExpr.denoteEval_eq_ofBool_iff, hdef]
  constructor
  · rintro ⟨hd, h, hb⟩
    obtain ⟨aty, hfn, harg⟩ := HasTypeA.app_inv h
    have : aty = .bool := by
      have := HasTypeA.op_inv hfn
      simp only [LMonoTy.arrow, LMonoTy.tcons.injEq, List.cons.injEq, and_true, true_and] at this
      exact this
    subst this
    refine ⟨_, LExpr.denoteEval_eq_ofBool_iff.mpr ⟨hd, harg, rfl⟩, ?_⟩
    rw [← hb]
    exact (Denotes_denote (Denotes.app (h := h) .nil (Denotes.op (h := hfn) .nil)
      (denote_Denotes M.model.tcInterp M.model.opInterp (σ.fvarVal M.model.tcInterp)
        M.tyVarVal .nil _ _ harg))).symm
  · rintro ⟨b, he, rfl⟩
    obtain ⟨hd, harg, hb⟩ := LExpr.denoteEval_eq_ofBool_iff.mp he
    have h : ((LExpr.app m (.op m' o (some (LMonoTy.arrow .bool .bool))) e).annotateFvars
        σ.ann).HasTypeA [] .bool := .app .op harg
    refine ⟨hd, h, ?_⟩
    have hden := denote_Denotes M.model.tcInterp M.model.opInterp (σ.fvarVal M.model.tcInterp)
      M.tyVarVal .nil _ _ harg
    have hdenApp := Denotes_denote (Denotes.app (h := h) .nil (Denotes.op (h := .op) .nil) hden)
    rw [← hb]
    exact hdenApp.symm

/-- **Binary operator law.**  An operator annotated `a → b → c`, at ground types, applied to
arguments of sorts `a` and `b` evaluates to a value of sort `c`. -/
theorem LExpr.denoteEval_app2_op {M : ModeledFactory T} {σ : ValStore T}
    {m m' m'' : T.Metadata} {o : Identifier T.IDMeta} {x y : LExpr T.mono} {a b c : LMonoTy}
    {vx vy : SemValue} (hga : a.IsGround) (hgb : b.IsGround) (hgc : c.IsGround)
    (hx : x.denoteEval M σ = some vx) (hxs : vx.sort = a.substTyVars M.tyVarVal)
    (hy : y.denoteEval M σ = some vy) (hys : vy.sort = b.substTyVars M.tyVarVal) :
    ∃ v, (LExpr.app m (.app m' (.op m'' o (some (LMonoTy.arrow a (LMonoTy.arrow b c)))) x)
        y).denoteEval
        M σ = some v ∧ v.sort = c.substTyVars M.tyVarVal := by
  obtain ⟨hdx, τx, hτx, hgx, rfl⟩ := LExpr.denoteEval_eq_some_iff.mp hx
  obtain ⟨hdy, τy, hτy, hgy, rfl⟩ := LExpr.denoteEval_eq_some_iff.mp hy
  have hτxa : τx = a := hgx.eq_of_substTyVars_eq hga hxs
  have hτyb : τy = b := hgy.eq_of_substTyVars_eq hgb hys
  subst hτxa hτyb
  have h : ((LExpr.app m (.app m' (.op m'' o (some (LMonoTy.arrow τx (LMonoTy.arrow τy c)))) x)
      y).annotateFvars
      σ.ann).HasTypeA [] c := .app (.app .op hτx) hτy
  have hd : σ.Defines M.model.tcInterp
      (LExpr.app m (.app m' (.op m'' o (some (LMonoTy.arrow τx (LMonoTy.arrow τy c)))) x) y) := by
    intro z hz
    simp only [getVars_eq_freeVars_idents, LExpr.freeVars, List.nil_append, List.map_append,
      List.mem_append] at hz
    rcases hz with hz | hz
    · exact hdx z (by rwa [getVars_eq_freeVars_idents])
    · exact hdy z (by rwa [getVars_eq_freeVars_idents])
  exact ⟨_, LExpr.denoteEval_of_hasTypeA hd h hgc, rfl⟩

/-- A literal evaluates to its value. -/
theorem LExpr.denoteEval_const {M : ModeledFactory T} {σ : ValStore T}
    {m : T.Metadata} {c : LConst} :
    (LExpr.const m c : LExpr T.mono).denoteEval M σ =
      some (SemValue.ofConst M.model.tcInterp c) := by
  rw [LExpr.denoteEval_eq_some_iff]
  exact ⟨fun y hy => by simp [getVars_eq_freeVars_idents, LExpr.freeVars] at hy, c.ty, .const,
    by cases c <;> rfl, by cases c <;> rfl⟩

/-- An integer literal evaluates to its value. -/
theorem LExpr.denoteEval_intConst {M : ModeledFactory T} {σ : ValStore T}
    {m : T.Metadata} {i : Int} :
    (LExpr.const m (.intConst i) : LExpr T.mono).denoteEval M σ =
      some (SemValue.ofInt M.model.tcInterp i) :=
  LExpr.denoteEval_const

/-- **Equality law.**  An equality of two expressions evaluating to the same value
evaluates to `true`. -/
theorem LExpr.denoteEval_eq_true {M : ModeledFactory T} {σ : ValStore T}
    {m : T.Metadata} {a b : LExpr T.mono} {v : SemValue}
    (ha : a.denoteEval M σ = some v) (hb : b.denoteEval M σ = some v) :
    (LExpr.eq m a b).denoteEval M σ = some (SemValue.ofBool M.model.tcInterp true) := by
  letI := M.model.allInhabited
  obtain ⟨hda, τa, hτa, hga, rfl⟩ := LExpr.denoteEval_eq_some_iff.mp ha
  obtain ⟨hdb, τb, hτb, hgb, hvb⟩ := LExpr.denoteEval_eq_some_iff.mp hb
  have hτ : τb = τa :=
    hgb.eq_of_substTyVars_eq hga (congrArg SemValue.sort hvb).symm
  subst hτ
  have hden : LExpr.denote M.model.tcInterp M.model.opInterp (σ.fvarVal M.model.tcInterp)
        M.tyVarVal .nil (a.annotateFvars σ.ann) τb hτa =
      LExpr.denote M.model.tcInterp M.model.opInterp (σ.fvarVal M.model.tcInterp)
        M.tyVarVal .nil (b.annotateFvars σ.ann) τb hτb := by
    unfold LExpr.denoteEvalResult at hvb
    exact eq_of_heq (SemValue.mk.inj hvb).2.2
  have hd : σ.Defines M.model.tcInterp (LExpr.eq m a b) := by
    intro x hx
    simp only [getVars_eq_freeVars_idents, LExpr.freeVars, List.map_append, List.mem_append] at hx
    rcases hx with hx | hx
    · exact hda x (by rwa [getVars_eq_freeVars_idents])
    · exact hdb x (by rwa [getVars_eq_freeVars_idents])
  have h : ((LExpr.eq m a b : LExpr T.mono).annotateFvars σ.ann).HasTypeA [] .bool :=
    .eq hτa hτb
  exact LExpr.denoteEval_eq_ofBool_iff.mpr ⟨hd, h, denote_eq_true .nil hτa hτb h hden⟩

/-- **Disequality law.**  An equality of two expressions evaluating to distinct values of the
same sort evaluates to `false`. -/
theorem LExpr.denoteEval_eq_false {M : ModeledFactory T} {σ : ValStore T}
    {m : T.Metadata} {a b : LExpr T.mono} {va vb : SemValue}
    (ha : a.denoteEval M σ = some va) (hb : b.denoteEval M σ = some vb)
    (hs : va.sort = vb.sort) (hne : va ≠ vb) :
    (LExpr.eq m a b).denoteEval M σ = some (SemValue.ofBool M.model.tcInterp false) := by
  letI := M.model.allInhabited
  obtain ⟨hda, τa, hτa, hga, rfl⟩ := LExpr.denoteEval_eq_some_iff.mp ha
  obtain ⟨hdb, τb, hτb, hgb, rfl⟩ := LExpr.denoteEval_eq_some_iff.mp hb
  have hτ : τb = τa := hgb.eq_of_substTyVars_eq hga hs.symm
  subst hτ
  have hden : LExpr.denote M.model.tcInterp M.model.opInterp (σ.fvarVal M.model.tcInterp)
        M.tyVarVal .nil (a.annotateFvars σ.ann) τb hτa ≠
      LExpr.denote M.model.tcInterp M.model.opInterp (σ.fvarVal M.model.tcInterp)
        M.tyVarVal .nil (b.annotateFvars σ.ann) τb hτb := by
    intro h
    apply hne
    unfold LExpr.denoteEvalResult
    rw [h]
  have hd : σ.Defines M.model.tcInterp (LExpr.eq m a b) := by
    intro x hx
    simp only [getVars_eq_freeVars_idents, LExpr.freeVars, List.map_append, List.mem_append] at hx
    rcases hx with hx | hx
    · exact hda x (by rwa [getVars_eq_freeVars_idents])
    · exact hdb x (by rwa [getVars_eq_freeVars_idents])
  have h : ((LExpr.eq m a b : LExpr T.mono).annotateFvars σ.ann).HasTypeA [] .bool :=
    .eq hτa hτb
  exact LExpr.denoteEval_eq_ofBool_iff.mpr ⟨hd, h, denote_eq_false .nil hτa hτb h hden⟩

/-- An expression evaluates to the integer `i` exactly when its annotation is
well-typed at `int` and denotes `i`. -/
theorem LExpr.denoteEval_eq_ofInt_iff {M : ModeledFactory T} {σ : ValStore T}
    {e : LExpr T.mono} {i : Int} :
    e.denoteEval M σ = some (SemValue.ofInt M.model.tcInterp i) ↔
      σ.Defines M.model.tcInterp e ∧ ∃ h : (e.annotateFvars σ.ann).HasTypeA [] .int,
        (letI := M.model.allInhabited
         LExpr.denote M.model.tcInterp M.model.opInterp (σ.fvarVal M.model.tcInterp)
          M.tyVarVal .nil _ .int h : Int) = i :=
  LExpr.denoteEval_eq_mk_iff (τ := .int) rfl

/-- **Binary operator law.**  An operator annotated `a → b → c`, at ground types, applied
to arguments with values of sorts `a` and `b` evaluates to the operator's interpretation
at the two values. -/
theorem LExpr.denoteEval_app2_op_val {M : ModeledFactory T} {σ : ValStore T}
    {m m' m'' : T.Metadata} {o : Identifier T.IDMeta} {x y : LExpr T.mono} {a b c : LMonoTy}
    (ha : a.IsGround) (hb : b.IsGround) (hc : c.IsGround)
    {va : SortDenote M.model.tcInterp (a.substTyVars M.tyVarVal)}
    {vb : SortDenote M.model.tcInterp (b.substTyVars M.tyVarVal)}
    (hx : x.denoteEval M σ = some ⟨M.model.tcInterp, a.substTyVars M.tyVarVal, va⟩)
    (hy : y.denoteEval M σ = some ⟨M.model.tcInterp, b.substTyVars M.tyVarVal, vb⟩) :
    (LExpr.app m (.app m' (.op m'' o (some (LMonoTy.arrow a (LMonoTy.arrow b c)))) x)
        y).denoteEval M σ =
      some ⟨M.model.tcInterp, c.substTyVars M.tyVarVal,
        (M.model.opInterp o.name
            ((LMonoTy.arrow a (LMonoTy.arrow b c)).substTyVars M.tyVarVal)
          : SortDenote M.model.tcInterp (a.substTyVars M.tyVarVal) →
            SortDenote M.model.tcInterp (b.substTyVars M.tyVarVal) →
            SortDenote M.model.tcInterp (c.substTyVars M.tyVarVal)) va vb⟩ := by
  letI := M.model.allInhabited
  obtain ⟨hdx, τx, hτx, hgx, hvx⟩ := LExpr.denoteEval_eq_some_iff.mp hx
  obtain ⟨hdy, τy, hτy, hgy, hvy⟩ := LExpr.denoteEval_eq_some_iff.mp hy
  obtain rfl : τx = a := hgx.eq_of_substTyVars_eq ha (congrArg SemValue.sort hvx).symm
  obtain rfl : τy = b := hgy.eq_of_substTyVars_eq hb (congrArg SemValue.sort hvy).symm
  have hax : LExpr.denote M.model.tcInterp M.model.opInterp (σ.fvarVal M.model.tcInterp)
      M.tyVarVal .nil (x.annotateFvars σ.ann) τx hτx = va := by
    unfold LExpr.denoteEvalResult at hvx
    exact (eq_of_heq (SemValue.mk.inj hvx).2.2).symm
  have hby : LExpr.denote M.model.tcInterp M.model.opInterp (σ.fvarVal M.model.tcInterp)
      M.tyVarVal .nil (y.annotateFvars σ.ann) τy hτy = vb := by
    unfold LExpr.denoteEvalResult at hvy
    exact (eq_of_heq (SemValue.mk.inj hvy).2.2).symm
  have hop' : LExpr.HasTypeA [] (LExpr.op m'' o (some (LMonoTy.arrow τx (LMonoTy.arrow τy c))) :
      LExpr T.mono) (.arrow τx (.arrow τy c)) := .op
  have happ' : LExpr.HasTypeA [] (LExpr.app m' (.op m'' o
      (some (LMonoTy.arrow τx (LMonoTy.arrow τy c)))) (x.annotateFvars σ.ann))
      (.arrow τy c) := .app hop' hτx
  have h' : LExpr.HasTypeA [] (LExpr.app m (.app m' (.op m'' o
      (some (LMonoTy.arrow τx (LMonoTy.arrow τy c)))) (x.annotateFvars σ.ann))
      (y.annotateFvars σ.ann)) c := .app happ' hτy
  have hd : σ.Defines M.model.tcInterp
      (LExpr.app m (.app m' (.op m'' o (some (LMonoTy.arrow τx (LMonoTy.arrow τy c)))) x) y) := by
    intro z hz
    simp only [getVars_eq_freeVars_idents, LExpr.freeVars, List.nil_append, List.map_append,
      List.mem_append] at hz
    rcases hz with hz | hz
    · exact hdx z (by rwa [getVars_eq_freeVars_idents])
    · exact hdy z (by rwa [getVars_eq_freeVars_idents])
  rw [LExpr.denoteEval_of_hasTypeA hd h' hc]
  unfold LExpr.denoteEvalResult
  congr 2
  show LExpr.denote M.model.tcInterp M.model.opInterp (σ.fvarVal M.model.tcInterp) M.tyVarVal
    .nil _ c h' = _
  rw [denote_app .nil happ' hτy h', denote_app .nil hop' hτx happ', denote_op, hax, hby]

/-- **Binary integer operator law.**  An operator annotated `int → int → c`, at a ground
result type `c`, applied to two integer-valued arguments evaluates to the operator's
interpretation at the two integers. -/
theorem LExpr.denoteEval_app2_op_int {M : ModeledFactory T} {σ : ValStore T}
    {m m' m'' : T.Metadata} {o : Identifier T.IDMeta} {x y : LExpr T.mono} {c : LMonoTy}
    (hc : c.IsGround) {a b : Int}
    (hx : x.denoteEval M σ = some (SemValue.ofInt M.model.tcInterp a))
    (hy : y.denoteEval M σ = some (SemValue.ofInt M.model.tcInterp b)) :
    (LExpr.app m (.app m' (.op m'' o (some (LMonoTy.arrow .int (LMonoTy.arrow .int c)))) x)
        y).denoteEval M σ =
      some ⟨M.model.tcInterp, c.substTyVars M.tyVarVal,
        (M.model.opInterp o.name (LSort.mkArrow (c.substTyVars M.tyVarVal) [.int, .int])
          : Int → Int → SortDenote M.model.tcInterp (c.substTyVars M.tyVarVal)) a b⟩ :=
  LExpr.denoteEval_app2_op_val (a := .int) (b := .int) rfl rfl hc hx hy

/-- A well-typed value (`isValue`) at a ground type `τ` evaluates, in every store, to one
semantic value of the model's interpretation whose sort is `τ`. -/
theorem LExpr.denoteEval_of_isValue {M : ModeledFactory T} {v : LExpr T.mono} {τ : LMonoTy}
    (hv : LExpr.isValue M.factory v = true) (hT : v.HasTypeA [] τ) (hg : τ.IsGround) :
    ∃ sv : SemValue, sv.tc = M.model.tcInterp ∧ sv.sort.toMonoTy = τ ∧
      ∀ σ : ValStore T, v.denoteEval M σ = some sv := by
  have hfv : v.freeVars = [] := by
    have h := isValue_getVars_nil M.factory v hv
    rw [getVars_eq_freeVars_idents, List.map_eq_nil_iff] at h
    exact h
  let σ₀ : ValStore T := fun _ => none
  have hd : σ₀.Defines M.model.tcInterp v := fun x hx => by
    rw [getVars_eq_freeVars_idents, hfv] at hx
    cases hx
  have hann : v.annotateFvars σ₀.ann = v := by
    have : σ₀.ann = fun _ => none := rfl
    rw [this, LExpr.annotateFvars_none]
  have hT' : (v.annotateFvars σ₀.ann).HasTypeA [] τ := by rw [hann]; exact hT
  refine ⟨v.denoteEvalResult M σ₀ τ hT', rfl, ?_, fun σ => ?_⟩
  · show (τ.substTyVars M.tyVarVal).toMonoTy = τ
    rw [hg.substTyVars_eq M.tyVarVal refTyVarVal]
    exact hg
  rw [LExpr.denoteEval_congr v (σ' := σ₀) (fun x ty hx => by simp [hfv] at hx)]
  exact LExpr.denoteEval_of_hasTypeA hd hT' hg

end Compound

end -- public section

end Lambda
