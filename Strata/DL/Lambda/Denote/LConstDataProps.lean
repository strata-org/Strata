/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Lambda.LConstData
public import Strata.DL.Lambda.Denote.LExprDenoteConsts
import all Strata.DL.Lambda.LConstData
import all Strata.DL.Lambda.LExpr
import all Strata.DL.Lambda.LSort
import all Strata.DL.Lambda.Denote.LExprDenote
import Strata.DL.Lambda.Denote.LExprDenoteTySubst
import all Strata.DL.Lambda.FactoryProps

/-! # Denotations of datatype values and constructor applications

The conversions of `Strata.DL.Lambda.LConstData` keep denotations, in every interpretation:

- `LConst.denote_toLExpr` — the expression of a well-typed constant (`LConst.toLExpr`) has its
  type and denotes it;
- `LExpr.toConst?_sound` — the constant an expression stands for (`LExpr.toConst?`) has the
  expression's type and denotation;
- `LConst.eqlIn_sound` — in an interpretation whose constructors are disjoint and injective
  (`ConstrInterpConsistent`), a decided `LConst.eqlIn` is the equality of the values.
-/

namespace Lambda

public section

variable {T : LExprParams}

/-! ### Sorts of signatures -/

/-- A function applied to an argument, heterogeneously: equal functions applied to equal
    arguments, across equal domain and codomain types, give equal results. -/
private theorem heq_app {α α' β β' : Type} (hα : α = α') (hβ : β = β') {f : α → β} {g : α' → β'}
    {x : α} {y : α'} (hf : HEq f g) (hx : HEq x y) : HEq (f x) (g y) := by
  subst hα hβ; cases hf; cases hx; rfl

/-- The types naming a list of sorts denote those sorts under every type-variable valuation. -/
private theorem map_toMonoTy_substTyVars (vt : TyVarVal) (as : List LSort) :
    (as.map (·.toMonoTy)).map (LMonoTy.substTyVars vt) = as := by
  induction as <;> simp_all [LSort.toMonoTy_substTyVars]

/-- The type naming a function sort is the iterated arrow of the types naming its sorts. -/
private theorem LSort.toMonoTy_mkArrow (r : LSort) :
    ∀ as : List LSort, (LSort.mkArrow r as).toMonoTy = LMonoTy.mkArrow' r.toMonoTy (as.map (·.toMonoTy))
  | [] => rfl
  | a :: as => by
    simp only [LSort.mkArrow, LSort.toMonoTy, LSort.toMonoTy.map, List.map_cons, LMonoTy.mkArrow',
      LMonoTy.arrow, LSort.toMonoTy_mkArrow r as]

/-- The ground signature `as → r` denotes the function sort `LSort.mkArrow r as`. -/
private theorem substTyVars_sig (vt : TyVarVal) (r : LSort) :
    ∀ as : List LSort, LMonoTy.substTyVars vt (LMonoTy.mkArrow' r.toMonoTy (as.map (·.toMonoTy))) =
      LSort.mkArrow r as
  | [] => LSort.toMonoTy_substTyVars vt r
  | a :: as => by
    simp only [List.map_cons, LMonoTy.mkArrow', LMonoTy.arrow, LMonoTy.substTyVars,
      LMonoTy.substTyVars.map, LSort.toMonoTy_substTyVars, substTyVars_sig vt r as, LSort.mkArrow]

/-- The arguments a datatype value is well typed with are well typed. -/
private theorem wt_of_wtArgs : ∀ {as : List LSort} {es : List LConst},
    LConst.wtArgs as es = true → ∀ e ∈ es, e.wt = true
  | [], [], _, _, he => nomatch he
  | _ :: _, e :: es, h, e', he => by
    simp only [LConst.wtArgs, Bool.and_eq_true] at h
    rcases List.mem_cons.mp he with rfl | he
    · exact h.1.1
    · exact wt_of_wtArgs h.2 e' he
  | [], _ :: _, h, _, _ | _ :: _, [], h, _, _ => by simp [LConst.wtArgs] at h

/-! ### Denotations of constants and their values -/

/-- Values of one constant at equal sorts are heterogeneously equal. -/
private theorem constVal_heq {tc : TyConstrInterp} {op : OpInterp tc} {c : LConst} :
    ∀ {s₁ s₂ : LSort} (_ : s₁ = s₂) {y : SortDenote tc s₁} {x : SortDenote tc s₂},
      constVal tc op s₁ c = some y → constVal tc op s₂ c = some x → HEq y x := by
  intro s₁ s₂ hs y x h₁ h₂
  subst hs
  obtain rfl := Option.some.inj (h₁.symm.trans h₂)
  rfl

/-- A well-typed constant's denotation is its value at its sort. -/
private theorem heq_denoteConst {tc : TyConstrInterp} {op : OpInterp tc} (vt : TyVarVal)
    {c : LConst} {s : LSort} {x : SortDenote tc s} (hw : c.wt = true)
    (h : constVal tc op s c = some x) : HEq (denoteConst tc op vt c) x :=
  constVal_heq (by rw [LConst.ty_of_wt hw, LSort.toMonoTy_substTyVars]; exact constVal_sort h)
    (constVal_denoteConst vt hw) h

/-- Denotations of one expression at equal types are heterogeneously equal. -/
private theorem denote_heq_of_ty {tc : TyConstrInterp} {op : OpInterp tc} {fv : FreeVarVal T tc}
    {vt : TyVarVal} {e : LExpr T.mono} {τ τ' : LMonoTy} (hτ : τ = τ') (h : LExpr.HasTypeA [] e τ)
    (h' : LExpr.HasTypeA [] e τ') :
    HEq (LExpr.denote tc op fv vt .nil e τ h) (LExpr.denote tc op fv vt .nil e τ' h') := by
  subst hτ; rfl

/-! ### The expression of a constant -/

mutual
/-- **The expression of a constant denotes the constant.** The expression of a well-typed
    constant (`LConst.toLExpr`) has the constant's type, and denotes what the constant denotes in
    every interpretation. -/
theorem LConst.denote_toLExpr [Inhabited T.IDMeta] (tc : TyConstrInterp) (op : OpInterp tc)
    (fv : FreeVarVal T tc) (vt : TyVarVal) (md : T.Metadata) :
    ∀ (c : LConst), c.wt = true → ∃ h : LExpr.HasTypeA [] (c.toLExpr md : LExpr T.mono) c.ty,
      LExpr.denote tc op fv vt .nil (c.toLExpr md) c.ty h = denoteConst tc op vt c
  | .dataConst n as s ⟨es⟩, hw => by
    have hw' := hw
    simp only [LConst.wt, Bool.and_eq_true] at hw'
    obtain ⟨vs, hvs⟩ := Option.isSome_iff_exists.mp (constValArgs_isSome tc op as es hw'.2)
    have hcv : constVal tc op s (.dataConst n as s ⟨es⟩) =
        some (SortDenote.applyArgs tc (op n (LSort.mkArrow s as)) vs) := by
      rw [constVal_dataConst n as s es hw'.1, hvs]; rfl
    have hty : (LConst.dataConst n as s ⟨es⟩).ty = s.toMonoTy := by
      rw [LConst.ty_of_wt hw]; rfl
    have hop : HEq (LExpr.denote tc op fv vt .nil
        (.op md ⟨n, default⟩ (some (LMonoTy.mkArrow' s.toMonoTy (as.map (·.toMonoTy)))) :
          LExpr T.mono) _ .op) (op n (LSort.mkArrow s as)) := by
      rw [← Denotes_denote (.op .nil)]
      have hsort : ∀ {s₁ s₂ : LSort}, s₁ = s₂ → HEq (op n s₁) (op n s₂) := by
        intro _ _ h; subst h; rfl
      exact hsort (substTyVars_sig vt s as)
    obtain ⟨h, hd⟩ := LConst.denote_toLExprApp tc op fv vt md as es vs s _ .op _ hop hvs hw'.2
    have hdef : (LConst.dataConst n as s ⟨es⟩).toLExpr md = LConst.toLExprApp md
        (.op md ⟨n, default⟩ (some (LMonoTy.mkArrow' s.toMonoTy (as.map (·.toMonoTy))))) es := rfl
    rw [hdef]
    refine ⟨hty ▸ h, eq_of_heq ((denote_heq_of_ty hty _ h).trans
      (hd.trans (heq_denoteConst vt hw hcv).symm))⟩
  | .intConst _, hw | .strConst _, hw | .rationalConst _, hw | .bitvecConst _ _, hw
  | .boolConst _, hw | .mapConst .., hw | .sequenceConst .., hw => ⟨.const hw, rfl⟩
/-- The expression of `f` applied to the constants `es`, whose values at the argument sorts `as`
    are `vs`, denotes the denotation of `f` applied to `vs`. -/
private theorem LConst.denote_toLExprApp [Inhabited T.IDMeta] (tc : TyConstrInterp) (op : OpInterp tc)
    (fv : FreeVarVal T tc) (vt : TyVarVal) (md : T.Metadata) :
    ∀ (as : List LSort) (es : List LConst) (vs : HList (SortDenote tc) as) (s : LSort)
      (f : LExpr T.mono)
      (hf : LExpr.HasTypeA [] f (LMonoTy.mkArrow' s.toMonoTy (as.map (·.toMonoTy))))
      (F₀ : SortDenote tc (LSort.mkArrow s as)),
      HEq (LExpr.denote tc op fv vt .nil f _ hf) F₀ →
      constValArgs tc op as es = some vs → LConst.wtArgs as es = true →
      ∃ h : LExpr.HasTypeA [] (LConst.toLExprApp md f es) s.toMonoTy,
        HEq (LExpr.denote tc op fv vt .nil (LConst.toLExprApp md f es) s.toMonoTy h)
          (SortDenote.applyArgs tc F₀ vs)
  | [], [], .nil, _, _, hf, _, hF, _, _ => ⟨hf, hF⟩
  | a :: as, e :: r, .cons x xs, s, f, hf, F₀, hF, hvs, hwt => by
    simp only [constValArgs] at hvs
    split at hvs
    · rename_i y ys hx hxs
      simp only [Option.some.injEq, HList.cons.injEq] at hvs
      obtain ⟨rfl, rfl⟩ := hvs
      simp only [LConst.wtArgs, Bool.and_eq_true, decide_eq_true_eq] at hwt
      obtain ⟨⟨hwe, hse⟩, hwr⟩ := hwt
      have hte : e.ty = a.toMonoTy := by rw [LConst.ty_of_wt hwe, hse]
      obtain ⟨he, hde⟩ := LConst.denote_toLExpr tc op fv vt md e hwe
      have he' : LExpr.HasTypeA [] (e.toLExpr md : LExpr T.mono) a.toMonoTy := hte ▸ he
      have hf' : LExpr.HasTypeA [] f
          (.arrow a.toMonoTy (LMonoTy.mkArrow' s.toMonoTy (as.map (·.toMonoTy)))) := hf
      have happ := LExpr.HasTypeA.app (m := md) hf' he'
      have hx' : HEq (LExpr.denote tc op fv vt .nil (e.toLExpr md) a.toMonoTy he') y :=
        (denote_heq_of_ty hte he he').symm.trans
          ((heq_of_eq hde).trans (heq_denoteConst vt hwe hx))
      have hF' : HEq (LExpr.denote tc op fv vt .nil (.app md f (e.toLExpr md)) _ happ) (F₀ y) := by
        rw [denote_app .nil hf' he' happ]
        exact heq_app (congrArg (SortDenote tc) (LSort.toMonoTy_substTyVars vt a))
          (congrArg (SortDenote tc) (substTyVars_sig vt s as)) hF hx'
      exact LConst.denote_toLExprApp tc op fv vt md as r ys s _ happ (F₀ y) hF' hxs hwr
    · cases hvs
  | [], _ :: _, _, _, _, _, _, _, hvs, _ | _ :: _, [], _, _, _, _, _, _, hvs, _ => by
    simp [constValArgs] at hvs
end

/-- Applying an expression to the expressions of constants and then to one more constant is
    applying it to the expressions of all of them. -/
private theorem LConst.toLExprApp_append [Inhabited T.IDMeta] (md : T.Metadata) (c : LConst) :
    ∀ (cs : List LConst) (f : LExpr T.mono),
      LConst.toLExprApp md f (cs ++ [c]) = .app md (LConst.toLExprApp md f cs) (c.toLExpr md)
  | [], _ => rfl
  | _ :: cs, _ => LConst.toLExprApp_append md c cs _

/-! ### The constant of an expression -/

/-- Two expressions are *denotationally equivalent* when they have the same types and, at each,
    the same denotation in every interpretation. -/
private def DenEquiv (e e' : LExpr T.mono) : Prop :=
  ∀ τ, (LExpr.HasTypeA [] e τ ↔ LExpr.HasTypeA [] e' τ) ∧
    ∀ (tc : TyConstrInterp) (op : OpInterp tc) (fv : FreeVarVal T tc) (vt : TyVarVal)
      (h : LExpr.HasTypeA [] e τ) (h' : LExpr.HasTypeA [] e' τ),
      LExpr.denote tc op fv vt .nil e τ h = LExpr.denote tc op fv vt .nil e' τ h'

/-- Denotational equivalence is symmetric. -/
private theorem DenEquiv.symm {e e' : LExpr T.mono} (h : DenEquiv e e') : DenEquiv e' e :=
  fun τ => ⟨(h τ).1.symm, fun tc op fv vt h₁ h₂ => ((h τ).2 tc op fv vt h₂ h₁).symm⟩

/-- Denotational equivalence is transitive. -/
private theorem DenEquiv.trans {e₁ e₂ e₃ : LExpr T.mono} (h₁₂ : DenEquiv e₁ e₂)
    (h₂₃ : DenEquiv e₂ e₃) : DenEquiv e₁ e₃ :=
  fun τ => ⟨(h₁₂ τ).1.trans (h₂₃ τ).1, fun tc op fv vt h₁ h₃ =>
    ((h₁₂ τ).2 tc op fv vt h₁ ((h₁₂ τ).1.mp h₁)).trans ((h₂₃ τ).2 tc op fv vt _ h₃)⟩

/-- Operators of one name and annotation are denotationally equivalent. -/
private theorem DenEquiv.op {m m' : T.Metadata} {o o' : Identifier T.IDMeta} {ty : Option LMonoTy}
    (hn : o.name = o'.name) : DenEquiv (.op m o ty : LExpr T.mono) (.op m' o' ty) := by
  intro τ
  cases ty with
  | none =>
    refine ⟨⟨fun h => absurd (LExpr.HasTypeA_to_typeCheck h) (by simp [LExpr.typeCheck]),
      fun h => absurd (LExpr.HasTypeA_to_typeCheck h) (by simp [LExpr.typeCheck])⟩,
      fun _ _ _ _ h => absurd (LExpr.HasTypeA_to_typeCheck h) (by simp [LExpr.typeCheck])⟩
  | some ty =>
    refine ⟨⟨fun h => HasTypeA.op_inv h ▸ .op, fun h => HasTypeA.op_inv h ▸ .op⟩,
      fun tc op fv vt h h' => ?_⟩
    obtain rfl := HasTypeA.op_inv h
    rw [denote_op, denote_op, hn]

/-- Applications of denotationally equivalent expressions to denotationally equivalent
    arguments are denotationally equivalent. -/
private theorem DenEquiv.app {m m' : T.Metadata} {f f' a a' : LExpr T.mono}
    (hf : DenEquiv f f') (ha : DenEquiv a a') : DenEquiv (.app m f a) (.app m' f' a') := by
  intro τ
  refine ⟨⟨fun h => ?_, fun h => ?_⟩, fun tc op fv vt h h' => ?_⟩
  · obtain ⟨aty, h₁, h₂⟩ := HasTypeA.app_inv h
    exact .app ((hf _).1.mp h₁) ((ha _).1.mp h₂)
  · obtain ⟨aty, h₁, h₂⟩ := HasTypeA.app_inv h
    exact .app ((hf _).1.mpr h₁) ((ha _).1.mpr h₂)
  · obtain ⟨aty, h₁, h₂⟩ := HasTypeA.app_inv h
    obtain ⟨aty', h₁', h₂'⟩ := HasTypeA.app_inv h'
    obtain rfl := HasTypeA_unique ((ha _).1.mp h₂) h₂'
    rw [denote_app .nil h₁ h₂ h, denote_app .nil h₁' h₂' h', (hf _).2 tc op fv vt h₁ h₁',
      (ha _).2 tc op fv vt h₂ h₂']

/-- A well-typed constant is denotationally equivalent to its expression (`LConst.toLExpr`). -/
private theorem DenEquiv.const_toLExpr [Inhabited T.IDMeta] (md md' : T.Metadata) {c : LConst}
    (hw : c.wt = true) : DenEquiv (.const md c : LExpr T.mono) (c.toLExpr md') := by
  have hinh := SortDenote.inhabited (fun _ _ => Unit) (fun _ _ => ⟨()⟩)
  have ⟨ht, _⟩ := LConst.denote_toLExpr (T := T) (fun _ _ => Unit) (fun _ s => (hinh s).default)
    (fun _ s => (hinh s).default) (fun _ => .bool) md' c hw
  intro τ
  refine ⟨⟨fun h => HasTypeA.const_inv h ▸ ht, fun h => HasTypeA_unique ht h ▸ .const hw⟩,
    fun tc op fv vt h h' => ?_⟩
  obtain rfl := HasTypeA.const_inv h
  obtain ⟨h'', hd⟩ := LConst.denote_toLExpr tc op fv vt md' c hw
  rw [hd]
  rfl

/-- The datatype value `LConst.dataOf?` builds is well typed, and its expression is the operator
    with the given name and annotation applied to the expressions of the given constants. -/
private theorem LConst.dataOf?_some [Inhabited T.IDMeta] {F : Factory T} {n : String}
    {ty : LMonoTy} {cs : List LConst} {c : LConst} (md : T.Metadata)
    (h : LConst.dataOf? F n ty cs = some c) :
    c.wt = true ∧ (∀ c' ∈ cs, c'.wt = true) ∧
      c.toLExpr md = LConst.toLExprApp md (.op md ⟨n, default⟩ (some ty)) cs := by
  unfold LConst.dataOf? at h
  split at h
  · rename_i s hs
    dsimp only at h
    split at h
    · rename_i hc
      simp only [Option.some.injEq] at h; subst h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
      obtain ⟨⟨⟨hsa, -⟩, hr⟩, hwa⟩ := hc
      refine ⟨by simp [LConst.wt, hr, hwa], wt_of_wtArgs hwa, ?_⟩
      have hty : ty = LMonoTy.mkArrow' (s.dropArrows cs.length).toMonoTy
          ((cs.map (·.sort)).map (·.toMonoTy)) := by
        rw [← LMonoTy.toSort?_toMonoTy hs, ← LSort.toMonoTy_mkArrow, ← hsa]
      rw [hty]; rfl
    · cases h
  · cases h

/-- Both parts of `LExpr.toConstAux` are sound: the constant an expression stands for is
    denotationally equivalent to it, and an expression whose operator spine has well-typed
    constant arguments is denotationally equivalent to that operator applied to their
    expressions. -/
private theorem LExpr.toConstAux_sound [Inhabited T.IDMeta] (F : Factory T) (md : T.Metadata) :
    ∀ e : LExpr T.mono,
      (∀ c, (LExpr.toConstAux F e).1 = some c → DenEquiv e (.const md c)) ∧
      (∀ n ty cs, (LExpr.toConstAux F e).2 = some (n, ty, cs) → (∀ c ∈ cs, c.wt = true) →
        DenEquiv e (LConst.toLExprApp md (.op md ⟨n, default⟩ (some ty)) cs))
  | .const m c => by
    refine ⟨fun c' h => ?_, fun _ _ _ h => by simp [LExpr.toConstAux] at h⟩
    simp only [LExpr.toConstAux, Option.some.injEq] at h; subst h
    intro τ
    refine ⟨⟨fun h => HasTypeA.const_inv h ▸ .const (HasTypeA.const_wt h),
      fun h => HasTypeA.const_inv h ▸ .const (HasTypeA.const_wt h)⟩, fun tc op fv vt h h' => ?_⟩
    obtain rfl := HasTypeA.const_inv h
    rfl
  | .op m o (some ty) => by
    have hspine : ∀ n ty' cs, (LExpr.toConstAux F (.op m o (some ty))).2 = some (n, ty', cs) →
        (∀ c ∈ cs, c.wt = true) →
        DenEquiv (.op m o (some ty)) (LConst.toLExprApp md (.op md ⟨n, default⟩ (some ty')) cs) := by
      intro n ty' cs h _
      simp only [LExpr.toConstAux, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact DenEquiv.op rfl
    refine ⟨fun c h => ?_, hspine⟩
    obtain ⟨hw, -, hc⟩ := LConst.dataOf?_some md h
    simp only [LConst.toLExprApp] at hc
    have hce := (DenEquiv.const_toLExpr md md hw).symm
    rw [hc] at hce
    exact (@DenEquiv.op T m md o ⟨o.name, default⟩ (some ty) rfl).trans hce
  | .app m f a => by
    obtain ⟨-, ihf⟩ := LExpr.toConstAux_sound F md f
    obtain ⟨iha, -⟩ := LExpr.toConstAux_sound F md a
    have hspine : ∀ n ty cs, (LExpr.toConstAux F (.app m f a)).2 = some (n, ty, cs) →
        (∀ c ∈ cs, c.wt = true) →
        DenEquiv (.app m f a) (LConst.toLExprApp md (.op md ⟨n, default⟩ (some ty)) cs) := by
      intro n ty cs h hw
      simp only [LExpr.toConstAux] at h
      obtain ⟨⟨n₀, ty₀, cs'⟩, hf, hp⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨c, ha, hc⟩ := Option.map_eq_some_iff.mp hp
      simp only [Prod.mk.injEq] at hc
      obtain ⟨rfl, rfl, rfl⟩ := hc
      have hwc := hw c (by simp)
      rw [LConst.toLExprApp_append]
      exact DenEquiv.app (ihf n₀ ty₀ cs' hf (fun c' hc' => hw c' (by simp [hc'])))
        ((iha c ha).trans (DenEquiv.const_toLExpr md md hwc))
    refine ⟨fun c h => ?_, hspine⟩
    simp only [LExpr.toConstAux] at h
    obtain ⟨⟨n, ty, cs⟩, hsp, hd⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨hw, hwcs, hc⟩ := LConst.dataOf?_some md hd
    exact (hspine n ty cs (by simp only [LExpr.toConstAux]; exact hsp) hwcs).trans
      (hc ▸ (DenEquiv.const_toLExpr md md hw).symm)
  | .op _ _ none | .bvar .. | .fvar .. | .abs .. | .quant .. | .ite .. | .eq .. => by
    exact ⟨fun _ h => by simp [LExpr.toConstAux] at h, fun _ _ _ h => by simp [LExpr.toConstAux] at h⟩

/-- **The constant of an expression has its type and denotation.** If an expression of type `τ`
    stands for the constant `c` (`LExpr.toConst?`), then `c` is well typed, has type `τ`, and as
    an expression denotes what the expression denotes in every interpretation. -/
theorem LExpr.toConst?_sound [Inhabited T.IDMeta] {F : Factory T} {e : LExpr T.mono} {c : LConst}
    (hc : e.toConst? F = some c) {τ : LMonoTy} (he : LExpr.HasTypeA [] e τ) :
    c.wt = true ∧ c.ty = τ ∧ ∀ (tc : TyConstrInterp) (op : OpInterp tc) (fv : FreeVarVal T tc)
      (vt : TyVarVal) (md : T.Metadata) (h : LExpr.HasTypeA [] (.const md c : LExpr T.mono) τ),
      LExpr.denote tc op fv vt .nil (.const md c) τ h = LExpr.denote tc op fv vt .nil e τ he := by
  have hq := fun md => (LExpr.toConstAux_sound F md e).1 c hc
  have hcτ := ((hq e.metadata) τ).1.mp he
  refine ⟨HasTypeA.const_wt hcτ, (HasTypeA.const_inv hcτ).symm, fun tc op fv vt md h => ?_⟩
  exact ((hq md τ).2 tc op fv vt he h).symm

/-! ### Equality of constants knowing the constructors -/

/-- A ground constructor (`Factory.isGroundConstr`) is a constructor function of the factory
    with that name and signature. -/
private theorem Factory.isGroundConstr_some {F : Factory T} {n : String} {as : List LSort}
    {s : LSort} (h : F.isGroundConstr n as s = true) :
    ∃ f ∈ F.toArray, f.name.name = n ∧ f.isConstr = true ∧ f.output = s.toMonoTy ∧
      f.inputs.values = as.map (·.toMonoTy) := by
  unfold Factory.isGroundConstr at h
  split at h
  · rename_i f hf
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨hm, hn⟩ := Factory.getElem?_eq_some_iff'.mp hf
    exact ⟨f, hm, hn, h.1.1, h.1.2, h.2⟩
  · cases h

/-- The sorts of a function with a ground signature, under any type-variable valuation. -/
private theorem ground_sorts (vt : TyVarVal) {f : LFunc T} {as : List LSort} {s : LSort}
    (ho : f.output = s.toMonoTy) (hi : f.inputs.values = as.map (·.toMonoTy)) :
    LMonoTy.substTyVars vt f.output = s ∧ f.inputs.values.map (LMonoTy.substTyVars vt) = as := by
  rw [ho, hi, LSort.toMonoTy_substTyVars, map_toMonoTy_substTyVars]; exact ⟨rfl, rfl⟩

/-- Two different ground constructors of one sort give different values. -/
private theorem constr_disjoint_ground {tc : TyConstrInterp} {op : OpInterp tc} {F : Factory T}
    (hF : ConstrInterpConsistent tc op F) {n₁ n₂ : String} {as₁ as₂ : List LSort} {s : LSort}
    (h₁ : F.isGroundConstr n₁ as₁ s = true) (h₂ : F.isGroundConstr n₂ as₂ s = true)
    (hn : n₁ ≠ n₂) (v₁ : HList (SortDenote tc) as₁) (v₂ : HList (SortDenote tc) as₂) :
    SortDenote.applyArgs tc (op n₁ (LSort.mkArrow s as₁)) v₁ ≠
      SortDenote.applyArgs tc (op n₂ (LSort.mkArrow s as₂)) v₂ := by
  obtain ⟨f₁, hm₁, rfl, hc₁, ho₁, hi₁⟩ := Factory.isGroundConstr_some h₁
  obtain ⟨f₂, hm₂, rfl, hc₂, ho₂, hi₂⟩ := Factory.isGroundConstr_some h₂
  have hd := hF.constr_disjoint f₁ f₂ hm₁ hm₂ hc₁ hc₂ hn (fun _ => .bool)
  obtain ⟨hs₁, ha₁⟩ := ground_sorts (fun _ => .bool) ho₁ hi₁
  obtain ⟨hs₂, ha₂⟩ := ground_sorts (fun _ => .bool) ho₂ hi₂
  simp only at hd
  revert hd
  rw [hs₁, ha₁, hs₂, ha₂]
  exact fun hd => hd rfl v₁ v₂

/-- A ground constructor is injective. -/
private theorem constr_injective_ground {tc : TyConstrInterp} {op : OpInterp tc} {F : Factory T}
    (hF : ConstrInterpConsistent tc op F) {n : String} {as : List LSort} {s : LSort}
    (h : F.isGroundConstr n as s = true) (v₁ v₂ : HList (SortDenote tc) as) :
    SortDenote.applyArgs tc (op n (LSort.mkArrow s as)) v₁ =
      SortDenote.applyArgs tc (op n (LSort.mkArrow s as)) v₂ → v₁ = v₂ := by
  obtain ⟨f, hm, rfl, hc, ho, hi⟩ := Factory.isGroundConstr_some h
  have hd := hF.constr_injective f hm hc (fun _ => .bool)
  obtain ⟨hs, ha⟩ := ground_sorts (fun _ => .bool) ho hi
  simp only at hd
  revert hd
  rw [hs, ha]
  exact fun hd => hd v₁ v₂

/-- A decided `LConst.eql` is the equality of the values. -/
private theorem LConst.eql_sound {tc : TyConstrInterp} {op : OpInterp tc} {c₁ c₂ : LConst}
    {s : LSort} {x y : SortDenote tc s} {b : Bool} (hx : constVal tc op s c₁ = some x)
    (hy : constVal tc op s c₂ = some y) (h : LConst.eql c₁ c₂ = some b) : x = y ↔ b = true := by
  unfold LConst.eql at h
  split at h
  · rename_i heq
    cases h
    obtain rfl := eq_of_beq heq
    exact ⟨fun _ => rfl, fun _ => Option.some.inj (hx.symm.trans hy)⟩
  · split at h
    · rename_i hne hd
      cases h
      simp only [LConst.eqDecidable, Bool.and_eq_true, Bool.not_eq_true'] at hd
      have hs : s.hasMap = false := constVal_sort hx ▸ hd.1.1.2
      exact ⟨fun hxy => absurd (constVal_injective c₁ c₂ hs hd.1.2 hx (hxy ▸ hy)) (by simpa using hne),
        nofun⟩
    · cases h

/-- Lists of sorts named by the same types are equal. -/
private theorem map_toMonoTy_injective : ∀ {as₁ as₂ : List LSort},
    as₁.map (·.toMonoTy) = as₂.map (·.toMonoTy) → as₁ = as₂
  | [], [], _ => rfl
  | _ :: _, _ :: _, h => by
    simp only [List.map_cons, List.cons.injEq] at h
    rw [LSort.toMonoTy_injective h.1, map_toMonoTy_injective h.2]
  | [], _ :: _, h | _ :: _, [], h => by simp at h

/-- The ground constructors of one name have one signature. -/
private theorem Factory.isGroundConstr_unique {F : Factory T} {n : String}
    {as₁ as₂ : List LSort} {s₁ s₂ : LSort} (h₁ : F.isGroundConstr n as₁ s₁ = true)
    (h₂ : F.isGroundConstr n as₂ s₂ = true) : as₁ = as₂ := by
  obtain ⟨f₁, hm₁, hn₁, -, -, hi₁⟩ := Factory.isGroundConstr_some h₁
  obtain ⟨f₂, hm₂, hn₂, -, -, hi₂⟩ := Factory.isGroundConstr_some h₂
  obtain rfl : f₁ = f₂ := Option.some.inj ((Factory.getElem?_eq_some_iff'.mpr ⟨hm₁, hn₁⟩).symm.trans
    (Factory.getElem?_eq_some_iff'.mpr ⟨hm₂, hn₂⟩))
  exact map_toMonoTy_injective (hi₁.symm.trans hi₂)

mutual
/-- **The factory-aware equality of constants is sound.** In an interpretation whose constructors
    are disjoint and injective (`ConstrInterpConsistent`), a decided `LConst.eqlIn F` on two
    constants with values at one sort is the equality of those values. -/
theorem LConst.eqlIn_sound {tc : TyConstrInterp} {op : OpInterp tc} {F : Factory T}
    (hF : ConstrInterpConsistent tc op F) :
    ∀ (c₁ c₂ : LConst) {s : LSort} {x y : SortDenote tc s} {b : Bool},
      constVal tc op s c₁ = some x → constVal tc op s c₂ = some y → LConst.eqlIn F c₁ c₂ = some b →
      (x = y ↔ b = true)
  | .dataConst n₁ as₁ s₁ ⟨xs⟩, .dataConst n₂ as₂ s₂ ⟨ys⟩, s, x, y, b, hx, hy, h => by
    simp only [LConst.eqlIn] at h
    split at h
    · rename_i heq
      obtain ⟨rfl, rfl, rfl, rfl⟩ := heq
      cases h
      exact ⟨fun _ => rfl, fun _ => Option.some.inj (hx.symm.trans hy)⟩
    · split at h
      · rename_i _ hg
        simp only [Bool.and_eq_true] at hg
        obtain ⟨rfl, hd⟩ := constVal_dataConst_some hx
        obtain ⟨rfl, -⟩ := constVal_dataConst_some hy
        rw [constVal_dataConst _ _ _ _ hd] at hx hy
        obtain ⟨vs, hvs, rfl⟩ := Option.map_eq_some_iff.mp hx
        obtain ⟨ws, hws, rfl⟩ := Option.map_eq_some_iff.mp hy
        split at h
        · rename_i hn
          subst hn
          obtain rfl := Factory.isGroundConstr_unique hg.1 hg.2
          rw [← LConst.eqlInArgs_sound hF xs ys hvs hws h]
          exact ⟨constr_injective_ground hF hg.1 vs ws, fun h => h ▸ rfl⟩
        · rename_i hn
          cases h
          exact ⟨fun he => absurd he (constr_disjoint_ground hF hg.1 hg.2 hn vs ws), nofun⟩
      · cases h
  | .dataConst .., .intConst _, _, _, _, _, hx, hy, h
  | .dataConst .., .strConst _, _, _, _, _, hx, hy, h
  | .dataConst .., .rationalConst _, _, _, _, _, hx, hy, h
  | .dataConst .., .bitvecConst .., _, _, _, _, hx, hy, h
  | .dataConst .., .boolConst _, _, _, _, _, hx, hy, h
  | .dataConst .., .mapConst .., _, _, _, _, hx, hy, h
  | .dataConst .., .sequenceConst .., _, _, _, _, hx, hy, h
  | .intConst _, _, _, _, _, _, hx, hy, h
  | .strConst _, _, _, _, _, _, hx, hy, h
  | .rationalConst _, _, _, _, _, _, hx, hy, h
  | .bitvecConst .., _, _, _, _, _, hx, hy, h
  | .boolConst _, _, _, _, _, _, hx, hy, h
  | .mapConst .., _, _, _, _, _, hx, hy, h
  | .sequenceConst .., _, _, _, _, _, hx, hy, h => by
    simp only [LConst.eqlIn] at h
    exact LConst.eql_sound hx hy h
/-- `LConst.eqlIn_sound` for the arguments of two datatype values, position by position. -/
private theorem LConst.eqlInArgs_sound {tc : TyConstrInterp} {op : OpInterp tc} {F : Factory T}
    (hF : ConstrInterpConsistent tc op F) :
    ∀ (xs ys : List LConst) {as : List LSort} {vs ws : HList (SortDenote tc) as} {b : Bool},
      constValArgs tc op as xs = some vs → constValArgs tc op as ys = some ws →
      LConst.eqlInArgs F xs ys = some b → (vs = ws ↔ b = true)
  | [], [], [], .nil, .nil, b, _, _, h => by
    simp only [LConst.eqlInArgs, Option.some.injEq] at h
    subst h; exact ⟨fun _ => rfl, fun _ => rfl⟩
  | x :: xs, y :: ys, a :: as, .cons v vs, .cons w ws, b, hx, hy, h => by
    simp only [constValArgs] at hx hy
    split at hx
    · rename_i v' vs' hv hvs
      simp only [Option.some.injEq, HList.cons.injEq] at hx
      obtain ⟨rfl, rfl⟩ := hx
      split at hy
      · rename_i w' ws' hw hws
        simp only [Option.some.injEq, HList.cons.injEq] at hy
        obtain ⟨rfl, rfl⟩ := hy
        simp only [LConst.eqlInArgs] at h
        simp only [HList.cons.injEq]
        have ih₁ := fun b₁ (e : LConst.eqlIn F x y = some b₁) => LConst.eqlIn_sound hF x y hv hw e
        have ih₂ := fun b₂ (e : LConst.eqlInArgs F xs ys = some b₂) =>
          LConst.eqlInArgs_sound hF xs ys hvs hws e
        generalize LConst.eqlIn F x y = o₁ at ih₁ h
        generalize LConst.eqlInArgs F xs ys = o₂ at ih₂ h
        rcases o₁ with _ | _ | _ <;> rcases o₂ with _ | _ | _ <;>
          simp only [Option.some.injEq, reduceCtorEq] at h <;> subst h <;> simp_all
      · cases hy
    · cases hx
  | [], [], _ :: _, _, _, _, hx, _, _ | [], _ :: _, [], _, _, _, _, hy, _
  | [], _ :: _, _ :: _, _, _, _, hx, _, _ | _ :: _, [], [], _, _, _, hx, _, _
  | _ :: _, [], _ :: _, _, _, _, _, hy, _ | _ :: _, _ :: _, [], _, _, _, hx, _, _ => by
    first | simp [constValArgs] at hx | simp [constValArgs] at hy
end

end -- public section

end Lambda
