/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.Simplify.ExprCorrect
import all Strata.Transform.Simplify.ExprCorrect
import all Strata.Transform.Simplify.Expr
import all Strata.DL.Lambda.Denote.ReachesModMeta
import all Strata.DL.Lambda.Denote.Assumptions
import all Strata.DL.Lambda.Denote.LExprSemanticsConsistent
import all Strata.DL.Lambda.LExprDenoteEval
import Strata.DL.Lambda.LExprDenoteEvalProps
import Strata.DL.Lambda.Denote.LExprAnnotated
import Strata.DL.Lambda.OperationalSemanticsProps
import Strata.Util.ListMapProps
import Strata.Transform.Simplify.StmtShape
import all Strata.Util.ListMap
public import Strata.DL.Imperative.BigStep.Sem
import Strata.DL.Imperative.BigStep.SemProps
import all Strata.DL.Imperative.Store

/-! # Simplify's recorded values against a store

While Simplify walks a body it records, for some variables, an expression for their current
value. Against the store a run of the body has reached, a recorded value is sound
(`ValueGood`) when it evaluates there, under Core's evaluator, to its variable's value, and
each of its free variables is bound and annotated with the sort of its value. A context all
of whose values are sound (`ValuesSound`) is a sound context for the expression lemmas
(`CtxSound.ofValues`), with the type map that records the stored sorts of any finite set of
names covering the recorded values (`storeTyMap`).

The key result is `simplifyExpr_eval`: in such a context, simplifying an expression that is
well-formed against the store keeps it well-formed and keeps its value.
-/

namespace Core.Simplify

open Lambda

/-- Every free variable of `e` is bound in `σ` and annotated with the sort of its value. -/
def StoreAnnotated (σ : ValStore CoreLParams) (e : Expression.Expr) : Prop :=
  ∀ y ty, (y, ty) ∈ LExpr.freeVars e → ∃ v, σ y = some v ∧ ty = some v.sort.toMonoTy

/-- The recorded value `r` of `x` is sound in `σ`: it evaluates there to the value of `x`, its
    operators are annotated as the factory `F` says, and its free variables are bound and
    annotated with their stored sorts. -/
def ValueGood (F : Lambda.Factory CoreLParams) (M : ModeledFactory CoreLParams)
    (σ : ValStore CoreLParams) (x : CoreIdent) (r : Expression.Expr) : Prop :=
  (∃ v, σ x = some v ∧ r.denoteEval M σ = some v) ∧ OpsConsistent F r ∧ StoreAnnotated σ r

/-- Every value the context records is sound in `σ`. -/
def ValuesSound (ctx : Ctx) (M : ModeledFactory CoreLParams) (σ : ValStore CoreLParams) :
    Prop :=
  ∀ x r, (x, r) ∈ ctx.values.toList → ValueGood ctx.foldFactory M σ x r

/-- A value the context finds for a variable is sound. -/
private theorem ValuesSound.find {ctx : Ctx} {M : ModeledFactory CoreLParams}
    {σ : ValStore CoreLParams} (h : ValuesSound ctx M σ) {x : CoreIdent}
    {r : Expression.Expr} (hx : Map.find? ctx.values x = some r) :
    ValueGood ctx.foldFactory M σ x r :=
  h x r (Map.find?_mem _ _ _ hx)

/-- The type map giving each name of `N` that `σ` binds the sort of its value. -/
def storeTyMap (σ : ValStore CoreLParams) (N : List CoreIdent) : Map CoreIdent LMonoTy :=
  N.filterMap fun y => (σ y).map fun v => (y, v.sort.toMonoTy)

/-- The store's type map of `N` gives each name of `N` the sort of its stored value. -/
private theorem find?_storeTyMap (σ : ValStore CoreLParams) :
    ∀ (N : List CoreIdent) (y : CoreIdent),
      Map.find? (storeTyMap σ N) y = if y ∈ N then (σ y).map (·.sort.toMonoTy) else none := by
  intro N
  induction N with
  | nil => intro y; rfl
  | cons z N ih =>
    intro y
    unfold storeTyMap at ih ⊢
    rw [List.filterMap_cons]
    cases hz : σ z with
    | none =>
      simp only [Option.map_none]
      rw [ih y]
      by_cases hyz : y = z
      · subst hyz; simp [hz]
      · simp [hyz]
    | some w =>
      simp only [Option.map_some, Map.find?]
      split
      · rename_i hzy; subst hzy; simp [hz]
      · rename_i hzy
        rw [ih y]
        have : y ≠ z := fun h => hzy h.symm
        simp [this]

/-- A name the store's type map types is in `N`, bound, at the sort of its value. -/
theorem find?_storeTyMap_eq_some {σ : ValStore CoreLParams} {N : List CoreIdent}
    {y : CoreIdent} {τ : LMonoTy} (h : Map.find? (storeTyMap σ N) y = some τ) :
    y ∈ N ∧ ∃ v, σ y = some v ∧ v.sort.toMonoTy = τ := by
  rw [find?_storeTyMap] at h
  split at h
  · rename_i hy
    cases hσ : σ y with
    | none => rw [hσ] at h; cases h
    | some v => rw [hσ] at h; cases h; exact ⟨hy, v, rfl, rfl⟩
  · cases h

/-- The store's type map types every bound name of `N` at the sort of its value. -/
private theorem find?_storeTyMap_of {σ : ValStore CoreLParams} {N : List CoreIdent}
    {y : CoreIdent} (hy : y ∈ N) {v : SemValue} (hv : σ y = some v) :
    Map.find? (storeTyMap σ N) y = some v.sort.toMonoTy := by
  rw [find?_storeTyMap]; simp [hy, hv]

/-- A store-annotated expression is left unchanged by the store's annotation. -/
private theorem StoreAnnotated.annotate_eq {σ : ValStore CoreLParams} {e : Expression.Expr}
    (h : StoreAnnotated σ e) : e.annotateFvars σ.ann = e := by
  apply LExpr.annotateFvars_eq_self_of_none
  intro y ty hy
  obtain ⟨v, hv, rfl⟩ := h y ty hy
  right
  simp [ValStore.ann, hv]

/-- A store-annotated expression is annotated against the store's type map of any names
    covering its free variables. -/
private theorem StoreAnnotated.fvars_annotated_by {σ : ValStore CoreLParams} {N : List CoreIdent}
    {e : Expression.Expr} (h : StoreAnnotated σ e) :
    fvars_annotated_by (storeTyMap σ N) e := by
  induction e with
  | const | op | bvar => trivial
  | fvar m y ty =>
    obtain ⟨v, hv, rfl⟩ := h y ty (by simp [LExpr.freeVars])
    intro t ht
    obtain ⟨-, w, hw, rfl⟩ := find?_storeTyMap_eq_some ht
    rw [hv] at hw; cases hw; rfl
  | abs _ _ _ _ ih => exact ih (fun y ty hy => h y ty hy)
  | quant _ _ _ _ _ _ ih₁ ih₂ =>
    exact ⟨ih₁ (fun y ty hy => h y ty (by simp [LExpr.freeVars, hy])),
      ih₂ (fun y ty hy => h y ty (by simp [LExpr.freeVars, hy]))⟩
  | app _ _ _ ih₁ ih₂ =>
    exact ⟨ih₁ (fun y ty hy => h y ty (by simp [LExpr.freeVars, hy])),
      ih₂ (fun y ty hy => h y ty (by simp [LExpr.freeVars, hy]))⟩
  | eq _ _ _ ih₁ ih₂ =>
    exact ⟨ih₁ (fun y ty hy => h y ty (by simp [LExpr.freeVars, hy])),
      ih₂ (fun y ty hy => h y ty (by simp [LExpr.freeVars, hy]))⟩
  | ite _ _ _ _ ih₁ ih₂ ih₃ =>
    exact ⟨ih₁ (fun y ty hy => h y ty (by simp [LExpr.freeVars, hy])),
      ih₂ (fun y ty hy => h y ty (by simp [LExpr.freeVars, hy])),
      ih₃ (fun y ty hy => h y ty (by simp [LExpr.freeVars, hy]))⟩


/-- A sound recorded value is well-typed at the sort of its variable's value, which is
    ground, and denotes that value at the model's type-variable valuation. -/
private theorem ValueGood.denote {F : Lambda.Factory CoreLParams} {M : ModeledFactory CoreLParams}
    {σ : ValStore CoreLParams} {x : CoreIdent} {r : Expression.Expr}
    (h : ValueGood F M σ x r) :
    ∃ v, σ x = some v ∧ v.tc = M.model.tcInterp ∧
      LExpr.HasTypeA [] r v.sort.toMonoTy ∧
      ∀ ht : LExpr.HasTypeA [] r v.sort.toMonoTy,
        LExpr.denote M.model.tcInterp M.model.opInterp
          (@ValStore.fvarVal CoreLParams M.model.tcInterp M.model.allInhabited σ) M.tyVarVal
          .nil r v.sort.toMonoTy ht =
        @ValStore.fvarVal CoreLParams M.model.tcInterp M.model.allInhabited σ x
          (v.sort.toMonoTy.substTyVars M.tyVarVal) := by
  obtain ⟨⟨v, hx, hv⟩, -, hann⟩ := h
  obtain ⟨-, τ, hτ, hg, rfl⟩ := (LExpr.denoteEval_eq_some_iff (T := CoreLParams)).mp hv
  have he := hann.annotate_eq
  have hsort : (τ.substTyVars M.tyVarVal).toMonoTy = τ := by
    rw [hg.substTyVars_eq M.tyVarVal refTyVarVal]; exact hg
  simp only [LExpr.denoteEvalResult] at hx ⊢
  refine ⟨_, hx, rfl, ?_, fun ht => ?_⟩
  · rw [hsort]; exact he ▸ hτ
  · simp only [ValStore.fvarVal, hx, Option.bind_some]
    generalize hT : (LMonoTy.substTyVars M.tyVarVal τ).toMonoTy = τ' at ht ⊢
    rw [hsort] at hT
    subst hT
    have hr := SemValue.read_self ⟨M.model.tcInterp, τ.substTyVars M.tyVarVal,
      LExpr.denote M.model.tcInterp M.model.opInterp
        (@ValStore.fvarVal CoreLParams M.model.tcInterp M.model.allInhabited σ) M.tyVarVal .nil
        (LExpr.annotateFvars σ.ann r) τ hτ⟩
    simp only at hr
    rw [hr, Option.getD_some]
    exact denote_congr_term he.symm ht hτ


/-- **A context whose values are sound is sound** for the valuation a store induces, with
    the type map recording the stored sorts of names `N` that cover the recorded values. -/
def CtxSound.ofValues {ctx : Ctx} {M : ModeledFactory CoreLParams} {σ : ValStore CoreLParams}
    {tf : @Lambda.TypeFactory CoreLParams.IDMeta} (N : List CoreIdent)
    (hok : ctx.FactoriesOK) (hV : ValuesSound ctx M σ)
    (hN : ∀ x r, Map.find? ctx.values x = some r → x ∈ N ∧ r.NamesIn (fun y : CoreIdent => y ∈ N))
    (hfac : Factory.WF ctx.foldFactory tf)
    (hstep : Factory.StepWFOn ctx.foldFactory (storeTyMap σ N))
    (hfic : Factory.InterpConsistent M.model.tcInterp M.model.opInterp ctx.foldFactory)
    (hcic : ConstrInterpConsistent M.model.tcInterp M.model.opInterp ctx.foldFactory) :
    CtxSound ctx tf M.model.tcInterp M.model.opInterp
      (@ValStore.fvarVal CoreLParams M.model.tcInterp M.model.allInhabited σ) M.tyVarVal where
  factories := hok
  envWF := {
    typed := {
      tyMap := storeTyMap σ N
      wt := fun x r ty hx hty => by
        obtain ⟨v, hv, -, ht, -⟩ := (hV.find hx).denote
        obtain ⟨-, w, hw, rfl⟩ := find?_storeTyMap_eq_some hty
        rw [hv] at hw; cases hw; exact ht
      cover := fun x r hx => by
        obtain ⟨v, hv, -⟩ := (hV.find hx).denote
        exact ⟨_, find?_storeTyMap_of (hN x r hx).1 hv⟩ }
    lc := fun x r hx => by
      obtain ⟨v, -, -, ht, -⟩ := (hV.find hx).denote
      exact HasTypeA_nil_lcAt ht
    ops := fun x r hx => (hV.find hx).2.1
    annot := fun x r hx => (hV.find hx).2.2.fvars_annotated_by }
  facWF := hfac
  fWF := hstep
  fic := hfic
  cic := hcic
  envIC := fun x r ty hx ht => by
    obtain ⟨v, hv, -, ht₀, hd⟩ := (hV.find hx).denote
    have hty : ty = v.sort.toMonoTy := HasTypeA_unique ht ht₀
    subst hty
    exact hd ht
  cover := fun x r hx y ty hy => by
    obtain ⟨v, hv, -⟩ := (hV.find hx).2.2 y ty hy
    rw [find?_storeTyMap_of ((hN x r hx).2 y ty hy) hv]; rfl

/-- The names a context's recorded values mention, with their variables. -/
def Ctx.valueNames (ctx : Ctx) : List CoreIdent :=
  let keys := ctx.values.toList.map Prod.fst
  keys ++ keys.flatMap fun k =>
    ((Map.find? ctx.values k).map fun r => (LExpr.freeVars r).map Prod.fst).getD []

/-- The names of a context's values include each recorded variable and the free variables of its
    value. -/
private theorem Ctx.mem_valueNames {ctx : Ctx} {x : CoreIdent} {r : Expression.Expr}
    (hx : Map.find? ctx.values x = some r) :
    x ∈ ctx.valueNames ∧ ∀ y ty, (y, ty) ∈ LExpr.freeVars r → y ∈ ctx.valueNames := by
  have hm : (x, r) ∈ ctx.values.toList := Map.find?_mem _ _ _ hx
  have hk : x ∈ ctx.values.toList.map Prod.fst := List.mem_map.mpr ⟨_, hm, rfl⟩
  refine ⟨List.mem_append_left _ hk, fun y ty hy => ?_⟩
  refine List.mem_append_right _ (List.mem_flatMap.mpr ⟨x, hk, ?_⟩)
  rw [hx]
  exact List.mem_map.mpr ⟨_, hy, rfl⟩

/-- The names of a context's values satisfy every predicate its variables and their values' free
    variables satisfy. -/
private theorem Ctx.valueNames_sat {ctx : Ctx} {A : CoreIdent → Prop}
    (hAV : ∀ x r, Map.find? ctx.values x = some r → A x ∧ r.NamesIn A) :
    ∀ y ∈ ctx.valueNames, A y := by
  intro y hy
  rcases List.mem_append.mp hy with hy | hy
  · obtain ⟨⟨x, r⟩, hm, rfl⟩ := List.mem_map.mp hy
    obtain ⟨r', hr'⟩ := Option.isSome_iff_exists.mp (Map.find?_isSome_of_mem ctx.values.toList hm)
    exact (hAV _ r' hr').1
  · obtain ⟨k, -, hk⟩ := List.mem_flatMap.mp hy
    cases hf : Map.find? ctx.values k with
    | none => rw [hf] at hk; cases hk
    | some r =>
      rw [hf] at hk
      obtain ⟨⟨_, ty⟩, hm, rfl⟩ := List.mem_map.mp hk
      exact (hAV k r hf).2 _ ty hm

/-- What simplification keeps of an expression that is well-formed against a store: its
    value, its operators' consistency with the fold factory, the annotation of its free
    variables with their stored sorts, and which names those variables are. -/
structure ExprGood (F : Lambda.Factory CoreLParams) (M : ModeledFactory CoreLParams)
    (σ : ValStore CoreLParams) (A : CoreIdent → Prop) (e : Expression.Expr) : Prop where
  ops : OpsConsistent F e
  ann : StoreAnnotated σ e
  names : e.NamesIn A

/-- **Simplifying an expression against a store.** In a context whose recorded values are
    sound in the store `σ` and mention only names satisfying `A`, simplifying an expression
    well-formed against `σ` keeps it well-formed and keeps its value, provided the fold
    factory satisfies the step assumptions under the stored sorts of any names satisfying
    `A`. -/
theorem simplifyExpr_eval {ctx : Ctx} {M : ModeledFactory CoreLParams}
    {σ : ValStore CoreLParams} {tf : @Lambda.TypeFactory CoreLParams.IDMeta}
    {A : CoreIdent → Prop} (hok : ctx.FactoriesOK) (hV : ValuesSound ctx M σ)
    (hσ : ∀ y v, σ y = some v → v.tc = M.model.tcInterp)
    (hAV : ∀ x r, Map.find? ctx.values x = some r → A x ∧ r.NamesIn A)
    (hfac : Factory.WF ctx.foldFactory tf)
    (hstep : ∀ N : List CoreIdent, (∀ y ∈ N, A y) →
      Factory.StepWFOn ctx.foldFactory (storeTyMap σ N))
    (hfic : Factory.InterpConsistent M.model.tcInterp M.model.opInterp ctx.foldFactory)
    (hcic : ConstrInterpConsistent M.model.tcInterp M.model.opInterp ctx.foldFactory)
    {e : Expression.Expr} (he : ExprGood ctx.foldFactory M σ A e) :
    ExprGood ctx.foldFactory M σ A (simplifyExpr ctx e) ∧
      ∀ v, e.denoteEval M σ = some v → (simplifyExpr ctx e).denoteEval M σ = some v := by
  let N : List CoreIdent := (LExpr.freeVars e).map Prod.fst ++ ctx.valueNames
  have hNA : ∀ y ∈ N, A y := by
    intro y hy
    rcases List.mem_append.mp hy with hy | hy
    · obtain ⟨⟨_, ty⟩, hm, rfl⟩ := List.mem_map.mp hy; exact he.names _ ty hm
    · exact Ctx.valueNames_sat hAV y hy
  let h := CtxSound.ofValues (tf := tf) N hok hV
    (fun x r hx => ⟨List.mem_append_right _ (ctx.mem_valueNames hx).1,
      fun y ty hy => List.mem_append_right _ ((ctx.mem_valueNames hx).2 y ty hy)⟩)
    hfac (hstep N hNA) hfic hcic
  have hT : h.envWF.typed.tyMap = storeTyMap σ N := rfl
  have hmap : ∀ x τ, Map.find? h.envWF.typed.tyMap x = some τ →
      ∃ v, σ x = some v ∧ v.tc = M.model.tcInterp ∧ v.sort.toMonoTy = τ := by
    intro x τ hx
    rw [hT] at hx
    obtain ⟨-, v, hv, hs⟩ := find?_storeTyMap_eq_some hx
    exact ⟨v, hv, hσ x v hv, hs⟩
  have hcov : e.NamesIn (fun y => (Map.find? h.envWF.typed.tyMap y).isSome) := by
    intro y ty hy
    obtain ⟨v, hv, -⟩ := he.ann y ty hy
    rw [hT, find?_storeTyMap_of (List.mem_append_left _ (List.mem_map.mpr ⟨_, hy, rfl⟩)) hv]; rfl
  have hann : fvars_annotated_by h.envWF.typed.tyMap e := hT ▸ he.ann.fvars_annotated_by
  obtain ⟨hops', hann', -⟩ := simplifyExpr_preserves h e he.ops hann
  have hcov' := simplifyExpr_namesIn h hcov
  refine ⟨⟨hops', fun y ty hy => ?_, fun y ty hy => ?_⟩,
    fun v hv => simplifyExpr_denoteEval h hmap he.ops hann hcov hv⟩
  · obtain ⟨t, rfl, ht⟩ := fvars_annotated_by_annotated hann' y ty hy
    obtain ⟨t', ht'⟩ := Option.isSome_iff_exists.mp (hcov' y _ hy)
    have ht'' := ht'
    rw [hT] at ht''
    obtain ⟨-, v, hv, hs⟩ := find?_storeTyMap_eq_some ht''
    exact ⟨v, hv, by rw [ht _ ht', hs]⟩
  · obtain ⟨t', ht'⟩ := Option.isSome_iff_exists.mp (hcov' y ty hy)
    rw [hT] at ht'
    exact hNA y (find?_storeTyMap_eq_some ht').1


/-! ## Keeping recorded values sound as the store changes -/

/-- A sound recorded value stays sound in a store that agrees on its variable and on its
    free variables. -/
private theorem ValueGood.transfer {F : Lambda.Factory CoreLParams} {M : ModeledFactory CoreLParams}
    {σ σ' : ValStore CoreLParams} {x : CoreIdent} {r : Expression.Expr}
    (h : ValueGood F M σ x r) (hx : σ' x = σ x)
    (hfv : ∀ y ty, (y, ty) ∈ LExpr.freeVars r → σ' y = σ y) : ValueGood F M σ' x r := by
  obtain ⟨⟨v, hv, he⟩, hops, hann⟩ := h
  refine ⟨⟨v, hx ▸ hv, ?_⟩, hops, fun y ty hy => (hfv y ty hy) ▸ hann y ty hy⟩
  rw [← he]
  exact LExpr.denoteEval_congr r (fun y ty hy => hfv y ty hy)

/-- The free variables of `r` in the sense of `HasFvars`, by name. -/
theorem mem_getFvars_of_freeVars {r : Expression.Expr} {y : CoreIdent} {ty : Option LMonoTy}
    (hy : (y, ty) ∈ LExpr.freeVars r) :
    y ∈ Imperative.HasFvars.getFvars (P := Core.Expression) r := by
  show y ∈ LExpr.LExpr.getVars r
  rw [getVars_eq_freeVars_idents]
  exact List.mem_map.mpr ⟨_, hy, rfl⟩

/-- Forgetting the variables `names` keeps the values sound in any store that agrees with the
    current one outside `names`. -/
theorem ValuesSound.invalidate {ctx : Ctx} {M : ModeledFactory CoreLParams}
    {σ σ' : ValStore CoreLParams} (h : ValuesSound ctx M σ) {names : Std.HashSet String}
    (hσ : ∀ y : CoreIdent, y.name ∉ names → σ' y = σ y) :
    ValuesSound (ctx.invalidate names) M σ' := by
  intro x r hx
  obtain ⟨hm, hxn, hfv⟩ := mem_invalidate hx
  have hfac : (ctx.invalidate names).foldFactory = ctx.foldFactory := by
    unfold Ctx.invalidate Ctx.invalidateBy; split <;> (try split) <;> (try split) <;> rfl
  rw [hfac]
  exact (h x r hm).transfer (hσ x hxn)
    (fun y ty hy => hσ y (hfv y (mem_getFvars_of_freeVars hy)))

/-- Recording, for `x`, a value sound in the store before an assignment of its value keeps
    the context sound in the store after it. -/
theorem ValuesSound.record {ctx : Ctx} {M : ModeledFactory CoreLParams}
    {σ σ' : ValStore CoreLParams} (h : ValuesSound ctx M σ) {x : CoreIdent}
    {e : Expression.Expr} {v : SemValue} (hx : σ' x = some v)
    (hσ : ∀ y : CoreIdent, y ≠ x → σ' y = σ y) (he : e.denoteEval M σ = some v)
    (hops : OpsConsistent ctx.foldFactory e) (hann : StoreAnnotated σ e) :
    ValuesSound (ctx.record x e) M σ' := by
  have hfac : (ctx.record x e).foldFactory = ctx.foldFactory := by
    unfold Ctx.record Ctx.invalidateVar Ctx.invalidateBy; split <;> rfl
  have hold : ∀ y r, (y, r) ∈ (ctx.invalidateVar x).values.toList →
      ValueGood ctx.foldFactory M σ' y r := by
    intro y r hm
    obtain ⟨hm, hyx, hfv⟩ := mem_invalidateVar hm
    exact (h y r hm).transfer (hσ y fun h => hyx (h ▸ rfl))
      (fun z ty hz => hσ z fun h => hfv z (mem_getFvars_of_freeVars hz) (h ▸ rfl))
  intro y r hm
  rw [hfac]
  unfold Ctx.record at hm
  split at hm
  · exact hold y r hm
  · rename_i hnx
    rcases Map.mem_insert hm with heq | hm
    · simp only [Prod.mk.injEq] at heq
      obtain ⟨rfl, rfl⟩ := heq
      have hfv : ∀ z ty, (z, ty) ∈ LExpr.freeVars r → σ' z = σ z := by
        intro z ty hz
        apply hσ
        rintro rfl
        apply hnx
        exact List.any_eq_true.mpr ⟨_, mem_getFvars_of_freeVars hz, by simp⟩
      refine ⟨⟨v, hx, ?_⟩, hops, fun z ty hz => (hfv z ty hz) ▸ hann z ty hz⟩
      rw [← he]
      exact LExpr.denoteEval_congr r (fun z ty hz => hfv z ty hz)
    · exact hold y r hm


/-! ## The context after a branch or a block -/

section Join
open Imperative

/-- Forgetting values keeps the fold factory. -/
private theorem Ctx.invalidate_foldFactory (ctx : Ctx) (names : Std.HashSet String) :
    (ctx.invalidate names).foldFactory = ctx.foldFactory := by
  unfold Ctx.invalidate Ctx.invalidateBy; split <;> (try split) <;> (try split) <;> rfl

/-- Recording the agreed values keeps the fold factory. -/
private theorem recordAgreed_foldFactory :
    ∀ (base : Ctx) (agreed : List (CoreIdent × Expression.Expr)),
    (recordAgreed base agreed).foldFactory = base.foldFactory := by
  intro base agreed
  induction agreed generalizing base with
  | nil => rfl
  | cons p rest ih => exact ih _

/-- Joining the contexts of a branch keeps the fold factory. -/
private theorem Ctx.join_foldFactory (base : Ctx) (live : List Ctx) (a d : Std.HashSet String) :
    (base.join live a d).foldFactory = base.foldFactory := by
  unfold Ctx.join; split
  · rfl
  · rw [recordAgreed_foldFactory, Ctx.invalidate_foldFactory]

/-- An identifier whose name is not among the written names is not written. -/
private theorem not_mem_of_name {w : Std.HashSet String} {l : List CoreIdent}
    (hw : ∀ n, n ∈ w ↔ n ∈ l.map (·.name)) {z : CoreIdent} (hz : z.name ∉ w) : z ∉ l :=
  fun h => hz ((hw _).mpr (List.mem_map.mpr ⟨z, h, rfl⟩))

/-- A value recorded before a statement, under a name the statement does not write and
    mentioning none of its writes, stays sound in the store after it, the statement's run
    being projected back on the store it started from. -/
private theorem ValueGood.after_unwritten {F : Lambda.Factory CoreLParams}
    {M : ModeledFactory CoreLParams} {σ σa : SemanticStore Expression} {vars : List CoreIdent}
    (hframe : ∀ z, z ∉ vars → σa z = σ z) {x : CoreIdent} {r : Expression.Expr}
    (h : ValueGood F M σ x r) (hx : x ∉ vars)
    (hfv : ∀ y ty, (y, ty) ∈ LExpr.freeVars r → y ∉ vars) :
    ValueGood F M (projectStore σ σa) x r := by
  have hp : ∀ z, z ∉ vars → projectStore σ σa z = σ z := fun z hz => by
    simp only [projectStore, hframe z hz]; cases σ z <;> rfl
  exact h.transfer (hp x hx) (fun y ty hy => hp y (hfv y ty hy))

/-- A recorded value equal up to metadata to a sound one is sound. -/
private theorem ValueGood.of_beq {F : Lambda.Factory CoreLParams} {M : ModeledFactory CoreLParams}
    {σ : ValStore CoreLParams} {x : CoreIdent} {v r : Expression.Expr}
    (hb : v.beqIgnoringMetadata r = true) (h : ValueGood F M σ x v) : ValueGood F M σ x r := by
  have he : v.eraseMetadata = r.eraseMetadata := LExpr.replaceMetadata_const_of_beq () hb
  obtain ⟨⟨w, hw, hd⟩, hops, hann⟩ := h
  refine ⟨⟨w, hw, ?_⟩, OpsConsistent_of_eraseMetadata_eq he hops, fun y ty hy => ?_⟩
  · rw [← LExpr.denoteEval_replaceMetadata (T := CoreLParams) M σ (fun _ => default) r,
      ← LExpr.replaceMetadata_const_of_beq default hb,
      LExpr.denoteEval_replaceMetadata (T := CoreLParams)]
    exact hd
  · rw [← LExpr.freeVars_eraseMetadata, ← he, LExpr.freeVars_eraseMetadata] at hy
    exact hann y ty hy

/-- **After a branch.** The values recorded by the join of the arms that can run are sound
    after the arm that ran, projected on the store before the branch, when that arm's
    context is among them. -/
theorem ValuesSound.join {base armCtx : Ctx} {live : List Ctx} {M : ModeledFactory CoreLParams}
    {σ σa : SemanticStore Expression} {w : Writes} {vars defined : List CoreIdent}
    (hbase : ValuesSound base M σ) (harm : ValuesSound armCtx M σa) (hmem : armCtx ∈ live)
    (hfold : armCtx.foldFactory = base.foldFactory) (hw : w.Covers vars defined)
    (hframe : ∀ z, z ∉ vars → σa z = σ z)
    (hundef : ∀ z, z ∉ defined → σ z = none → σa z = none) :
    ValuesSound (base.join live w.vars w.defined) M (projectStore σ σa) := by
  intro y r hm
  rw [Ctx.join_foldFactory]
  rcases mem_join hm with ⟨-, hyd, hall, hfvd⟩ | ⟨hb, hyv, hfvv⟩
  · obtain ⟨v', hv', hb⟩ := hall armCtx hmem
    have hg := (harm y v' hv').of_beq hb
    rw [hfold] at hg
    have hp : ∀ z, z ∉ defined → (σa z).isSome → projectStore σ σa z = σa z := by
      intro z hz hs
      cases h0 : σ z with
      | none => rw [hundef z hz h0] at hs; cases hs
      | some _ => simp [projectStore, h0]
    obtain ⟨⟨v, hv, -⟩, -, hann⟩ := id hg
    exact hg.transfer (hp y (not_mem_of_name hw.defined_iff hyd) (by simp [hv]))
      (fun z ty hz => by
        obtain ⟨u, hu, -⟩ := hann z ty hz
        exact hp z (not_mem_of_name hw.defined_iff (hfvd z (mem_getFvars_of_freeVars hz)))
          (by simp [hu]))
  · exact (hbase y r hb).after_unwritten hframe (not_mem_of_name hw.vars_iff hyv)
      (fun z ty hz => not_mem_of_name hw.vars_iff (hfvv z (mem_getFvars_of_freeVars hz)))

/-- **After a block.** The values the context keeps after a block are sound after the
    block's run, projected on the store before it. -/
theorem ValuesSound.block {ctx : Ctx} {M : ModeledFactory CoreLParams}
    {σ σa : SemanticStore Expression} (ss : List Statement) (hctx : ValuesSound ctx M σ)
    (hframe : ∀ z, z ∉ Block.modifiedOrDefinedVars (P := Expression) (C := Command) ss false →
      σa z = σ z) :
    ValuesSound ({ ctx with values := (simpStmts ctx ss).2.1.values }.invalidate
      (simpStmts ctx ss).2.2.vars) M (projectStore σ σa) := by
  intro y r hm
  rw [Ctx.invalidate_foldFactory]
  have hw := simpStmts_writes ctx ss
  obtain ⟨hm, hyv, hfvv⟩ := mem_invalidate hm
  have hold : (y, r) ∈ ctx.values.toList :=
    simpStmts_values_sub ctx ss hm (fun h => hyv ((hw.vars_iff _).mpr h))
  exact (hctx y r hold).after_unwritten hframe (not_mem_of_name hw.vars_iff hyv)
    (fun z ty hz => not_mem_of_name hw.vars_iff (hfvv z (mem_getFvars_of_freeVars hz)))

end Join

end Core.Simplify
