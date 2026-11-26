/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Cortex.LangDef
import Strata.Languages.Cortex.HeapProps
import Strata.Languages.Core.InstExprTyping
import Strata.DL.Lambda.LExprDenoteEvalProps
import Strata.DL.Lambda.LExprWFProps
import all Strata.DL.Lambda.LExprDenoteEval
import all Strata.DL.Lambda.Denote.LExprDenote
import all Strata.DL.Lambda.Denote.LExprAnnotated
import all Strata.Languages.Cortex.Module

/-! # Every reference of a Cortex run is `Null` or allocated

The relation steps only with writes of references that are `Null` or allocated in the current
heap (`SafeRef`): base commands, field writes and `throw` carry it as a premise, and a call
gives the callee an entry store of such references. This file proves that, from an initial
environment satisfying `CortexInitEnvWF` in which the run starts with safe references
(`SafeStart`), every configuration a run reaches has a store of safe references and a closed
heap (`HeapClosed`), so that the program never holds a dangling reference. The proof is a
preservation argument over the mutually inductive command, call and body relations: an
allocation keeps every allocated reference and changes no field, a field write of a safe
reference keeps the allocated references and the other fields, and a call returns a heap that
keeps the caller's allocated references.

The heap laws of `HeapApiModel` are stated over terms in which some arguments are variables;
the proof moves between such terms by evaluating API operations argument by argument
(`apiCall_inv`, `apiCall_typed`, `apiCall_of`).

## Key results

- `cortex_reachable_safe`: every reachable configuration is safe (`CConfig.Safe`).
- `allocGrows_newObj`, `read_newObj`: an allocation keeps the allocated references and every
  field.
- `allocGrows_write`, `heapClosed_write`: a field write of a safe reference keeps the allocated
  references and a closed heap.
- `apiCall_inv`, `apiCall_typed`, `apiCall_of`: the evaluation of an API operation from the
  values of its arguments.

## Key definitions

- `AllocGrows`: a heap keeps the references allocated in another.
- `CState.Safe`, `CConfig.Safe`: the invariant of states and configurations.
-/

namespace Cortex.Sem

open Imperative Lambda

public section

/-! ## Evaluation of applications -/

section Eval

variable {M : Fac}

/-- The annotation of an application is the application of the annotations. -/
private theorem annotateFvars_app (ann : Core.Expression.Ident → Option LMonoTy) (m) (f a : Expr) :
    (LExpr.app m f a).annotateFvars ann = .app m (f.annotateFvars ann) (a.annotateFvars ann) :=
  rfl

/-- A store that defines an application defines its function and its argument. -/
private theorem defines_app {σ : Store} {tc} {m} {f a : Expr} :
    ValStore.Defines (T := Core.CoreLParams) σ tc (.app m f a) ↔
      ValStore.Defines (T := Core.CoreLParams) σ tc f ∧
        ValStore.Defines (T := Core.CoreLParams) σ tc a := by
  simp only [ValStore.Defines, getVars_eq_freeVars_idents, LExpr.freeVars, List.map_append,
    List.mem_append]
  exact ⟨fun h => ⟨fun x hx => h x (.inl hx), fun x hx => h x (.inr hx)⟩,
    fun h x hx => hx.elim (h.1 x) (h.2 x)⟩

/-- The components of a ground arrow type are ground. -/
private theorem isGround_arrow {a b : LMonoTy} (h : (LMonoTy.arrow a b).IsGround) :
    a.IsGround ∧ b.IsGround := by
  simp only [LMonoTy.IsGround, LMonoTy.arrow, LMonoTy.substTyVars, LMonoTy.substTyVars.map,
    LSort.toMonoTy, LSort.toMonoTy.map, LMonoTy.tcons.injEq, List.cons.injEq, true_and,
    and_true] at h
  exact h

/-- An evaluated expression has a ground type whose sort is its value's. -/
private theorem eval_typed {σ : Store} {e : Expr} {v : SemValue}
    (h : e.denoteEval M σ = some v) :
    ∃ τ, (e.annotateFvars (ValStore.ann (T := Core.CoreLParams) σ)).HasTypeA [] τ ∧
      τ.IsGround ∧ v.sort = τ.substTyVars M.tyVarVal := by
  obtain ⟨-, τ, hτ, hg, rfl⟩ := (LExpr.denoteEval_eq_some_iff (T := Core.CoreLParams)).mp h
  exact ⟨τ, hτ, hg, rfl⟩

/-- A value is of a ground type exactly when its interpretation is the model's and its sort is
the type's. -/
private theorem isOfTy_iff {v : SemValue} {τ : LMonoTy} (hg : τ.IsGround) :
    IsOfTy M v τ ↔ v.tc = M.model.tcInterp ∧ v.sort = τ.substTyVars M.tyVarVal := by
  simp only [IsOfTy, HasVal.valueOfTy, LTy.toMonoType?, Option.some.injEq]
  refine and_congr_right fun _ => ⟨fun h => ?_, fun h => ?_⟩
  · rw [h, LSort.toMonoTy_substTyVars]
  · rw [h, ← hg.substTyVars_eq refTyVarVal M.tyVarVal, hg]

/-- An evaluated expression's value is of the expression's type. -/
private theorem isOfTy_of_eval {σ : Store} {e : Expr} {v : SemValue} {τ : LMonoTy}
    (h : e.denoteEval M σ = some v)
    (hτ : (e.annotateFvars (ValStore.ann (T := Core.CoreLParams) σ)).HasTypeA [] τ) :
    IsOfTy M v τ := by
  obtain ⟨τ', hτ', hg, hs⟩ := eval_typed h
  obtain rfl := HasTypeA_unique hτ hτ'
  exact (isOfTy_iff hg).2 ⟨LExpr.denoteEval_tc h, hs⟩

/-- The denotation of an annotated application applies the denotation of its function to that
of its argument. -/
private theorem denote_app_ann {tc : TyConstrInterp} {op : OpInterp tc}
    {fv : FreeVarVal Core.CoreLParams tc} {vt : TyVarVal} {ann} {m} {f a : Expr} {aty τ : LMonoTy}
    (hF : (f.annotateFvars ann).HasTypeA [] (.arrow aty τ))
    (hA : (a.annotateFvars ann).HasTypeA [] aty)
    {h : ((LExpr.app m f a).annotateFvars ann).HasTypeA [] τ} :
    LExpr.denote tc op fv vt .nil ((LExpr.app m f a).annotateFvars ann) τ h =
      LExpr.denote tc op fv vt .nil (f.annotateFvars ann) _ hF
        (LExpr.denote tc op fv vt .nil (a.annotateFvars ann) aty hA) :=
  denote_app .nil hF hA h

/-- An application of a function and an argument with given values evaluates, in another store,
to the same value when the function and the argument do. -/
private theorem eval_app_of {σ σ' : Store} {m m' : Core.ExpressionMetadata} {f f' a a' : Expr}
    {u w v : SemValue} (h : (LExpr.app m f a).denoteEval M σ = some v)
    (hf : f.denoteEval M σ = some u) (hf' : f'.denoteEval M σ' = some u)
    (ha : a.denoteEval M σ = some w) (ha' : a'.denoteEval M σ' = some w) :
    (LExpr.app m' f' a').denoteEval M σ' = some v := by
  letI := M.model.allInhabited
  obtain ⟨-, τ, hτ, hg, rfl⟩ := (LExpr.denoteEval_eq_some_iff (T := Core.CoreLParams)).mp h
  obtain ⟨aty, hF, hA⟩ := HasTypeA.app_inv hτ
  obtain ⟨-, τf, hτf, hgf, rfl⟩ := (LExpr.denoteEval_eq_some_iff (T := Core.CoreLParams)).mp hf
  obtain ⟨hdf', τf', hτf', hgf', hu⟩ :=
    (LExpr.denoteEval_eq_some_iff (T := Core.CoreLParams)).mp hf'
  obtain ⟨-, τa, hτa, hga, rfl⟩ := (LExpr.denoteEval_eq_some_iff (T := Core.CoreLParams)).mp ha
  obtain ⟨hda', τa', hτa', hga', hw⟩ :=
    (LExpr.denoteEval_eq_some_iff (T := Core.CoreLParams)).mp ha'
  obtain rfl := HasTypeA_unique hτf hF
  obtain rfl := HasTypeA_unique hτa hA
  obtain rfl : τf' = .arrow τa τ :=
    hgf'.eq_of_substTyVars_eq hgf (congrArg SemValue.sort hu).symm
  obtain rfl : τa' = τa := hga'.eq_of_substTyVars_eq hga (congrArg SemValue.sort hw).symm
  have hfu := eq_of_heq (SemValue.mk.inj hu).2.2
  have hwu := eq_of_heq (SemValue.mk.inj hw).2.2
  refine (LExpr.denoteEval_eq_some_iff (T := Core.CoreLParams)).mpr
    ⟨defines_app.2 ⟨hdf', hda'⟩, τ, .app hτf' hτa', hg, ?_⟩
  unfold LExpr.denoteEvalResult
  congr 1
  exact (denote_app_ann hF hA).trans ((congr hfu hwu).trans (denote_app_ann hτf' hτa').symm)

/-- The type of a value is ground. -/
private theorem isGround_of_isOfTy {v : SemValue} {τ : LMonoTy} (hv : IsOfTy M v τ) :
    τ.IsGround := by
  have hτ : τ = v.sort.toMonoTy := by simpa [IsOfTy, HasVal.valueOfTy, LTy.toMonoType?] using hv.2
  exact hτ ▸ LSort.toMonoTy_isGround _

/-- The type of an evaluated expression is the type its value has. -/
private theorem hasType_of_isOfTy {σ : Store} {e : Expr} {v : SemValue} {τ : LMonoTy}
    (h : e.denoteEval M σ = some v) (hv : IsOfTy M v τ) :
    (e.annotateFvars (ValStore.ann (T := Core.CoreLParams) σ)).HasTypeA [] τ := by
  obtain ⟨τ', hτ', hg, hs⟩ := eval_typed h
  have hτ : τ = v.sort.toMonoTy := by simpa [IsOfTy, HasVal.valueOfTy, LTy.toMonoType?] using hv.2
  rw [hτ, hs, ← hg.substTyVars_eq refTyVarVal M.tyVarVal, hg]
  exact hτ'

/-- A variable of the function of an application chain is a variable of the chain. -/
private theorem mem_freeVars_mkApp {x} :
    ∀ (es : List Expr) {g : Expr}, x ∈ g.freeVars → x ∈ (mkApp g es).freeVars
  | [], _, h => h
  | e :: es, g, h => mem_freeVars_mkApp es (g := .app Core.coreLoc g e) (by
      simp only [LExpr.freeVars, List.mem_append]
      exact .inl h)

/-- The function of a well-typed application chain is well typed. -/
private theorem mkApp_spine {ann : Core.Expression.Ident → Option LMonoTy} :
    ∀ (es : List Expr) {g : Expr} {τ}, ((mkApp g es).annotateFvars ann).HasTypeA [] τ →
      ∃ τg, (g.annotateFvars ann).HasTypeA [] τg
  | [], _, _, h => ⟨_, h⟩
  | _ :: es, _, _, h => by
    obtain ⟨_, h1⟩ := mkApp_spine es h
    obtain ⟨_, hF, -⟩ := HasTypeA.app_inv h1
    exact ⟨_, hF⟩

/-- In an evaluated application chain whose function evaluates, the application of the function
to the first argument evaluates, and so does that argument. -/
private theorem eval_mkApp_head {σ : Store} {e g : Expr} {es : List Expr} {u v : SemValue}
    (h : (mkApp g (e :: es)).denoteEval M σ = some v) (hg : g.denoteEval M σ = some u) :
    ∃ aty τ1 u1 w, (LExpr.app Core.coreLoc g e).denoteEval M σ = some u1 ∧
      e.denoteEval M σ = some w ∧ IsOfTy M u (.arrow aty τ1) ∧ IsOfTy M w aty ∧
      IsOfTy M u1 τ1 := by
  obtain ⟨hd, τ, hτ, -, -⟩ := (LExpr.denoteEval_eq_some_iff (T := Core.CoreLParams)).mp h
  obtain ⟨τ1, h1⟩ := mkApp_spine es hτ
  obtain ⟨aty, hF, hA⟩ := HasTypeA.app_inv h1
  obtain ⟨τg, hτg, hgg, -⟩ := eval_typed hg
  obtain rfl := HasTypeA_unique hτg hF
  obtain ⟨hga, hg1⟩ := isGround_arrow hgg
  have hd1 : ValStore.Defines (T := Core.CoreLParams) σ M.model.tcInterp
      (.app Core.coreLoc g e) := hd.mono fun _ ty hx => ⟨ty, mem_freeVars_mkApp es hx⟩
  have ha := LExpr.denoteEval_of_hasTypeA (defines_app.1 hd1).2 hA hga
  have h1e := LExpr.denoteEval_of_hasTypeA hd1 h1 hg1
  exact ⟨aty, τ1, _, _, h1e, ha, isOfTy_of_eval hg hτg, isOfTy_of_eval ha hA,
    isOfTy_of_eval h1e h1⟩

/-- An application chain evaluates, in another store, to the same value when its function
and each of its arguments do. -/
private theorem eval_mkApp_of {σ σ' : Store} :
    ∀ {es es' : List Expr} {g g' : Expr} {u v : SemValue},
      List.Rel₂ (fun e e' => ∀ w, e.denoteEval M σ = some w → e'.denoteEval M σ' = some w)
        es es' →
      (mkApp g es).denoteEval M σ = some v → g.denoteEval M σ = some u →
      g'.denoteEval M σ' = some u → (mkApp g' es').denoteEval M σ' = some v
  | _, _, _, _, _, _, .nil, h, hg, hg' => hg'.trans (hg.symm.trans h)
  | _, _, _, _, _, _, .cons he hes, h, hg, hg' => by
    obtain ⟨_, _, _, _, h1, ha, -⟩ := eval_mkApp_head h hg
    exact eval_mkApp_of (g := .app Core.coreLoc _ _) (g' := .app Core.coreLoc _ _) hes h h1
      (eval_app_of h1 hg hg' ha (he _ ha))

/-- An application chain whose function and arguments evaluate to values of the function's
argument types evaluates to a value of its result type. -/
private theorem eval_mkApp_typed {σ : Store} :
    ∀ {es : List Expr} {ts : List LMonoTy} {g : Expr} {u : SemValue} {res : LMonoTy},
      List.Rel₂ (fun e t => ∃ w, e.denoteEval M σ = some w ∧ IsOfTy M w t) es ts →
      g.denoteEval M σ = some u → IsOfTy M u (ts.foldr LMonoTy.arrow res) →
      ∃ v, (mkApp g es).denoteEval M σ = some v ∧ IsOfTy M v res
  | _, _, _, u, _, .nil, hg, hu => ⟨u, hg, hu⟩
  | _, _, _, _, _, .cons ⟨_, he, hw⟩ hes, hg, hu => by
    have hF := hasType_of_isOfTy hg hu
    have hA := hasType_of_isOfTy he hw
    have hd : ValStore.Defines (T := Core.CoreLParams) σ M.model.tcInterp
        (.app Core.coreLoc _ _) := defines_app.2 ⟨LExpr.denoteEval_defines hg,
          LExpr.denoteEval_defines he⟩
    have h1 := LExpr.denoteEval_of_hasTypeA hd (.app hF hA)
      (isGround_arrow (isGround_of_isOfTy hu)).2
    exact eval_mkApp_typed (g := .app Core.coreLoc _ _) hes h1 (isOfTy_of_eval h1 (.app hF hA))

/-- A value has one type. -/
private theorem isOfTy_unique {v : SemValue} {τ τ' : LMonoTy} (h : IsOfTy M v τ)
    (h' : IsOfTy M v τ') : τ = τ' := by
  have hτ : τ = v.sort.toMonoTy := by simpa [IsOfTy, HasVal.valueOfTy, LTy.toMonoType?] using h.2
  have hτ' : τ' = v.sort.toMonoTy := by
    simpa [IsOfTy, HasVal.valueOfTy, LTy.toMonoType?] using h'.2
  exact hτ.trans hτ'.symm

/-- The arguments of an evaluated application chain, as many as the argument types of a
function that evaluates, evaluate to values of those types, and the chain to a value of the
result type. -/
private theorem eval_mkApp_inv {σ : Store} :
    ∀ {es : List Expr} {ts : List LMonoTy} {g : Expr} {u v : SemValue} {res : LMonoTy},
      es.length = ts.length → (mkApp g es).denoteEval M σ = some v →
      g.denoteEval M σ = some u → IsOfTy M u (ts.foldr LMonoTy.arrow res) →
      List.Rel₂ (fun e t => ∃ w, e.denoteEval M σ = some w ∧ IsOfTy M w t) es ts ∧
        IsOfTy M v res
  | [], [], _, _, _, _, _, h, hg, hu => ⟨.nil, Option.some.inj (hg.symm.trans h) ▸ hu⟩
  | _ :: _, _ :: _, _, _, _, _, hl, h, hg, hu => by
    obtain ⟨_, _, _, w, h1, ha, hu', hw, hu1⟩ := eval_mkApp_head h hg
    have harr := isOfTy_unique hu hu'
    simp only [List.foldr_cons, LMonoTy.arrow, LMonoTy.tcons.injEq, List.cons.injEq,
      and_true, true_and] at harr
    obtain ⟨rfl, rfl⟩ := harr
    obtain ⟨hes, hv⟩ := eval_mkApp_inv (g := .app Core.coreLoc _ _) (Nat.succ.inj hl) h h1 hu1
    exact ⟨.cons ⟨w, ha, hw⟩ hes, hv⟩

/-- A ground type of a function from ground types is ground. -/
private theorem isGround_foldr {res : LMonoTy} (hres : res.IsGround) :
    ∀ {ts : List LMonoTy}, (∀ t ∈ ts, t.IsGround) → (ts.foldr LMonoTy.arrow res).IsGround
  | [], _ => hres
  | t :: ts, h => by
    have ht := h t (List.mem_cons_self ..)
    have hr := isGround_foldr hres fun t' ht' => h t' (List.mem_cons_of_mem _ ht')
    simp only [LMonoTy.IsGround, List.foldr_cons, LMonoTy.arrow, LMonoTy.substTyVars,
      LMonoTy.substTyVars.map, LSort.toMonoTy, LSort.toMonoTy.map] at ht hr ⊢
    rw [ht, hr]

/-- An operator with a ground type evaluates, in every store, to one value of that type. -/
private theorem eval_op {n : String} {ty : LMonoTy} (hg : ty.IsGround) :
    ∃ v, IsOfTy M v ty ∧
      ∀ σ : Store, (LExpr.op Core.coreLoc ⟨n, ()⟩ (some ty) : Expr).denoteEval M σ = some v := by
  refine ⟨⟨M.model.tcInterp, ty.substTyVars M.tyVarVal,
    M.model.opInterp n (ty.substTyVars M.tyVarVal)⟩, (isOfTy_iff hg).2 ⟨rfl, rfl⟩, fun σ => ?_⟩
  rw [LExpr.denoteEval_of_hasTypeA (T := Core.CoreLParams) (fun x hx => by
    simp [getVars_eq_freeVars_idents, LExpr.freeVars] at hx) .op hg]
  rfl

/-- A variable of an API term evaluates to the value its binding gives it, when that value
belongs to the model. -/
private theorem eval_var {bs : List (String × SemValue)} {n : String} {v : SemValue} :
    (apiVar n).denoteEval M (bindStore bs) = some v ↔
      bs.lookup n = some v ∧ v.tc = M.model.tcInterp := by
  refine ⟨fun h => ?_, fun h => LExpr.denoteEval_fvar h.1 h.2⟩
  obtain ⟨w, hw, htc⟩ := LExpr.denoteEval_defines h ⟨n, ()⟩
    (by simp [apiVar, mkFvar, getVars_eq_freeVars_idents, LExpr.freeVars])
  obtain rfl := Option.some.inj ((LExpr.denoteEval_fvar hw htc).symm.trans h)
  exact ⟨hw, htc⟩

/-- The type of an application chain, of as many arguments as its function has argument types,
is the function's result type. -/
private theorem mkApp_type {ann : Core.Expression.Ident → Option LMonoTy} :
    ∀ {es : List Expr} {ts : List LMonoTy} {g : Expr} {res τ : LMonoTy}, es.length = ts.length →
      (g.annotateFvars ann).HasTypeA [] (ts.foldr LMonoTy.arrow res) →
      ((mkApp g es).annotateFvars ann).HasTypeA [] τ → τ = res
  | [], [], _, _, _, _, hg, h => HasTypeA_unique h hg
  | _ :: es, _ :: _, _, _, _, hl, hg, h => by
    obtain ⟨_, h1⟩ := mkApp_spine es h
    obtain ⟨_, hF, -⟩ := HasTypeA.app_inv h1
    have harr := HasTypeA_unique hF hg
    simp only [List.foldr_cons, LMonoTy.arrow, LMonoTy.tcons.injEq, List.cons.injEq,
      and_true, true_and] at harr
    exact mkApp_type (g := .app Core.coreLoc _ _) (Nat.succ.inj hl) (harr.2 ▸ h1) h

end Eval

/-! ## Evaluation of API terms -/

section Api

variable {f : Fac} {bs bs' : List (String × SemValue)}

/-- The result type of an evaluated API operation is ground. -/
private theorem apiCall_res_ground {n : String} {ts : List LMonoTy} {res : LMonoTy}
    {es : List Expr} {v : SemValue} (h : apiEval f bs (apiCall n ts res es) = some v)
    (hl : es.length = ts.length) : res.IsGround := by
  obtain ⟨τ, hτ, hg, -⟩ := eval_typed h
  exact mkApp_type hl .op hτ ▸ hg

/-- The arguments of an evaluated API operation with ground argument types evaluate to values
of those types, and the operation to a value of its result type. -/
theorem apiCall_inv {n : String} {ts : List LMonoTy} {res : LMonoTy} {es : List Expr}
    {v : SemValue} (h : apiEval f bs (apiCall n ts res es) = some v)
    (hts : ∀ t ∈ ts, t.IsGround) (hl : es.length = ts.length) :
    List.Rel₂ (fun e t => ∃ w, apiEval f bs e = some w ∧ IsOfTy f w t) es ts ∧
      IsOfTy f v res := by
  obtain ⟨u, hu, hop⟩ := eval_op (M := f) (n := n) (isGround_foldr (apiCall_res_ground h hl) hts)
  exact eval_mkApp_inv hl h (hop _) hu

/-- An API operation whose arguments evaluate to values of its argument types evaluates to a
value of its result type, when that is ground. -/
theorem apiCall_typed {n : String} {ts : List LMonoTy} {res : LMonoTy} {es : List Expr}
    (hes : List.Rel₂ (fun e t => ∃ w, apiEval f bs e = some w ∧ IsOfTy f w t) es ts)
    (hres : res.IsGround) :
    ∃ v, apiEval f bs (apiCall n ts res es) = some v ∧ IsOfTy f v res := by
  have hts : ∀ t ∈ ts, t.IsGround := by
    clear hres
    induction hes with
    | nil => nofun
    | cons ht _ ih =>
      obtain ⟨_, -, hw⟩ := ht
      exact fun t h => (List.mem_cons.1 h).elim (· ▸ isGround_of_isOfTy hw) (ih t)
  obtain ⟨u, hu, hop⟩ := eval_op (M := f) (n := n) (isGround_foldr hres hts)
  exact eval_mkApp_typed hes (hop _) hu

/-- An evaluated API operation with ground argument types evaluates, under other bindings, to
the same value when each argument does. -/
theorem apiCall_of {n : String} {ts : List LMonoTy} {res : LMonoTy} {es es' : List Expr}
    {v : SemValue} (h : apiEval f bs (apiCall n ts res es) = some v)
    (hts : ∀ t ∈ ts, t.IsGround) (hl : es.length = ts.length)
    (hes : List.Rel₂ (fun e e' => ∀ w, apiEval f bs e = some w → apiEval f bs' e' = some w)
      es es') :
    apiEval f bs' (apiCall n ts res es') = some v := by
  obtain ⟨_, -, hop⟩ := eval_op (M := f) (n := n) (isGround_foldr (apiCall_res_ground h hl) hts)
  exact eval_mkApp_of hes h (hop _) (hop _)

/-- A variable of an API term evaluates to its binding, when that belongs to the model. -/
private theorem apiEval_var {n : String} {v : SemValue} :
    apiEval f bs (apiVar n) = some v ↔ bs.lookup n = some v ∧ v.tc = f.model.tcInterp :=
  eval_var

/-- A variable evaluates under other bindings to the value it evaluates to, when they bind a
variable to the same value. -/
private theorem var_to {a b : String} (h : bs'.lookup b = bs.lookup a) :
    ∀ w, apiEval f bs (apiVar a) = some w → apiEval f bs' (apiVar b) = some w := fun _ hw =>
  have hw := apiEval_var.1 hw
  apiEval_var.2 ⟨h.trans hw.1, hw.2⟩

/-- A term evaluates under other bindings to a variable bound to its value. -/
private theorem to_var {e : Expr} {b : String} {w₀ : SemValue} (he : apiEval f bs e = some w₀)
    (hb : bs'.lookup b = some w₀) :
    ∀ w, apiEval f bs e = some w → apiEval f bs' (apiVar b) = some w := fun _ hw =>
  Option.some.inj (he.symm.trans hw) ▸ apiEval_var.2 ⟨hb, LExpr.denoteEval_tc he⟩

/-- A variable bound to a value evaluates under other bindings to a term with that value. -/
private theorem var_from {e : Expr} {a : String} {w₀ : SemValue} (he : apiEval f bs' e = some w₀)
    (ha : bs.lookup a = some w₀) :
    ∀ w, apiEval f bs (apiVar a) = some w → apiEval f bs' e = some w := fun _ hw =>
  Option.some.inj ((apiEval_var.1 hw).1.symm.trans ha) ▸ he

/-- A term without variables evaluates to the same value under all bindings. -/
private theorem closed_to {e : Expr} (he : e.freeVars = []) :
    ∀ w, apiEval f bs e = some w → apiEval f bs' e = some w := fun _ hw =>
  (LExpr.denoteEval_congr (M := f) e fun _ _ hx => by simp [he] at hx).symm.trans hw

/-- A Boolean value of an API term makes the term hold or fail. -/
private theorem holds_or_fails {e : Expr} {v : SemValue} (h : apiEval f bs e = some v)
    (hv : IsOfTy f v .bool) : apiHolds f bs e ∨ apiFails f bs e :=
  (Core.valueOfTy_bool f v hv).imp (h.trans <| congrArg some ·) (h.trans <| congrArg some ·)

/-- An equality of two variables holds only when they are bound to the same value. -/
private theorem eq_of_holds {a b : String} {x y : SemValue} (hx : bs.lookup a = some x)
    (hy : bs.lookup b = some y) (h : apiHolds f bs (.eq Core.coreLoc (apiVar a) (apiVar b))) :
    x = y := by
  obtain ⟨-, τ, hτ, -, -⟩ := (LExpr.denoteEval_eq_some_iff (T := Core.CoreLParams)).mp h
  obtain ⟨ty, -, ha, hb⟩ := HasTypeA.eq_inv hτ
  have hxt : x.tc = f.model.tcInterp := (LExpr.denoteEval_defines h ⟨a, ()⟩ (by
    simp [apiVar, mkFvar, getVars_eq_freeVars_idents, LExpr.freeVars])).elim
      fun w ⟨hw, htc⟩ => (Option.some.inj (hw.symm.trans hx)) ▸ htc
  have hyt : y.tc = f.model.tcInterp := (LExpr.denoteEval_defines h ⟨b, ()⟩ (by
    simp [apiVar, mkFvar, getVars_eq_freeVars_idents, LExpr.freeVars])).elim
      fun w ⟨hw, htc⟩ => (Option.some.inj (hw.symm.trans hy)) ▸ htc
  have hex := apiEval_var (f := f) (bs := bs) |>.2 ⟨hx, hxt⟩
  have hey := apiEval_var (f := f) (bs := bs) |>.2 ⟨hy, hyt⟩
  have hs : x.sort = y.sort := LSort.toMonoTy_injective <|
    (isOfTy_unique (isOfTy_of_eval hex ha) ((isOfTy_iff (LSort.toMonoTy_isGround _)).2
      ⟨hxt, (LSort.toMonoTy_substTyVars _ _).symm⟩)).symm.trans
    (isOfTy_unique (isOfTy_of_eval hey hb) ((isOfTy_iff (LSort.toMonoTy_isGround _)).2
      ⟨hyt, (LSort.toMonoTy_substTyVars _ _).symm⟩))
  refine Classical.byContradiction fun hne => ?_
  exact HasBool.ttVal_ne_ffVal (P := Core.Expression) f
    (Option.some.inj (h.symm.trans (LExpr.denoteEval_eq_false hex hey hs hne)))

end Api

/-! ## Safe references -/

section Safe

variable {Γ : UnorderedProgram} {f : Fac}

/-- The sort of location sets is a ground type. -/
private theorem locsTy_ground : locsTy.IsGround := rfl
/-- The sort of field identities is a ground type. -/
private theorem fieldIdTy_ground : fieldIdTy.IsGround := rfl
/-- The Boolean type is ground. -/
private theorem bool_ground : LMonoTy.bool.IsGround := rfl

/-- The sort of the fields of a ground type is ground. -/
private theorem fieldTy_ground {t : LMonoTy} (ht : t.IsGround) : (fieldTy t).IsGround := by
  simp only [LMonoTy.IsGround, fieldTy, LMonoTy.substTyVars, LMonoTy.substTyVars.map,
    LSort.toMonoTy, LSort.toMonoTy.map] at ht ⊢
  rw [ht]

/-- The two components of a relation between two lists of two elements. -/
private theorem rel₂_two {α β} {R : α → β → Prop} {a b : α} {s t : β}
    (h : List.Rel₂ R [a, b] [s, t]) : R a s ∧ R b t := by
  cases h with | cons h1 h => cases h with | cons h2 _ => exact ⟨h1, h2⟩

/-- The three components of a relation between two lists of three elements. -/
private theorem rel₂_three {α β} {R : α → β → Prop} {a b c : α} {s t u : β}
    (h : List.Rel₂ R [a, b, c] [s, t, u]) : R a s ∧ R b t ∧ R c u := by
  cases h with | cons h1 h => cases h with | cons h2 h => cases h with | cons h3 _ =>
    exact ⟨h1, h2, h3⟩

/-- A variable evaluates to its binding. -/
private theorem var_val {bs : List (String × SemValue)} {n : String} {v w : SemValue}
    (hl : bs.lookup n = some w) (h : apiEval f bs (apiVar n) = some v) : v = w :=
  Option.some.inj ((apiEval_var.1 h).1.symm.trans hl)

/-- An evaluated test of allocation binds a heap and a reference. -/
private theorem allocated_typed {h o b : SemValue}
    (ha : apiEval f [("$h", h), ("$o", o)] (allocatedT (apiVar "$h") (apiVar "$o")) = some b) :
    IsOfTy f h heapTy ∧ IsOfTy f o refTy := by
  obtain ⟨⟨_, hh, th⟩, ⟨_, ho, tho⟩⟩ :=
    rel₂_two (apiCall_inv ha (by simp only [List.forall_mem_cons]; exact ⟨rfl, rfl, nofun⟩) rfl).1
  exact ⟨var_val rfl hh ▸ th, var_val rfl ho ▸ tho⟩

/-- A value of another type than `Ref` is a safe reference. -/
theorem safeRef_of_isOfTy {h v : SemValue} {t : LMonoTy} (hv : IsOfTy f v t) (ht : t ≠ refTy) :
    SafeRef f h v := fun hr => absurd (isOfTy_unique hv hr) ht

/-- A Boolean is a safe reference. -/
private theorem safeRef_ofBool {h : SemValue} (b : Bool) :
    SafeRef f h (SemValue.ofBool f.model.tcInterp b) :=
  safeRef_of_isOfTy (t := .bool) ⟨rfl, rfl⟩ (by decide)

/-- The references allocated in `h` are allocated in `h'`. -/
@[expose] def AllocGrows (f : Fac) (h h' : SemValue) : Prop :=
  ∀ o, IsOfTy f o refTy →
    apiHolds f [("$h", h), ("$o", o)] (allocatedT (apiVar "$h") (apiVar "$o")) →
    apiHolds f [("$h", h'), ("$o", o)] (allocatedT (apiVar "$h") (apiVar "$o"))

/-- A safe reference stays safe in a heap that keeps the allocated references. -/
theorem SafeRef.mono {h h' v : SemValue} (hg : AllocGrows f h h') (hs : SafeRef f h v) :
    SafeRef f h' v := fun hr => (hs hr).imp id (hg v hr)

/-- A store of safe references stays one in a heap that keeps the allocated references. -/
theorem StoreSafe.mono {h h' : SemValue} {σ : Store} (hg : AllocGrows f h h')
    (hs : StoreSafe f h σ) : StoreSafe f h' σ := fun x v hx => (hs x v hx).mono hg

/-- The field declaration a field access reads is one of the program's fields. -/
theorem findField?_mem {r : FieldRef} {d : FieldDecl} (h : Γ.findField? r = some d) :
    (r, d) ∈ programFields Γ := by
  simp only [UnorderedProgram.findField?, UnorderedProgram.findComposite?,
    Option.bind_eq_some_iff] at h
  obtain ⟨c, hc, hd⟩ := h
  have hcn : c.name = r.owner := by simpa using List.find?_some hc
  have hdn : d.name = r.field := by simpa using List.find?_some hd
  simp only [programFields, List.mem_flatMap, List.mem_map]
  exact ⟨c, List.mem_of_find?_eq_some hc, d, List.mem_of_find?_eq_some hd, by
    rw [hcn, hdn]⟩

end Safe

/-! ## The heap commands keep the references safe -/

section Heap

variable {Γ : UnorderedProgram} {f : Fac}

/-- An operator of a ground type evaluates to one value of that type under all bindings. -/
private theorem apiEval_op {n : String} {ty : LMonoTy} (hg : ty.IsGround) :
    ∃ v, IsOfTy f v ty ∧
      ∀ bs, apiEval f bs (LExpr.op Core.coreLoc ⟨n, ()⟩ (some ty)) = some v :=
  (eval_op hg).imp fun _ ⟨hv, h⟩ => ⟨hv, fun _ => h _⟩

/-- Closes the groundness of the argument types of an API operation. -/
local macro "grounds" : tactic => `(tactic| (
  simp only [List.forall_mem_cons, List.forall_mem_nil, and_true]
  (repeat' constructor) <;>
    first
    | rfl
    | exact fun _ h => nomatch h
    | assumption
    | (apply fieldTy_ground; assumption)))

/-- The identity of a field of a ground type evaluates, under all bindings, to one value. -/
private theorem fieldId_eval (r : FieldRef) {t : LMonoTy} (ht : t.IsGround) :
    ∃ k, IsOfTy f k fieldIdTy ∧ ∀ bs, apiEval f bs (fieldIdT t (fieldConst r t)) = some k := by
  obtain ⟨c, hc, hce⟩ := apiEval_op (f := f) (n := s!"{r.owner}.{r.field}") (fieldTy_ground ht)
  obtain ⟨k, hke, hk⟩ := apiCall_typed (f := f) (bs := []) (n := "Field.id")
    (.cons ⟨c, hce _, hc⟩ .nil) fieldIdTy_ground
  exact ⟨k, hk, fun _ => closed_to rfl _ hke⟩

/-- An allocation keeps the allocated references. -/
theorem allocGrows_newObj (hm : HeapApiModel Γ f) {h v h' : SemValue} {ty : TypeName}
    (hn : NewObj f h ty v h') : AllocGrows f h h' := by
  obtain ⟨hfresh, halloc, -, -, hgrows, -⟩ := hn
  exact (hm.grows h h' (allocated_typed hfresh).1 (allocated_typed halloc).1).1 hgrows

/-- An allocation changes no field: a field of a reference reads after it what it read
before. -/
theorem read_newObj (hm : HeapApiModel Γ f) {h v h' o w : SemValue} {ty : TypeName}
    (hn : NewObj f h ty v h') {r : FieldRef} {d : FieldDecl} (hd : Γ.findField? r = some d)
    (ho : IsOfTy f o refTy)
    (hr : apiEval f [("$h", h'), ("$o", o)]
      (readT (fieldMonoTy Γ d) (apiVar "$h") (apiVar "$o") (fieldConst r (fieldMonoTy Γ d))) =
      some w) :
    apiEval f [("$h", h), ("$o", o)]
      (readT (fieldMonoTy Γ d) (apiVar "$h") (apiVar "$o") (fieldConst r (fieldMonoTy Γ d))) =
      some w := by
  obtain ⟨hfresh, halloc, -, -, -, hmod⟩ := hn
  have ht := apiCall_res_ground hr rfl
  obtain ⟨L, hL, hLe⟩ := apiEval_op (f := f) (n := "Locs.none") locsTy_ground
  obtain ⟨k, hk, hke⟩ := fieldId_eval (f := f) r ht
  have hmod' : apiHolds f [("$h", h), ("$h'", h'), ("$L", L)]
      (onlyModifiesT (apiVar "$h") (apiVar "$h'") (apiVar "$L")) :=
    apiCall_of hmod (by grounds) rfl
      (.cons (var_to rfl) (.cons (var_to rfl) (.cons (to_var (hLe _) rfl) .nil)))
  have hmem : apiFails f [("$L", L), ("$o", o)] (locsMemT (apiVar "$L") (apiVar "$o")
      (fieldIdT (fieldMonoTy Γ d) (fieldConst r (fieldMonoTy Γ d)))) :=
    apiCall_of (hm.memNone o k ho hk) (by grounds) rfl
      (.cons (to_var (hLe _) rfl) (.cons (var_to rfl) (.cons (var_from (hke _) rfl) .nil)))
  exact (hm.frame r d (findField?_mem hd) h h' L o (allocated_typed hfresh).1
    (allocated_typed halloc).1 hL ho hmod' hmem).symm.trans hr

/-- A field write keeps the allocated references. -/
theorem allocGrows_write (hm : HeapApiModel Γ f) {h v w h' : SemValue} {r : FieldRef}
    {d : FieldDecl} (hd : Γ.findField? r = some d) (hh : IsOfTy f h heapTy)
    (hv : IsOfTy f v refTy) (hw : IsOfTy f w (fieldMonoTy Γ d))
    (hwr : apiEval f [("$h", h), ("$o", v), ("$w", w)]
      (writeT (fieldMonoTy Γ d) (apiVar "$h") (apiVar "$o") (fieldConst r (fieldMonoTy Γ d))
        (apiVar "$w")) = some h') :
    AllocGrows f h h' := fun p hp ha =>
  (hm.writeKeepsAllocated r d (findField?_mem hd) h v w h' p hh hv hw hp hwr).trans ha

/-- A field write of a safe reference keeps a heap closed: the written field reads the written
value, and every other field of every reference reads what it read before. -/
theorem heapClosed_write (hm : HeapApiModel Γ f) {h v w h' : SemValue} {r : FieldRef}
    {d : FieldDecl} (hd : Γ.findField? r = some d) (hh : IsOfTy f h heapTy)
    (hv : IsOfTy f v refTy) (hw : IsOfTy f w (fieldMonoTy Γ d))
    (hwr : apiEval f [("$h", h), ("$o", v), ("$w", w)]
      (writeT (fieldMonoTy Γ d) (apiVar "$h") (apiVar "$o") (fieldConst r (fieldMonoTy Γ d))
        (apiVar "$w")) = some h')
    (hsw : SafeRef f h w) (hc : HeapClosed Γ f h) : HeapClosed Γ f h' := by
  intro r' d' hd' o' w' ho' hr'
  have hrd := findField?_mem hd
  have ht := isGround_of_isOfTy hw
  have ht' := apiCall_res_ground hr' rfl
  have hgr := allocGrows_write hm hd hh hv hw hwr
  have hh' := (apiCall_inv hwr (by grounds) rfl).2
  have hmod := hm.writeOnlyModifies r d hrd h v w h' hh hv hw hwr
  obtain ⟨-, -, L, hLe, hL⟩ := rel₂_three (apiCall_inv hmod (by grounds) rfl).1
  have hmod' : apiHolds f [("$h", h), ("$h'", h'), ("$L", L)]
      (onlyModifiesT (apiVar "$h") (apiVar "$h'") (apiVar "$L")) :=
    apiCall_of hmod (by grounds) rfl
      (.cons (var_to rfl) (.cons (var_to rfl) (.cons (to_var hLe rfl) .nil)))
  obtain ⟨j, hj, hje⟩ := fieldId_eval (f := f) r ht
  obtain ⟨k', hk', hke'⟩ := fieldId_eval (f := f) r' ht'
  obtain ⟨b, hbe, hb⟩ := apiCall_typed (f := f) (bs := [("$L", L), ("$o", o')])
    (n := "Locs.mem") (es := [apiVar "$L", apiVar "$o",
      fieldIdT (fieldMonoTy Γ d') (fieldConst r' (fieldMonoTy Γ d'))])
    (.cons ⟨L, apiEval_var.2 ⟨rfl, hL.1⟩, hL⟩
      (.cons ⟨o', apiEval_var.2 ⟨rfl, ho'.1⟩, ho'⟩ (.cons ⟨k', hke' _, hk'⟩ .nil))) bool_ground
  rcases holds_or_fails hbe hb with hmem | hmem
  · have hat : apiEval f [("$p", v), ("$j", j), ("$o", o'), ("$k", k')]
        (locsAtT (apiVar "$p") (apiVar "$j")) = some L :=
      apiCall_of hLe (by grounds) rfl (.cons (var_to rfl) (.cons (to_var (hje _) rfl) .nil))
    have hmem4 : apiHolds f [("$p", v), ("$j", j), ("$o", o'), ("$k", k')]
        (locsMemT (locsAtT (apiVar "$p") (apiVar "$j")) (apiVar "$o") (apiVar "$k")) :=
      apiCall_of hmem (by grounds) rfl
        (.cons (var_from hat rfl) (.cons (var_to rfl) (.cons (to_var (hke' _) rfl) .nil)))
    obtain ⟨heo, hek⟩ := (hm.memAt v j o' k' hv hj ho' hk').1 hmem4
    obtain rfl := eq_of_holds rfl rfl heo
    obtain rfl := eq_of_holds rfl rfl hek
    by_cases hrr : r' = r
    · subst hrr
      obtain rfl : d' = d := Option.some.inj (hd'.symm.trans hd)
      obtain rfl :=
        Option.some.inj ((hm.readWriteSame r' d' hrd h o' w h' hh hv hw hwr).symm.trans hr')
      exact hsw.mono hgr
    · exact absurd (LExpr.denoteEval_eq_true (hke' []) (hje []))
        (not_holds_of_fails (hm.fieldIdsDistinct r' d' (findField?_mem hd') r d hrd hrr))
  · have hfr := hm.frame r' d' (findField?_mem hd') h h' L o' hh hh' hL ho' hmod' hmem
    exact (hc r' d' hd' o' w' ho' (hfr.symm.trans hr')).mono hgr

end Heap

/-! ## Stores of safe references -/

section Store

variable {f : Fac} {h : SemValue}

/-- An update by a safe reference keeps a store of safe references. -/
private theorem StoreSafe.updateState {σ σ' : Store} {x v} (hs : StoreSafe f h σ)
    (hu : UpdateState Core.Expression σ x v σ') (hv : SafeRef f h v) : StoreSafe f h σ' := by
  obtain ⟨-, hx, hy⟩ := hu
  intro y u hyu
  by_cases hxy : x = y
  · subst hxy
    exact Option.some.inj (hx.symm.trans hyu) ▸ hv
  · exact hs y u ((hy y hxy).symm.trans hyu)

/-- An update by safe references keeps a store of safe references. -/
private theorem StoreSafe.updateStates {σ σ' : Store} {xs vs} (hs : StoreSafe f h σ)
    (hu : UpdateStates σ xs vs σ') (hv : ∀ v ∈ vs, SafeRef f h v) : StoreSafe f h σ' := by
  induction hu with
  | update_none => exact hs
  | update_some h1 _ ih =>
    exact ih (hs.updateState h1 (hv _ (List.mem_cons_self ..)))
      fun v hv' => hv v (List.mem_cons_of_mem _ hv')

/-- The values read from a store of safe references are safe references. -/
theorem StoreSafe.readValues {σ : Store} {xs vs} (hs : StoreSafe f h σ)
    (hr : ReadValues f σ xs vs) : ∀ v ∈ vs, SafeRef f h v := by
  induction hr with
  | read_none => nofun
  | read_some hx _ _ ih =>
    exact fun v hv => (List.mem_cons.1 hv).elim (· ▸ hs _ _ hx) (ih v)

/-- Copying the globals back from a store of safe references keeps a store of safe
references. -/
private theorem StoreSafe.globalsBack {Γ : UnorderedProgram} {σ σE σ' : Store}
    (hs : StoreSafe f h σ) (hE : StoreSafe f h σE) (hg : GlobalsBack Γ f σ σE σ') :
    StoreSafe f h σ' :=
  have ⟨_, hr, hu⟩ := hg
  hs.updateStates hu (hE.readValues hr)

/-- Binding a safe reference keeps a store of safe references. -/
theorem StoreSafe.update {σ : Store} {x v} (hs : StoreSafe f h σ) (hv : SafeRef f h v) :
    StoreSafe f h (σ.update x v) := fun y u hy => by
  simp only [SemanticStore.update] at hy
  split at hy
  · exact Option.some.inj hy ▸ hv
  · exact hs y u hy

/-- The values an initialization binds differently are the initialized value. -/
theorem safe_writes_initState {σ σ' : Store} {x v} (hi : InitState Core.Expression σ x v σ')
    (hv : SafeRef f h v) : ∀ y u, σ' y = some u → σ y ≠ some u → SafeRef f h u := by
  obtain ⟨-, hx, hy⟩ := hi
  intro y u hu hne
  by_cases hxy : x = y
  · subst hxy
    exact Option.some.inj (hx.symm.trans hu) ▸ hv
  · exact absurd ((hy y hxy).symm.trans hu) hne

/-- The values an update binds differently are the updated value. -/
theorem safe_writes_updateState {σ σ' : Store} {x v} (hi : UpdateState Core.Expression σ x v σ')
    (hv : SafeRef f h v) : ∀ y u, σ' y = some u → σ y ≠ some u → SafeRef f h u := by
  obtain ⟨-, hx, hy⟩ := hi
  intro y u hu hne
  by_cases hxy : x = y
  · subst hxy
    exact Option.some.inj (hx.symm.trans hu) ▸ hv
  · exact absurd ((hy y hxy).symm.trans hu) hne

/-- The values a point update binds differently are the bound value. -/
theorem safe_writes_update {σ : Store} {x v} (hv : SafeRef f h v) :
    ∀ y u, σ.update x v y = some u → σ y ≠ some u → SafeRef f h u := fun y u hu hne => by
  simp only [SemanticStore.update] at hu
  split at hu
  · exact Option.some.inj hu ▸ hv
  · exact absurd hu hne

/-- The empty store holds only safe references. -/
theorem storeSafe_empty : StoreSafe f h emptyStore := fun _ _ h => nomatch h

end Store

/-! ## The invariant -/

section Invariant

variable {Γ : UnorderedProgram} {f : Fac}

/-- The state `s` has the factory `f`, a store of safe references in its heap, and a closed
heap. -/
@[expose] def CState.Safe (Γ : UnorderedProgram) (f : Fac) (s : CState) : Prop :=
  s.env.factory = f ∧ StoreSafe f s.heap s.env.store ∧ HeapClosed Γ f s.heap

/-- The state of the configuration `c` is safe (`CState.Safe`), and so is the exception of a
`raised` configuration. A `terminal` configuration has no heap. -/
@[expose] def CConfig.Safe (Γ : UnorderedProgram) (f : Fac) : CConfig → Prop
  | .atBlock _ _ s | .inBlock _ _ _ _ s | .returned s => s.Safe Γ f
  | .raised s v => s.Safe Γ f ∧ SafeRef f s.heap v
  | .terminal _ => True

/-- The heap of a configuration; a `terminal` configuration has none. -/
private def CConfig.heap? : CConfig → Option SemValue
  | .atBlock _ _ s | .inBlock _ _ _ _ s | .returned s | .raised s _ => some s.heap
  | .terminal _ => none

/-- The heap of `c'` keeps the references allocated in the heap of `c`, and `c'` has no heap
when `c` has none. -/
private def CConfig.Grows (f : Fac) (c c' : CConfig) : Prop :=
  (∀ h, c.heap? = some h → ∀ h', c'.heap? = some h' → AllocGrows f h h') ∧
    (c.heap? = none → c'.heap? = none)

/-- The exception of an outcome, if any, is a safe reference in `h`. -/
private def OutSafe (f : Fac) (h : SemValue) : COutcome → Prop
  | .normal => True
  | .exn v => SafeRef f h v

/-- The result of a body run from a state whose heap is `h₀` is safe and keeps the references
allocated in `h₀`. -/
private def ResultSafe (Γ : UnorderedProgram) (f : Fac) (h₀ : SemValue) : RunResult → Prop
  | .returned s => s.Safe Γ f ∧ AllocGrows f h₀ s.heap
  | .raised s v => s.Safe Γ f ∧ SafeRef f s.heap v ∧ AllocGrows f h₀ s.heap

/-- A heap keeps its own allocated references. -/
private theorem AllocGrows.refl {h : SemValue} : AllocGrows f h h := fun _ _ ha => ha

/-- Keeping the allocated references composes. -/
private theorem AllocGrows.trans {h h' h'' : SemValue} (g : AllocGrows f h h')
    (g' : AllocGrows f h' h'') : AllocGrows f h h'' := fun o ho ha => g' o ho (g o ho ha)

/-- Two configurations with heaps, the second keeping the references allocated in the first. -/
private theorem CConfig.Grows.of {c c' : CConfig} {h h' : SemValue} (g : AllocGrows f h h')
    (hc : c.heap? = some h) (hc' : c'.heap? = some h') : CConfig.Grows f c c' :=
  ⟨fun _ h1 _ h2 => Option.some.inj (hc.symm.trans h1) ▸ Option.some.inj (hc'.symm.trans h2) ▸ g,
    fun hn => nomatch hc.symm.trans hn⟩

/-- A configuration keeps its own allocated references. -/
private theorem CConfig.Grows.refl {c : CConfig} : CConfig.Grows f c c :=
  ⟨fun _ h1 _ h2 => Option.some.inj (h1.symm.trans h2) ▸ AllocGrows.refl, id⟩

/-- Keeping the allocated references composes along configurations. -/
private theorem CConfig.Grows.trans {c c₁ c' : CConfig} (g : CConfig.Grows f c c₁)
    (g' : CConfig.Grows f c₁ c') : CConfig.Grows f c c' := by
  refine ⟨fun h hc h' hc' => ?_, fun hn => g'.2 (g.2 hn)⟩
  cases h₁ : c₁.heap? with
  | none => exact nomatch hc'.symm.trans (g'.2 h₁)
  | some h₁' => exact (g.1 h hc h₁' h₁).trans (g'.1 h₁' h₁ h' hc')

/-- Every configuration a run of the relation reaches from a safe configuration is safe, and
its heap keeps the references allocated in the heap of the start: by induction over the
mutually inductive command, call and body relations, each command keeps the state safe and the
allocated references. -/
private theorem trace_safe (hm : HeapApiModel Γ f) {c evs c'}
    (h : ReflTransTrace (StepCortex Γ (EvalIRCmd Γ)) c evs c') :
    c.Safe Γ f → c'.Safe Γ f ∧ CConfig.Grows f c c' := by
  refine EvalIRCmd.rec_1
    (motive_1 := fun s _ s' o _ _ => s.Safe Γ f →
      s'.Safe Γ f ∧ AllocGrows f s.heap s'.heap ∧ OutSafe f s'.heap o)
    (motive_2 := fun s _ _ _ _ s' o _ _ => s.Safe Γ f →
      s'.Safe Γ f ∧ AllocGrows f s.heap s'.heap ∧ OutSafe f s'.heap o)
    (motive_3 := fun _ s₀ _ r _ => s₀.Safe Γ f → ResultSafe Γ f s₀.heap r)
    (motive_4 := fun c _ c' _ => c.Safe Γ f → c'.Safe Γ f ∧ CConfig.Grows f c c')
    (motive_5 := fun c _ c' _ => c.Safe Γ f → c'.Safe Γ f ∧ CConfig.Grows f c c')
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ h
  · rintro s c σ' evs - hw ⟨hf, hs, hc⟩
    refine ⟨⟨hf, fun x v hx => ?_, hc⟩, AllocGrows.refl, trivial⟩
    by_cases hold : s.env.store x = some v
    · exact hs x v hold
    · exact hf ▸ hw x v hx hold
  · rintro s x ty md cd v h' σ' - hn - hu ⟨rfl, hs, hc⟩
    have hg := allocGrows_newObj hm hn
    exact ⟨⟨rfl, (hs.mono hg).updateState hu fun _ => .inr hn.2.1,
      fun r d hd o w ho hr => (hc r d hd o w ho (read_newObj hm hn hd ho hr)).mono hg⟩, hg,
      trivial⟩
  · rintro s x obj r md v d w σ' - ha hd hr hu ⟨rfl, hs, hc⟩
    exact ⟨⟨rfl, hs.updateState hu (hc r d hd v w (allocated_typed ha).2 hr), hc⟩,
      AllocGrows.refl, trivial⟩
  · rintro s obj r rhs md v w d h' - ha - hsw hd hw hwr ⟨rfl, hs, hc⟩
    obtain ⟨hh, hv⟩ := allocated_typed ha
    have hg := allocGrows_write hm hd hh hv hw hwr
    exact ⟨⟨rfl, hs.mono hg, heapClosed_write hm hd hh hv hw hwr hsw hc⟩, hg, trivial⟩
  · rintro s x obj ty md v t mty σ' - - - hu ⟨rfl, hs, hc⟩
    exact ⟨⟨rfl, hs.updateState hu (safeRef_ofBool _), hc⟩, AllocGrows.refl, trivial⟩
  · rintro s e md v - hv ⟨rfl, hs, hc⟩
    exact ⟨⟨rfl, hs, hc⟩, AllocGrows.refl, hv⟩
  · exact fun _ ih => ih
  · exact fun _ _ _ ih => ih
  · rintro s lhs n args md p σ₀ evs sE outs σL σ' - - hσ₀ - - hrd - hup hgb ih ⟨rfl, hs, hc⟩
    obtain ⟨⟨-, hsE, hcE⟩, hg⟩ := ih ⟨rfl, hσ₀, hc⟩
    exact ⟨⟨rfl, ((hs.mono hg).updateStates hup (hsE.readValues hrd)).globalsBack hsE hgb, hcE⟩,
      hg, trivial⟩
  · rintro s lhs n args md p σ₀ evs sE v σG vals σ' - - hσ₀ - - hgb hrd - hup ih ⟨rfl, hs, hc⟩
    obtain ⟨⟨-, hsE, hcE⟩, hv, hg⟩ := ih ⟨rfl, hσ₀, hc⟩
    exact ⟨⟨rfl, ((hs.mono hg).globalsBack hsE hgb).updateStates hup (hsE.readValues hrd), hcE⟩,
      hg, hv⟩
  · rintro p b s₀ evs sE - - ih hs
    obtain ⟨hsE, hg⟩ := ih hs
    exact ⟨hsE, hg.1 _ rfl _ rfl⟩
  · rintro p b s₀ evs sE v - - ih hs
    obtain ⟨⟨hsE, hv⟩, hg⟩ := ih hs
    exact ⟨hsE, hv, hg.1 _ rfl _ rfl⟩
  · exact fun _ hc => ⟨hc, .refl⟩
  · intro _ _ _ _ _ _ _ ih ih' hc
    obtain ⟨hc₁, g⟩ := ih hc
    obtain ⟨hc', g'⟩ := ih' hc₁
    exact ⟨hc', g.trans g'⟩
  · exact fun _ hs => ⟨hs, .of .refl rfl rfl⟩
  · intro _ _ _ _ _ _ _ _ _ ih hs
    obtain ⟨hs', hg, -⟩ := ih hs
    exact ⟨hs', .of hg rfl rfl⟩
  · intro _ _ _ _ _ _ _ _ _ _ h _ _ _ ih hs
    obtain ⟨⟨hf, hs', hc'⟩, hg, hv⟩ := ih hs
    exact ⟨⟨hf, hs'.update hv, hc'⟩, .of hg rfl rfl⟩
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih hs
    obtain ⟨hs', hg, hv⟩ := ih hs
    exact ⟨⟨hs', hv⟩, .of hg rfl rfl⟩
  · intro _ _ _ _ _ _ _ _ _ _ _ _ _ _ ih hs
    obtain ⟨hs', hg, -⟩ := ih hs
    exact ⟨hs', .of hg rfl rfl⟩
  · exact fun _ hs => ⟨hs, .of .refl rfl rfl⟩
  · exact fun _ hs => ⟨hs, .of .refl rfl rfl⟩
  · exact fun hs => ⟨hs, .of .refl rfl rfl⟩
  · exact fun _ => ⟨trivial, fun _ _ _ h => (nomatch h), fun h => (nomatch h)⟩

/-- **Every reference is `Null` or allocated.** In every configuration that a Cortex run
reaches from an initial environment satisfying `CortexInitEnvWF` in which it starts with safe
references (`SafeStart`), the state has the run's factory, its store holds only references
that are `Null` or allocated in its heap (`StoreSafe`), its heap is closed (`HeapClosed`), and
the exception of a `raised` configuration is such a reference. -/
theorem cortex_reachable_safe {prog : Program} {params : Core.Logic.InitEnvWFParams}
    {st : Frame} {ρ : Imperative.Env Core.Expression}
    (hwf : CortexInitEnvWF prog.ctx params st ρ) (hs : SafeStart prog st ρ)
    {τ : List CEvent} {c : CConfig}
    (h : (EventLang.cortex prog).traceStar ((EventLang.cortex prog).stmtCfg st ρ) τ c) :
    c.Safe prog.ctx ρ.factory := by
  refine (trace_safe hwf.heapApi h ⟨rfl, fun x v hx => ?_, hs.heapClosed⟩).1
  by_cases hxe : x = entryHeapVar
  · subst hxe
    have hv : entryHeap ρ.factory ρ.store = v := by
      simp only [entryHeap, show ρ.store entryHeapVar = some v from hx, Option.getD_some]
    exact safeRef_of_isOfTy (hv ▸ (entryHeap_spec hwf).1) (by decide)
  · exact hs.storeSafe x v hxe hx

end Invariant

end -- public section

end Cortex.Sem
