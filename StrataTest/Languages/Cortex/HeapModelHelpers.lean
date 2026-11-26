/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.Languages.Cortex.LangDef
import Strata.Languages.Core.InstWellFormedSemanticsEval
import Strata.DL.Lambda.LExprDenoteEvalProps
public import Strata.DL.Lambda.Denote.LExprDenote
import all Strata.DL.Lambda.Denote.LExprDenote
import all Strata.DL.Lambda.Denote.LExprDenoteCompute
import all Strata.DL.Lambda.LExprDenoteEval
import all Strata.DL.Lambda.IntBoolFactory
import all Strata.DL.Lambda.Factory
import all Strata.Languages.Cortex.Semantics
import all Strata.Languages.Cortex.Module

/-! # Factories with a model of references and of the heap API, for tests

A test that builds a model of `RefTagModel` and `HeapApiModel` gives the carriers of its
sorts and the interpretation of its operators. This file builds from them the factory of
Core's negation and of uninterpreted functions with the API's names (`fac`), and the lemmas
that evaluate an API term under it (`apiEval_of_Denotes`, `ofTy` and the `api_eval` tactic).

## Key definitions and results

- `funcs`, `fns`, `model`, `fac`: the factory and its model.
- `name_mem`: the factory declares the functions it is built from.
- `apiEval_of_Denotes`, `api_eval`: an API term evaluates to the value a derivation of its
  annotated form gives it.
- `ofTy`: a value of a type is an element of the type's carrier.
-/

namespace Cortex.Sem.HeapModel

open Imperative Lambda

/-! ## The factory -/

/-- A function without a body, an evaluator or axioms: the model alone interprets it. -/
noncomputable def uninterp (n : String) : LFunc Core.CoreLParams :=
  LFunc.mk ⟨n, ()⟩ (inputs := []) (output := .bool)

/-- The functions of the factory: Core's negation and the functions named `names`. -/
noncomputable def funcs (names : List String) : Array (LFunc Core.CoreLParams) :=
  #[(boolNotFunc (T := Core.CoreLParams)).func] ++ (names.map uninterp).toArray

/-- The factory of `funcs names`. -/
noncomputable def fns (names : List String) : Factory Core.CoreLParams :=
  Factory.ofArray (funcs names)

variable {names : List String}

/-- A function of the factory is one of `funcs`. -/
theorem mem_funcs {g : LFunc Core.CoreLParams} (h : g ∈ (fns names).toArray) :
    g ∈ funcs names :=
  Factory.ofArray_mem h

/-- Every function of `funcs` is found in the factory under its name, when the names are
distinct. -/
theorem get_funcs (hnd : ((funcs names).toList.map (·.name.name)).Nodup)
    {g : LFunc Core.CoreLParams} (h : g ∈ funcs names) : (fns names)[g.name.name]? = some g :=
  Factory.get?_ofArray_of_mem h hnd

/-- The function a member name of the factory looks up is one of `funcs`. -/
theorem getElem_funcs {n : String} (hn : n ∈ fns names) : (fns names)[n] ∈ funcs names := by
  obtain ⟨g, hg⟩ :=
    Option.isSome_iff_exists.mp ((Factory.mem_iff_getElem?_isSome (fns names) n).mp hn)
  rw [Factory.getElem?_some_getElem hg]
  exact mem_funcs (Factory.getElem?_is_some_implies_mem hg)

/-- No function of `funcs` is a constructor, has a body or has an axiom, and only negation
has an evaluator. -/
theorem funcs_shape {g : LFunc Core.CoreLParams} (h : g ∈ funcs names) :
    g.isConstr = false ∧ g.body = none ∧ g.axioms = [] ∧
      (g.concreteEval.isSome → g = (boolNotFunc (T := Core.CoreLParams)).func) := by
  rcases Array.mem_append.mp h with h | h
  · obtain rfl : g = _ := List.mem_singleton.mp (Array.mem_def.mp h)
    exact ⟨rfl, rfl, rfl, fun _ => rfl⟩
  · obtain ⟨n, -, rfl⟩ := List.mem_map.mp (List.mem_toArray.mp h)
    exact ⟨rfl, rfl, rfl, nofun⟩

/-- The factory declares negation and the functions named `names`. -/
theorem name_mem (hnd : ((funcs names).toList.map (·.name.name)).Nodup) {n : String}
    (h : n ∈ "Bool.Not" :: names) : n ∈ fns names := by
  rcases List.mem_cons.mp h with rfl | h
  · exact Factory.getElem?_some_implies_mem
      (get_funcs hnd (g := (boolNotFunc (T := Core.CoreLParams)).func) (by simp [funcs]))
  · exact Factory.getElem?_some_implies_mem (get_funcs hnd (g := uninterp n)
      (Array.mem_append_right _ (List.mem_toArray.mpr (List.mem_map_of_mem h))))

/-! ## The interpretation -/

variable {carrier : String → List LSort → Type} [TyConstrInterp.AllInhabited carrier]
  {opI : OpInterp carrier}

omit [TyConstrInterp.AllInhabited carrier] in
/-- A model whose negation is Boolean negation interprets negation as its evaluator
computes it. -/
theorem boolNot_consistent
    (hnot : opI "Bool.Not" (.tcons "arrow" [.tcons "bool" [], .tcons "bool" []]) =
      fun (b : Bool) => !b)
    {ceval : ConcreteEval Core.CoreLParams}
    (hce : (boolNotFunc (T := Core.CoreLParams)).func.concreteEval = some ceval) :
    LFunc.InterpConsistentEval carrier opI (boolNotFunc (T := Core.CoreLParams)).func ceval := by
  intro vt fv md tySubst args res
  simp only []
  intro heval h_args h_result
  simp only [boolNotFunc, unaryOp, Option.some.injEq] at hce
  subst hce
  have hb : LMonoTy.subst tySubst (.bool : LMonoTy) = .bool :=
    LMonoTy.subst_ground _ _ rfl
  have hIT : List.map (LMonoTy.subst tySubst)
      (List.map Prod.snd (boolNotFunc (T := Core.CoreLParams)).func.inputs) = [.bool] :=
    congrArg ([·]) hb
  have hOT : LMonoTy.subst tySubst (boolNotFunc (T := Core.CoreLParams)).func.output = .bool := hb
  revert h_args h_result
  rw [hIT, hOT]
  intro h_args h_result
  rcases args with _ | ⟨x, _ | ⟨_, _⟩⟩ <;> simp only [reduceCtorEq] at heval
  cases x <;> simp only [LambdaLeanType.cevalTy, LExpr.denoteBool, reduceCtorEq] at heval
  rename_i c
  cases c <;> simp only [reduceCtorEq] at heval
  simp only [ite_true, Option.some.injEq] at heval
  subst heval
  change _ = (opI "Bool.Not" (.tcons "arrow" [.tcons "bool" [], .tcons "bool" []]) : Bool → Bool) _
  rw [hnot]
  rfl

variable (names carrier opI) in
/-- The model of the factory whose carriers are `carrier` and whose operators are `opI`. -/
noncomputable def model
    (hnot : opI "Bool.Not" (.tcons "arrow" [.tcons "bool" [], .tcons "bool" []]) =
      fun (b : Bool) => !b) :
    Lambda.Interp (fns names) where
  tcInterp := carrier
  opInterp := opI
  allInhabited := inferInstance
  interpConsistent := by
    refine ⟨fun f hf body hb => ?_, fun f hf ceval hc => ?_⟩
    · rw [(funcs_shape (getElem_funcs hf)).2.1] at hb
      cases hb
    · have hg := (funcs_shape (getElem_funcs hf)).2.2.2 (by rw [hc]; rfl)
      rw [hg] at hc ⊢
      exact boolNot_consistent hnot hc
  axiomsSatisfied f hf ax hax := by
    rw [(funcs_shape (getElem_funcs hf)).2.2.1] at hax
    cases hax
  constrConsistent :=
    ⟨fun f1 _ h1 _ c1 => by simp [(funcs_shape (mem_funcs h1)).1] at c1,
     fun f h c => by simp [(funcs_shape (mem_funcs h)).1] at c,
     fun _ _ _ _ ⟨f, hf, c, _⟩ => by simp [(funcs_shape (mem_funcs hf)).1] at c⟩

variable (names carrier opI) in
/-- The modeled factory, with every type variable read as `bool`. -/
noncomputable def fac
    (hnot : opI "Bool.Not" (.tcons "arrow" [.tcons "bool" [], .tcons "bool" []]) =
      fun (b : Bool) => !b) : Core.Expression.Factory :=
  ⟨fns names, model names carrier opI hnot, fun _ => .bool⟩

/-! ## Evaluating API terms -/

/-- A key of an association list looks up a value of the list. -/
theorem lookup_of_mem {bs : List (String × SemValue)} {k : String}
    (h : k ∈ bs.map Prod.fst) : ∃ v, bs.lookup k = some v ∧ (k, v) ∈ bs := by
  induction bs with
  | nil => cases h
  | cons p bs ih =>
    rcases p with ⟨k', v'⟩
    by_cases hk : k = k'
    · subst hk
      exact ⟨v', by simp [List.lookup], by simp⟩
    · obtain ⟨v, hv, hm⟩ := ih (by simpa [hk] using h)
      exact ⟨v, by simp [List.lookup, beq_false_of_ne hk, hv], List.mem_cons_of_mem _ hm⟩

omit [TyConstrInterp.AllInhabited carrier] in
/-- A store binding values of the model defines every term whose variables it binds. -/
theorem defines_of {bs : List (String × SemValue)} {e : Expr}
    (hb : ∀ p ∈ bs, p.2.tc = carrier)
    (hv : ∀ x ∈ LExpr.LExpr.getVars e, x.name ∈ bs.map Prod.fst) :
    ValStore.Defines (T := Core.CoreLParams) (bindStore bs) carrier e := fun x hx =>
  have ⟨v, hl, hm⟩ := lookup_of_mem (hv x hx)
  ⟨v, hl, hb _ hm⟩

variable {hnot : opI "Bool.Not" (.tcons "arrow" [.tcons "bool" [], .tcons "bool" []]) =
  fun (b : Bool) => !b}

/-- An API term evaluates, at a ground type `τ`, to the value a derivation of its annotated
form gives it. -/
theorem apiEval_of_Denotes {bs : List (String × SemValue)} {e : Expr} {τ : LMonoTy}
    {v : SortDenote carrier (τ.substTyVars fun _ => .bool)}
    (hd : ValStore.Defines (T := Core.CoreLParams) (bindStore bs) carrier e)
    (h : (e.annotateFvars (ValStore.ann (T := Core.CoreLParams) (bindStore bs))).HasTypeA [] τ)
    (hg : τ.IsGround)
    (hw : Denotes carrier opI (ValStore.fvarVal (T := Core.CoreLParams) carrier (bindStore bs))
      (fun _ => .bool) .nil _ τ h v) :
    apiEval (fac names carrier opI hnot) bs e =
      some ⟨carrier, τ.substTyVars fun _ => .bool, v⟩ :=
  (LExpr.denoteEval_eq_mk_iff (M := fac names carrier opI hnot) hg).mpr
    ⟨hd, h, denote_eq_of_Denotes hw rfl⟩

/-- A value of type `t` in the model is an element of `t`'s carrier. -/
theorem ofTy {v : SemValue} {t : LMonoTy} (h : IsOfTy (fac names carrier opI hnot) v t) :
    ∃ x : SortDenote carrier (t.substTyVars fun _ => .bool), v = ⟨carrier, _, x⟩ := by
  obtain ⟨tc, s, x⟩ := v
  obtain ⟨htc, hs⟩ := h
  obtain rfl : tc = carrier := htc
  obtain rfl : t = s.toMonoTy := by simpa [LTy.toMonoType?] using hs
  rw [LSort.toMonoTy_substTyVars]
  exact ⟨x, rfl⟩

/-- A variable bound to a value of the model reads that value. -/
theorem fvarVal_bind {bs : List (String × SemValue)} {n : String} {s : LSort}
    {x : SortDenote carrier s} (h : bs.lookup n = some ⟨carrier, s, x⟩) :
    ValStore.fvarVal (T := Core.CoreLParams) carrier (bindStore bs) ⟨n, ()⟩ s = x := by
  simp only [ValStore.fvarVal, bindStore, h, Option.bind_some]
  exact congrArg (Option.getD · default) (SemValue.read_self ⟨carrier, s, x⟩)

/-- A variable of an API term denotes the value its store binds it to. -/
theorem Denotes.fvar_bind {bs : List (String × SemValue)} {n : String} {ty : LMonoTy}
    {s : LSort} {x : SortDenote carrier s} {m : Core.ExpressionMetadata}
    {h : LExpr.HasTypeA [] (.fvar m ⟨n, ()⟩ (some ty) : Expr) ty}
    (hl : bs.lookup n = some ⟨carrier, s, x⟩) (hs : s = ty.substTyVars fun _ => .bool) :
    Denotes carrier opI (ValStore.fvarVal (T := Core.CoreLParams) carrier (bindStore bs))
      (fun _ => .bool) .nil (.fvar m ⟨n, ()⟩ (some ty)) ty h
      (cast (congrArg (SortDenote carrier) hs) x) := by
  subst hs
  have hd := Denotes.fvar_ann (opInterp := opI) (bvarVal := .nil) (h := h)
    (fvarVal := ValStore.fvarVal (T := Core.CoreLParams) carrier (bindStore bs))
    (vt := fun _ => .bool) (m := m) (x := ⟨n, ()⟩)
  rwa [fvarVal_bind hl] at hd

/-- Evaluate an API term by a derivation of its value, leaving the value's equation. -/
macro "api_eval" : tactic => `(tactic| (
  apply (apiEval_of_Denotes ?hd (LExpr.typeCheck_to_HasTypeA rfl) rfl ?hw).trans
  case hd =>
    refine defines_of ?_ (by simp only [List.map_cons, List.map_nil]; decide)
    simp only [List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
    try and_intros
    all_goals rfl
  case hw =>
    dsimp (config := {decide := true}) only [isObjT, objT, tagOfT, nullRef, locsNoneT, readT,
      writeT, allocatedT, growsT, onlyModifiesT, locsMemT, locsAtT, locsObjectT, fieldIdT,
      fieldConst, tagConst, apiVar, apiCall, mkApp, mkFvar, List.foldl, List.foldr,
      LExpr.annotateFvars, ValStore.ann, bindStore, List.lookup, Option.map]
    repeat (any_goals (first | exact LExpr.typeCheck_to_HasTypeA rfl |
      exact Denotes.fvar_bind rfl rfl | denotes_step))))

omit [TyConstrInterp.AllInhabited carrier] in
/-- A Boolean value of the model is determined by its Boolean. -/
theorem some_bool {b c : Bool} (h : b = c) :
    (some ⟨carrier, .bool, b⟩ : Option SemValue) = some ⟨carrier, .bool, c⟩ := h ▸ rfl

omit [TyConstrInterp.AllInhabited carrier] in
/-- Two Boolean values of the model that are equal have equal Booleans. -/
theorem bool_inj {b c : Bool}
    (h : (some ⟨carrier, .bool, b⟩ : Option SemValue) = some ⟨carrier, .bool, c⟩) : b = c := by
  cases h; rfl

/-- A Boolean value of the model holds exactly when its Boolean is `true`. -/
theorem holds_iff {b : Bool} :
    (some ⟨carrier, .bool, b⟩ : Option SemValue) =
        some (HasBool.ttVal (P := Core.Expression) (fac names carrier opI hnot))
      ↔ b = true :=
  ⟨bool_inj, fun h => h ▸ rfl⟩

end Cortex.Sem.HeapModel
