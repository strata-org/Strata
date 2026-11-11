/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Lambda.Factory
import all Strata.DL.Lambda.LExprType
public import Strata.Util.ListUtils
public import Strata.DL.Lambda.TypeFactory
import Strata.Util.ListUtilsProps

/-!
## Properties of `Lambda.Factory`

Theorems about `Factory`, `Factory.callOfLFunc`, `getLFuncCall`, and related
definitions.

### `callOfLFunc` / `getLFuncCall`
These characterize what a successful call decomposition tells you: `callOfLFunc`
yields an `.op` callee that resolves to a factory function of matching arity
(`callOfLFunc_eq_some`, `callOfLFunc_arity`, `callOfLFunc_getElem?`), whose
callee/args coincide with `getLFuncCall`'s decomposition (`callOfLFunc_getLFuncCall`)
and whose function is a member of the factory (`callOfLFunc_func_mem`). A set of size lemmas
(`getLFuncCall.go_size`, `getLFuncCall_smaller`, `callOfLFunc_smaller`) shows extracted
arguments are structurally smaller than the original expression, which is used for termination.

### Factory membership / lookup (`namespace Factory`)
These relate the three views of a factory — its name set, its backing array, and
`get?`/`get` lookups. Names are unique (`name_nodup`), the default factory is empty
(`toArray_default`, `default_mem_is_false`), and `push`/`pushIfNew` update membership
and lookups predictably (`push_mem_iff`, `push_mem_match`, `mem_iff_mem_names`). A
family of `getElem?_*`/`mem_name_eq_getElem` lemmas connects a successful lookup to
array membership and names, and the `ofArray`/`get?_foldl_pushIfNew_*` lemmas lift
these facts to factories built from arrays.

### Factories related function by function
Two factories whose functions are related one by one (`List.Rel₂` on their arrays), by a
relation that keeps names, hold the same names (`mem_of_forall₂`) and find related functions
(`getElem?_of_forall₂`); `pushIfNew` keeps them related (`forall₂_pushIfNew`,
`forall₂_foldl_pushIfNew`).

### Factories that differ only in function attributes, and lookups as list searches
`IsMapOf F G g` says `G` holds the images under `g` of `F`'s functions under the same names, and
`AttrOnly g` says `g` changes only attributes. Maps compose (`IsMapOf.trans`) and arise from
`ofArray` of a mapped array (`isMapOf_ofArray_map`). Lookups are list searches
(`getElem?_eq_find?`), and the lemmas `getElem?_pushIfNew`, `getElem?_foldl_pushIfNew`,
`getElem?_ofArray`, `getElem?_addFactory` and `getElem?_ofArray_map` compute lookups in built
factories. The semantic conditions that carry along such maps are in `LExprEvalDenoteEval`.

### `LFunc` conversions and type substitution
These are the algebraic facts about `LFunc` plumbing. Erasing metadata keeps an operator's
type annotation, which concrete evaluators receive (`LExpr.opTy?_eraseMetadata`). The
`LFuncDefined ↔ LFunc` conversions are mutually inverse (`LFuncDefined.toLFunc_toFunc`,
`LFunc.toFunc_toLFunc`). The remaining lemmas unfold type-substitution helpers:
`applyTypeSubst` reduces to `replaceUserProvidedType`
(`LExpr.applyTypeSubst_eq_replaceUserProvidedType`) and `computeTypeSubst` agrees with
`opTypeSubst` whenever the latter succeeds (`LFunc.computeTypeSubst_of_opTypeSubst`).

### Lookups across `Factory.push`
`Factory.push` only accepts a function whose name is absent from the factory
(`Factory.tryPush` rejects a redefinition), so a push cannot disturb any
existing binding: every `F[_]?` hit and every resolved `Factory.callOfLFunc`
survives a push unchanged (`Factory.push_getElem?_of_mem`, `callOfLFunc_push`).
The binding predicate `Factory.BindsTo` is preserved by a successful
`Factory.tryPush` (`Factory.BindsTo.tryPush`).
-/

namespace Lambda

theorem callOfLFunc_eq_some {GenericTy} {F : Factory T}
    {e callee : LExpr ⟨T, GenericTy⟩} {args : List (LExpr ⟨T, GenericTy⟩)} {fn : LFunc T}
    (hcall : Factory.callOfLFunc F e = some (callee, args, fn))
    : ∃ m name ty, callee = .op m name ty ∧
      F[name.name]? = some fn ∧ args.length = fn.inputs.length := by
  simp only [Factory.callOfLFunc, Bool.false_eq_true, ↓reduceIte] at hcall
  split at hcall <;> simp_all only [exists_and_right, reduceCtorEq]
  split at hcall <;> try contradiction
  split at hcall <;> try contradiction
  cases hcall
  grind

theorem callOfLFunc_getLFuncCall {GenericTy} {F : Factory T}
    {e callee : LExpr ⟨T, GenericTy⟩} {args : List (LExpr ⟨T, GenericTy⟩)} {fn : LFunc T}
    {aPA : Bool}
    (hcall : Factory.callOfLFunc F e (allowPartialApp := aPA) = some (callee, args, fn))
    : getLFuncCall e = (callee, args) := by
  simp only [Factory.callOfLFunc] at hcall
  split at hcall <;> simp_all only [reduceCtorEq]
  split at hcall <;> try contradiction
  cases aPA <;> simp only [Bool.false_eq_true, ↓reduceIte] at hcall <;> split at hcall <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hcall
  all_goals (obtain ⟨rfl, rfl, rfl⟩ := hcall; exact Prod.ext ‹_› rfl)

theorem getLFuncCall.go_size {T: LExprParamsT} {e: LExpr T} {op args acc} : getLFuncCall.go e acc = (op, args) →
op.sizeOf + List.sum (args.map LExpr.sizeOf) <= e.sizeOf + List.sum (acc.map LExpr.sizeOf) := by
  fun_induction go generalizing op args
  case case1 acc e' arg1 arg2 IH =>
    intros Hgo; specialize (IH Hgo); simp_all; omega
  case case2 acc fn fnty arg1 =>
    simp_all only [List.cons_append, List.nil_append, Prod.mk.injEq, LExpr.sizeOf, Nat.reduceAdd, and_imp]; intros op_eq args_eq; subst op args; simp; omega
  case case3 op' args' _ _ => intros Hop; cases Hop; omega

theorem getLFuncCall_smaller {T} {e: LExpr T} {op args} : getLFuncCall e = (op, args) → (forall a, a ∈ args → a.sizeOf < e.sizeOf) := by
  unfold getLFuncCall
  intros Hgo
  have Hsize := (getLFuncCall.go_size Hgo)
  simp_all only [List.map_nil, List.sum_nil, Nat.add_zero]
  -- `LExpr.sizeOf_pos` lives in `LExprProps`, which imports this module; inline
  -- the positivity fact here to avoid an import cycle.
  have Hop : 0 < op.sizeOf := by cases op <;> simp only [LExpr.sizeOf] <;> omega
  intros a a_in
  have Ha := List.sum_size_le LExpr.sizeOf a_in
  omega

theorem Factory.callOfLFunc_smaller {T} {F : Factory T.base} {e : LExpr T} {op args F'}
    {allowPartialMatch}
    : Factory.callOfLFunc F e (allowPartialApp := allowPartialMatch) = some (op, args, F') →
  (forall a, a ∈ args → a.sizeOf < e.sizeOf) := by
  simp only [callOfLFunc]; cases Hfunc: (getLFuncCall e) with | mk op args;
  simp only; cases op <;> simp only [reduceCtorEq, false_implies]
  rename_i o ty; cases F[o.name]? <;> simp only [reduceCtorEq, false_implies]
  rename_i F'
  cases allowPartialMatch
  · cases (args.length == List.length F'.inputs) <;> simp only [Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq, and_imp, reduceCtorEq, false_implies]; intros op_eq args_eq F_eq
    subst op args F'; exact (getLFuncCall_smaller Hfunc)
  · cases (Nat.ble args.length (List.length F'.inputs)) <;> simp only [↓reduceIte, Option.some.injEq, Prod.mk.injEq, and_imp, reduceCtorEq, false_implies]
    intros op_eq args_eq F_eq
    subst op args F'; exact (getLFuncCall_smaller Hfunc)

/-- If `F[s]?` finds a function, its name matches the query. -/
theorem Factory.getElem?_name {T} {F : Factory T} {s : String} {fn : LFunc T}
    (h : F[s]? = some fn) : fn.name.name = s := by
  simp +instances [instGetElem?, Factory.get?] at h
  split at h
  · contradiction
  · rename_i idx h_idx; simp at h
    have h_mem : s ∈ F.nameMap := by grind
    have h_idx_val : F.nameMap[s] = idx :=
      (Std.HashMap.getElem?_eq_some_iff.mp h_idx).2
    have h_cons := F.nameMapConsistent h_mem
    grind

/-- `callOfLFunc` ensures the number of args equals the number of inputs. -/
theorem Factory.callOfLFunc_arity {T} {F : Factory T} {e callee : LExpr T.mono}
    {args : List (LExpr T.mono)} {fn : LFunc T}
    (hcall : Factory.callOfLFunc F e = some (callee, args, fn))
    : args.length = fn.inputs.length := by
  simp only [callOfLFunc, Bool.false_eq_true, ↓reduceIte] at hcall
  split at hcall <;> simp_all only [reduceCtorEq]
  split at hcall <;> try contradiction
  split at hcall <;> try contradiction
  cases hcall
  grind

/-- The callee of `callOfLFunc` is an `.op` whose name resolves to `fn` via `F[_]?`. -/
theorem Factory.callOfLFunc_getElem?
    {T} {F : Factory T} {e callee : LExpr T.mono}
    {args : List (LExpr T.mono)} {fn : LFunc T}
    {aPA : Bool}
    (hcall : Factory.callOfLFunc F e (allowPartialApp := aPA) = some (callee, args, fn))
    : ∃ m name ty, callee = .op m name ty ∧ F[name.name]? = some fn := by
  simp only [callOfLFunc] at hcall
  split at hcall <;> simp_all only [exists_and_right, reduceCtorEq]
  split at hcall <;> try contradiction
  cases aPA <;> simp only [Bool.false_eq_true, ↓reduceIte] at hcall <;> split at hcall <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at hcall
  all_goals (obtain ⟨rfl, rfl, rfl⟩ := hcall; grind)

theorem LExpr.applyTypeSubst_eq_replaceUserProvidedType {T : LExprParams}
    (e : LExpr T.mono) (S : Subst) :
    e.applyTypeSubst S = replaceUserProvidedType e (LMonoTy.subst S) := by
  unfold applyTypeSubst
  split
  case isTrue h_empty =>
    have h_id : LMonoTy.subst S = id :=
      funext (fun ty => LMonoTy.subst_of_hasEmptyScopes h_empty ty)
    rw [h_id]
    induction e <;> unfold replaceUserProvidedType <;> grind
  case isFalse => rfl

/-- An unannotated free variable is fixed by `applyTypeSubst`. -/
theorem LExpr.applyTypeSubst_fvar_none {T : LExprParams} (S : Subst) (m : T.Metadata)
    (x : Identifier T.IDMeta) :
    LExpr.applyTypeSubst (LExpr.fvar m x none : LExpr T.mono) S = LExpr.fvar m x none := by
  rw [LExpr.applyTypeSubst_eq_replaceUserProvidedType]
  simp only [LExpr.replaceUserProvidedType, Option.map_none]

/-- When `opTypeSubst` succeeds, `computeTypeSubst` agrees with it. -/
theorem LFunc.computeTypeSubst_of_opTypeSubst {T : LExprParams}
    {fn : LFunc T} {callee : LExpr T.mono} {args : List (LExpr T.mono)} {s : Subst}
    (h : fn.opTypeSubst callee = some s)
    : fn.computeTypeSubst callee args = some s := by
  unfold LFunc.computeTypeSubst
  rw [h]

/-- `eraseMetadata` keeps the type annotation of an operator (`LExpr.opTy?`). -/
theorem LExpr.opTy?_eraseMetadata {T : LExprParamsT} (e : LExpr T) :
    e.eraseMetadata.opTy? = e.opTy? := by
  cases e <;> simp [LExpr.eraseMetadata, LExpr.replaceMetadata, LExpr.opTy?]

/-- Lifting an `LFuncDefined` to the full `LFunc` then projecting back recovers
    the original. -/
theorem LFuncDefined.toLFunc_toFunc {T : LExprParams} (f : LFuncDefined T)
    (ce : Option (ConcreteEval T)) :
    (f.toLFunc ce).toFunc = f := rfl

/-- Projecting an `LFunc` to its base then lifting back (restoring
    `concreteEval`) recovers the original. -/
theorem LFunc.toFunc_toLFunc {T : LExprParams} (l : LFunc T) :
    LFuncDefined.toLFunc l.toFunc l.concreteEval = l := rfl

namespace Factory

/-- Mapping a factory by a function that fixes each of its functions gives the factory. -/
theorem map_eq_self {T} (F : Factory T) (g : LFunc T → LFunc T)
    (hg : ∀ f, (g f).name.name = f.name.name) (h : ∀ f ∈ F.toArray, g f = f) :
    F.map g hg = F := by
  have harr : F.toArray.map g = F.toArray :=
    (Array.map_congr_left h).trans (Array.map_id F.toArray)
  cases F
  simp only [map, Factory.mk.injEq, and_true]
  exact harr

/-- The function names in a factory are unique. -/
theorem name_nodup {T} (f : Factory T) : List.Nodup (f.toArray |>.toList |>.map (·.name.name)) := by
  match f with
  | { toArray := ⟨l⟩, nameMap, toArrayDefined, nameMapValid, nameMapConsistent } =>
    apply List.inj_implies_nodup
    intro i j hi hj heq
    simp only [List.length_map] at hi hj
    -- toArrayDefined gives us injectivity via the nameMap
    have hdi : nameMap[l[i].name.name]? = some i := toArrayDefined ⟨i, hi⟩
    have hdj : nameMap[l[j].name.name]? = some j := toArrayDefined ⟨j, hj⟩
    grind

private theorem mem_pushIfNew {T} {f : Factory T} {g h : LFunc T}
    (p : g ∈ (f.pushIfNew h).toArray) : g ∈ f.toArray ∨ g = h := by
  revert p
  simp [pushIfNew, push]
  grind

private theorem ofArray_mem_take {T} {f : Factory T} {as : Array (LFunc T)} {fn : LFunc T}
    (p : fn ∈ (f.append as).toArray) : fn ∈ f.toArray ∨ fn ∈ (as.take as.size) := by
  simp only [append] at p
  revert p
  intro p2
  apply Array.foldl_induction (init := f) (f := pushIfNew)
    (motive := fun i m => fn ∈ m.toArray → fn ∈ f.toArray ∨ fn ∈ as.take i)
  case h0 =>
    grind
  case hf =>
    intro ⟨i, ilt⟩ f2 p p2
    simp_all only [Array.mem_extract_iff_getElem]
    match mem_pushIfNew p2 with
    | Or.inl q =>
      grind
    | Or.inr q =>
      grind
  case a =>
    exact p2

theorem ofArray_mem {T} {a : Array (LFunc T)} {fn : LFunc T}
    (p : fn ∈ (Factory.ofArray a).toArray) : fn ∈ a := by
  have q := ofArray_mem_take p
  simp only [Factory.default, List.mem_toArray, List.not_mem_nil, Array.drop_eq_extract, Array.extract_size,
    false_or] at q
  exact q

@[simp] theorem toArray_default {T} : (Factory.default (T := T)).toArray = #[] := by
  unfold Factory.default; rfl

@[simp]
theorem default_mem_is_false (T) (name : String) : name ∈ Factory.default (T := T) ↔ False := by
  simp +instances[Factory.default, Factory.instMem, Factory.mem]

theorem push_mem_iff {T} (f : Factory T) (fn : LFunc T) (h : fn.name.name ∉ f) (name : String) :
    name ∈ f.push fn h ↔ name = fn.name.name ∨ name ∈ f := by
  simp +instances only [instMem, Factory.mem, push]
  simp only [Std.HashMap.mem_insert]
  constructor <;> intro hm <;> grind

theorem mem_iff_mem_names {T} (f : Factory T) (s : String) :
    s ∈ f ↔ s ∈ f.toArray.map (·.name.name) := by
  constructor
  · intro hs
    have hvalid := f.nameMapValid hs
    have hcons := f.nameMapConsistent hs
    rw [Array.mem_iff_getElem]
    exact ⟨f.nameMap[s], by simp only [Array.size_map] ; exact hvalid, by simp only [Array.getElem_map] ; exact hcons⟩
  · intro hs
    rw [Array.mem_iff_getElem] at hs
    obtain ⟨i, hi, hname⟩ := hs
    simp only [Array.size_map] at hi
    simp only [Array.getElem_map] at hname
    have := f.toArrayDefined ⟨i, hi⟩
    simp +instances only [instMem, Factory.mem]
    rw [← hname]
    grind

theorem push_mem_match {T} (f : Factory T) (fn : LFunc T) (h : fn.name.name ∉ f) (name : String) :
  (f.push fn h)[name]? = if name = fn.name.name then some fn else f[name]? := by
  simp +instances [push, instGetElem?, Factory.get?]
  grind

theorem getElem?_is_some_implies_mem {T} {f : Factory T} {name : String} {fn : LFunc T}
 (eq : f[name]? = some fn) : fn ∈ f.toArray := by
  change Factory.get? f name = some fn at eq
  unfold Factory.get? at eq
  split at eq
  · contradiction
  · rename_i idx h_idx
    injection eq with h_eq
    subst h_eq
    have idx_lt : idx < f.toArray.size := by
      simp only [Std.HashMap.getElem?_eq_some_iff] at h_idx
      obtain ⟨h_mem, h_val⟩ := h_idx
      rw [←h_val]
      exact f.nameMapValid h_mem
    exact Array.mem_def.mpr (Array.getElem_mem_toList idx_lt)

theorem getElem?_some_implies_mem {T} {f : Factory T} {name : String} {fn : LFunc T}
    (eq : f[name]? = some fn) : name ∈ f := by
  simp +instances [instGetElem?, Factory.get?, instMem, Factory.mem] at eq ⊢
  grind

theorem getElem?_some_getElem {T} {f : Factory T} {name : String} {fn : LFunc T}
    (eq : f[name]? = some fn) : f[name]'(getElem?_some_implies_mem eq) = fn := by
  simp +instances only [instGetElem?, get?, Lean.Elab.WF.paramLet, get] at eq ⊢
  split at eq
  · contradiction
  · rename_i idx h_idx; simp at eq; grind

/-- If `fn ∈ F.toArray` and `fn.name.name = s`, then `s ∈ F` and `F[s] = fn`. -/
theorem mem_name_eq_getElem {T} {F : Factory T} {fn : LFunc T} {s : String}
    (hmem : fn ∈ F.toArray) (hname : fn.name.name = s) :
    ∃ (hs : s ∈ F), F[s]'hs = fn := by
  rw [Array.mem_def] at hmem
  rw [List.mem_iff_getElem] at hmem
  obtain ⟨i, hi, hval⟩ := hmem
  have hi' : i < F.toArray.size := by grind
  have hval' : F.toArray[i]'hi' = fn := by simpa using hval
  have hdef : F.nameMap[s]? = some i := by
    have hdef := F.toArrayDefined ⟨i, hi'⟩
    simp at hdef
    grind
  have hs : s ∈ F := by
    simp +instances only [instMem, Factory.mem]
    grind
  refine ⟨hs, ?_⟩
  simp +instances only [instGetElem?, Factory.get]
  have hidx : F.nameMap[s] = i := (Std.HashMap.getElem?_eq_some_iff.mp hdef).2
  grind

/-- Pushing a *differently*-named function via `pushIfNew` preserves an
    already-present binding. -/
theorem get?_pushIfNew_stable {T} (F : Factory T) (g fn : LFunc T)
    (hpres : F[fn.name.name]? = some fn) (hne : g.name.name ≠ fn.name.name) :
    (F.pushIfNew g)[fn.name.name]? = some fn := by
  unfold Factory.pushIfNew
  split
  · exact hpres
  · rename_i hnew
    rw [push_mem_match, ite_eq_right (fun h => hne h.symm)]
    exact hpres

/-- Folding `pushIfNew` over functions whose names all differ from `fn`'s name
    preserves an already-present binding for `fn`. -/
theorem get?_foldl_pushIfNew_stable {T} (fn : LFunc T) :
    ∀ (l : List (LFunc T)) (F : Factory T),
      F[fn.name.name]? = some fn →
      fn.name.name ∉ l.map (·.name.name) →
      (l.foldl Factory.pushIfNew F)[fn.name.name]? = some fn := by
  intro l
  induction l with
  | nil => intro F hpres _; simpa using hpres
  | cons g rest ih =>
    intro F hpres hnotin
    simp only [List.map_cons, List.mem_cons, not_or] at hnotin
    rw [List.foldl_cons]
    exact ih (F.pushIfNew g)
      (get?_pushIfNew_stable F g fn hpres (fun h => hnotin.1 h.symm)) hnotin.2

/-- If `fn` occurs in a list of functions with pairwise-distinct names, folding
    `pushIfNew` from an `fn`-free factory yields a binding for `fn`. -/
theorem get?_foldl_pushIfNew_of_mem {T} (fn : LFunc T) :
    ∀ (l : List (LFunc T)) (F : Factory T),
      fn ∈ l →
      fn.name.name ∉ F →
      List.Nodup (l.map (·.name.name)) →
      (l.foldl Factory.pushIfNew F)[fn.name.name]? = some fn := by
  intro l
  induction l with
  | nil => intro F hmem _ _; simp at hmem
  | cons g rest ih =>
    intro F hmem hnew hnodup
    simp only [List.map_cons, List.nodup_cons] at hnodup
    obtain ⟨hg_notin, hrest_nodup⟩ := hnodup
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hmem with heq | hmem_rest
    · rw [heq]
      have hnew_g : g.name.name ∉ F := by rw [← heq]; exact hnew
      have hpush : F.pushIfNew g = F.push g hnew_g := by
        unfold Factory.pushIfNew; rw [dite_eq_right hnew_g]
      have hpres : (F.pushIfNew g)[g.name.name]? = some g := by
        rw [hpush, push_mem_match, ite_eq_left rfl]
      exact get?_foldl_pushIfNew_stable g rest (F.pushIfNew g) hpres hg_notin
    · have hne : fn.name.name ≠ g.name.name := by
        intro h
        apply hg_notin
        rw [← h]
        exact List.mem_map.mpr ⟨fn, hmem_rest, rfl⟩
      have hnew' : fn.name.name ∉ F.pushIfNew g := by
        unfold Factory.pushIfNew
        split
        · exact hnew
        · rename_i hgnew
          rw [push_mem_iff F g hgnew]
          simp only [not_or]
          exact ⟨hne, hnew⟩
      exact ih (F.pushIfNew g) hmem_rest hnew' hrest_nodup

/-- Characterization of `get?` for `ofArray`-built factories: any member of the
    source array (whose names are pairwise-distinct) is found under its name. -/
theorem get?_ofArray_of_mem {T} {a : Array (LFunc T)} {fn : LFunc T}
    (hmem : fn ∈ a)
    (hnodup : List.Nodup (a.toList.map (·.name.name))) :
    (Factory.ofArray a)[fn.name.name]? = some fn := by
  unfold Factory.ofArray Factory.append
  rw [← Array.foldl_toList]
  exact get?_foldl_pushIfNew_of_mem fn a.toList Factory.default
    (by simpa using hmem) (Factory.default_empty fn.name.name) hnodup

/-- Looking up a stored function's name returns that function. -/
theorem getElem?_of_mem_toArray {T : LExprParams} (F : Lambda.Factory T) (fn : LFunc T)
    (hmem : fn ∈ F.toArray) : F[fn.name.name]? = some fn := by
  obtain ⟨hs, hget⟩ := Lambda.Factory.mem_name_eq_getElem hmem rfl
  simp +instances only [Lambda.Factory.instMem, Lambda.Factory.mem] at hs
  simp +instances only [Lambda.Factory.instGetElem?, Lambda.Factory.get?,
    Lambda.Factory.get] at hget ⊢
  split
  · rename_i hnone
    have hsome := Std.HashMap.mem_iff_isSome_getElem?.mp hs
    rw [hnone] at hsome
    exact absurd hsome (by simp)
  · rename_i idx hidx
    have hval : F.nameMap[fn.name.name] = idx := (Std.HashMap.getElem?_eq_some_iff.mp hidx).2
    grind

/-- Appending `fn :: rest` succeeds only if `fn`'s name is new and appending `rest` to the
    extended factory succeeds. -/
private theorem foldlM_tryPush_cons_inv {T : LExprParams} [Inhabited T.Metadata]
    [Std.ToFormat T.IDMeta] (fn : LFunc T) (rest : List (LFunc T)) (F F' : Factory T)
    (h : List.foldlM (fun F fn => Factory.tryPush F fn) F (fn :: rest) = .ok F') :
    ∃ hfresh : ¬ (fn.name.name ∈ F),
      List.foldlM (fun F fn => Factory.tryPush F fn) (F.push fn hfresh) rest = .ok F' := by
  simp only [List.foldlM_cons, bind, Except.bind] at h
  elim_err h with F1 h1
  simp only [Factory.tryPush] at h1
  elim_err h1 with hfresh
  simp only [Except.ok.injEq] at h1
  subst h1
  exact ⟨hfresh, h⟩

/-- Every function in the factory after appending a list was stored before or is in the list. -/
theorem mem_foldlM_tryPush {T : LExprParams} [Inhabited T.Metadata] [Std.ToFormat T.IDMeta]
    (l : List (LFunc T)) : ∀ (F F' : Lambda.Factory T),
      l.foldlM (fun F fn => Lambda.Factory.tryPush F fn) F = .ok F' →
      ∀ g ∈ F'.toArray, g ∈ F.toArray ∨ g ∈ l := by
  induction l with
  | nil =>
    intro F F' h g hg
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact Or.inl hg
  | cons fn rest ih =>
    intro F F' h g hg
    obtain ⟨hfresh, h⟩ := foldlM_tryPush_cons_inv fn rest F F' h
    rcases ih _ F' h g hg with hl | hr
    · have hpush : g ∈ F.toArray.push fn := by
        simpa only [Lambda.Factory.push] using hl
      rcases Array.mem_push.mp hpush with h' | h'
      · exact Or.inl h'
      · exact Or.inr (by rw [h']; exact List.mem_cons_self)
    · exact Or.inr (List.mem_cons_of_mem fn hr)

/-- Successfully appending a list of functions to a factory places them after
    its existing functions, in list order. -/
theorem toList_toArray_foldlM_tryPush {T : LExprParams} [Inhabited T.Metadata]
    [Std.ToFormat T.IDMeta] (l : List (LFunc T)) : ∀ (F F' : Factory T),
      l.foldlM (fun F fn => Factory.tryPush F fn) F = .ok F' →
      F'.toArray.toList = F.toArray.toList ++ l := by
  induction l with
  | nil =>
    intro F F' h
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact (List.append_nil _).symm
  | cons fn rest ih =>
    intro F F' h
    obtain ⟨hfresh, h⟩ := foldlM_tryPush_cons_inv fn rest F F' h
    rw [ih _ F' h]
    simp only [Factory.push, Array.toList_push, List.append_assoc,
      List.singleton_append]

/-- Every function in the factory after a successful push was stored before or is the pushed
    one. -/
theorem mem_tryPush {T : LExprParams} [Inhabited T.Metadata] [Std.ToFormat T.IDMeta]
    {F F' : Lambda.Factory T} {fn : LFunc T} (h : F.tryPush fn = .ok F') :
    ∀ g ∈ F'.toArray, g ∈ F.toArray ∨ g = fn := by
  have hl : [fn].foldlM (fun F fn => Lambda.Factory.tryPush F fn) F = .ok F' := by
    rw [List.foldlM_cons, h]
    rfl
  intro g hg
  rcases mem_foldlM_tryPush [fn] F F' hl g hg with hold | hnew
  · exact .inl hold
  · exact .inr (List.mem_singleton.mp hnew)

/-- A name is in the factory iff looking it up succeeds. -/
theorem mem_iff_getElem?_isSome {T : LExprParams} (F : Factory T) (nm : String) :
    nm ∈ F ↔ (F[nm]?).isSome = true := by
  constructor
  · intro hmem
    obtain ⟨fn, hfn, hname⟩ := Array.mem_map.mp ((mem_iff_mem_names F nm).mp hmem)
    rw [← hname, getElem?_of_mem_toArray F fn hfn]
    rfl
  · intro hsome
    obtain ⟨fn, hfn⟩ := Option.isSome_iff_exists.mp hsome
    exact getElem?_some_implies_mem hfn

end Factory

/-- If `callOfLFunc` returns a triple, the function is a member of the factory array. -/
theorem callOfLFunc_func_mem
    {T : LExprParams} (F : @Factory T) (e : LExpr T.mono)
    (op : LExpr T.mono) (args : List (LExpr T.mono)) (func : LFunc T)
    (aPA : Bool)
    (h : F.callOfLFunc e (allowPartialApp := aPA) = some (op, args, func)) :
    func ∈ F.toArray := by
  simp only [Factory.callOfLFunc] at h
  cases h_lfc : getLFuncCall e with | mk op' args' =>
  simp only [h_lfc] at h
  cases op' <;> simp only [reduceCtorEq] at h
  rename_i m_op name_op ty_op
  cases h_gf : F[name_op.name]? with
  | none => simp [h_gf] at h
  | some func' =>
    simp only [h_gf] at h
    cases aPA <;> simp only [Bool.false_eq_true, ↓reduceIte] at h <;> split at h <;> simp only [Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at h
    all_goals (obtain ⟨_, _, rfl⟩ := h; exact Factory.getElem?_is_some_implies_mem h_gf)

/-! ### Successful appends have new, distinct names -/

/-- A name the factory stores is still stored after another function is added. -/
private theorem mem_push_of_mem {T : LExprParams} (F : Factory T) (fn : LFunc T)
    (hnew : ¬ (fn.name.name ∈ F)) (n : String) (h : n ∈ F) : n ∈ F.push fn hnew := by
  simp +instances only [Factory.instMem, Factory.mem, Factory.push] at h ⊢
  grind

/-- The name of a function just added to a factory is stored in it. -/
private theorem name_mem_push {T : LExprParams} (F : Factory T) (fn : LFunc T)
    (hnew : ¬ (fn.name.name ∈ F)) : fn.name.name ∈ F.push fn hnew := by
  simp +instances only [Factory.instMem, Factory.mem, Factory.push]
  grind

/-- Appending a list of functions to a factory succeeds only if none of them carries a name
    the factory stores. -/
private theorem foldlM_tryPush_name_new {T : LExprParams} [Inhabited T.Metadata]
    [Std.ToFormat T.IDMeta] (l : List (LFunc T)) : ∀ (F F' : Factory T),
      List.foldlM (fun F fn => Factory.tryPush F fn) F l = .ok F' →
      ∀ g ∈ l, ¬ (g.name.name ∈ F) := by
  induction l with
  | nil => intro _ _ _ g hg; exact absurd hg (by simp)
  | cons fn rest ih =>
    intro F F' h g hg
    obtain ⟨hfresh, h⟩ := Factory.foldlM_tryPush_cons_inv fn rest F F' h
    rcases List.mem_cons.mp hg with rfl | hg'
    · exact hfresh
    · intro hmem
      exact ih _ F' h g hg' (mem_push_of_mem F fn hfresh g.name.name hmem)

/-- Appending a list of functions to a factory succeeds only if their names are pairwise
    distinct. -/
theorem foldlM_tryPush_names_nodup {T : LExprParams} [Inhabited T.Metadata]
    [Std.ToFormat T.IDMeta] (l : List (LFunc T)) : ∀ (F F' : Factory T),
      List.foldlM (fun F fn => Factory.tryPush F fn) F l = .ok F' →
      List.Nodup (l.map (·.name.name)) := by
  induction l with
  | nil => intro _ _ _; simp
  | cons fn rest ih =>
    intro F F' h
    obtain ⟨hfresh, h⟩ := Factory.foldlM_tryPush_cons_inv fn rest F F' h
    rw [List.map_cons, List.nodup_cons]
    refine ⟨?_, ih _ F' h⟩
    intro hmem
    obtain ⟨g, hg, hgEq⟩ := List.mem_map.mp hmem
    have hnew := foldlM_tryPush_name_new rest _ F' h g hg
    rw [hgEq] at hnew
    exact hnew (name_mem_push F fn hfresh)

/-! ## Lookup transport across a `Factory.push` -/

/-- A name absent from the factory has no binding. -/
theorem Factory.getElem?_eq_none_of_not_mem {Tbase : LExprParams}
    {F : @Factory Tbase} {nm : String}
    (h : nm ∉ F) : F[nm]? = none := by
  cases hget : F[nm]? <;> grind [getElem?_some_implies_mem]

/-- `Factory.push` preserves every pre-existing binding. -/
theorem Factory.push_getElem?_of_mem {Tbase : LExprParams}
    {F : @Factory Tbase} {g : LFunc Tbase}
    (hg : g.name.name ∉ F) {nm : String} {fn : LFunc Tbase}
    (h : F[nm]? = some fn) : (F.push g hg)[nm]? = some fn := by
  grind [push_mem_match, getElem?_some_implies_mem]

/-- A factory call resolved by `F` is resolved identically by `F.push g`. -/
theorem callOfLFunc_push {Tbase : LExprParams} {F : @Factory Tbase} {g : LFunc Tbase}
    (hg : g.name.name ∉ F) {e op_expr : LExpr Tbase.mono}
    {args : List (LExpr Tbase.mono)} {lfunc : LFunc Tbase} {ap : Bool}
    (h : Factory.callOfLFunc F e (allowPartialApp := ap) = some (op_expr, args, lfunc)) :
    Factory.callOfLFunc (F.push g hg) e (allowPartialApp := ap)
      = some (op_expr, args, lfunc) := by
  grind [Factory.callOfLFunc, Factory.push_getElem?_of_mem]

/-! ## A binding invariant preserved by `Factory.tryPush` -/

public section

/-- `F` resolves the name `nm` to exactly the function `fn`. -/
@[expose] def Factory.BindsTo {T : LExprParams} (F : Factory T) (nm : String)
    (fn : LFunc T) : Prop :=
  F[nm]? = some fn

/-- A *successful* `Factory.tryPush` preserves a `Factory.BindsTo` binding: the
    pushed name is absent from `F`, hence different from the already-bound `nm`. -/
theorem Factory.BindsTo.tryPush {T : LExprParams} [Inhabited T.Metadata]
    [Std.ToFormat T.IDMeta]
    {F F' : Factory T} {g : LFunc T} {nm : String} {fn : LFunc T}
    (h : F.BindsTo nm fn) (hpush : F.tryPush g = .ok F') : F'.BindsTo nm fn := by
  grind [Factory.tryPush, push_getElem?_of_mem, BindsTo]

end -- public section
namespace Factory

section Related

variable {T : LExprParams}

/-! ### Factories related function by function -/

/-- `pushIfNew` appends a function whose name is new and leaves the factory otherwise. -/
theorem toArray_pushIfNew (F : Factory T) (g : LFunc T) :
    (F.pushIfNew g).toArray = if g.name.name ∈ F then F.toArray else F.toArray.push g := by
  unfold pushIfNew
  split <;> rfl

/-- A factory finds `g` under `n` exactly when it stores `g` and `g` is named `n`. -/
theorem getElem?_eq_some_iff' {F : Factory T} {n : String} {g : LFunc T} :
    F[n]? = some g ↔ g ∈ F.toArray ∧ g.name.name = n :=
  ⟨fun h => ⟨getElem?_is_some_implies_mem h, getElem?_name h⟩,
   fun ⟨hm, hn⟩ => hn ▸ getElem?_of_mem_toArray F g hm⟩

variable {R : LFunc T → LFunc T → Prop}

/-- Functions related one by one by a relation that keeps names have the same names. -/
private theorem forall₂_names {l l' : List (LFunc T)}
    (hname : ∀ g g', R g g' → g'.name.name = g.name.name) (h : List.Rel₂ R l l') :
    l'.map (·.name.name) = l.map (·.name.name) := by
  induction h with
  | nil => rfl
  | cons hab _ ih => simp [hname _ _ hab, ih]

/-- A function of the second of two lists related one by one is related to one of the
    first. -/
theorem forall₂_mem_right {l l' : List (LFunc T)} (h : List.Rel₂ R l l')
    {g' : LFunc T} (hg' : g' ∈ l') : ∃ g ∈ l, R g g' := by
  induction h with
  | nil => simp at hg'
  | cons hab _ ih =>
    rcases List.mem_cons.mp hg' with rfl | hg'
    · exact ⟨_, List.mem_cons_self .., hab⟩
    · obtain ⟨g, hg, hr⟩ := ih hg'
      exact ⟨g, List.mem_cons_of_mem _ hg, hr⟩

/-- Two factories whose functions are related one by one, by a relation that keeps names,
    hold the same names. -/
theorem mem_of_forall₂ {F F' : Factory T} (hname : ∀ g g', R g g' → g'.name.name = g.name.name)
    (h : List.Rel₂ R F.toArray.toList F'.toArray.toList) (n : String) : n ∈ F' ↔ n ∈ F := by
  rw [mem_iff_mem_names, mem_iff_mem_names, ← Array.mem_toList_iff, ← Array.mem_toList_iff,
    Array.toList_map, Array.toList_map, forall₂_names hname h]

/-- In two factories whose functions are related one by one, by a relation that keeps
    names, a function found under a name is related to the one the other finds. -/
theorem getElem?_of_forall₂ {F F' : Factory T}
    (hname : ∀ g g', R g g' → g'.name.name = g.name.name)
    (h : List.Rel₂ R F.toArray.toList F'.toArray.toList) {n : String} {g' : LFunc T}
    (hg' : F'[n]? = some g') : ∃ g, F[n]? = some g ∧ R g g' := by
  obtain ⟨hm, hn⟩ := getElem?_eq_some_iff'.mp hg'
  obtain ⟨g, hg, hr⟩ := forall₂_mem_right h (Array.mem_toList_iff.mpr hm)
  exact ⟨g, getElem?_eq_some_iff'.mpr ⟨Array.mem_toList_iff.mp hg, (hname _ _ hr) ▸ hn⟩, hr⟩

/-- Pushing related functions keeps two factories related function by function. -/
theorem forall₂_pushIfNew {F F' : Factory T} {g g' : LFunc T}
    (hname : ∀ g g', R g g' → g'.name.name = g.name.name)
    (h : List.Rel₂ R F.toArray.toList F'.toArray.toList) (hg : R g g') :
    List.Rel₂ R (F.pushIfNew g).toArray.toList (F'.pushIfNew g').toArray.toList := by
  rw [toArray_pushIfNew, toArray_pushIfNew, hname _ _ hg]
  by_cases hm : g.name.name ∈ F
  · have hm' : g.name.name ∈ F' := (mem_of_forall₂ hname h _).mpr hm
    simp only [hm, hm', ↓reduceIte]
    exact h
  · have hm' : g.name.name ∉ F' := fun h' => hm ((mem_of_forall₂ hname h _).mp h')
    simp only [hm, hm', ↓reduceIte, Array.toList_push]
    exact List.Rel₂.append h (.cons hg .nil)

/-- Pushing the same functions keeps two factories related function by function, for a
    reflexive relation. -/
theorem forall₂_foldl_pushIfNew {F F' : Factory T}
    (hname : ∀ g g', R g g' → g'.name.name = g.name.name) (hrefl : ∀ g, R g g) :
    ∀ (fs : List (LFunc T)), List.Rel₂ R F.toArray.toList F'.toArray.toList →
      List.Rel₂ R (fs.foldl pushIfNew F).toArray.toList (fs.foldl pushIfNew F').toArray.toList
  | [], h => h
  | g :: fs, h => by
    simp only [List.foldl_cons]
    exact forall₂_foldl_pushIfNew (F := F.pushIfNew g) (F' := F'.pushIfNew g) hname hrefl fs
      (forall₂_pushIfNew hname h (hrefl g))

end Related

section Maps

variable {T : LExprParams}

/-! ## Factories that differ only in function attributes

A factory `G` is a map of `F` by `g` when it holds the images under `g` of `F`'s functions,
under the same names. When `g` changes only attributes, which no semantic condition reads
except `shortCircuit` and constructor identity, every condition on `F` carries to `G`. -/

/-- `G` holds the images under `g` of `F`'s functions, each under its name. -/
structure IsMapOf (F G : @Factory T) (g : LFunc T → LFunc T) : Prop where
  mem : ∀ fn, fn ∈ G.toArray → ∃ fn0 ∈ F.toArray, fn = g fn0
  get : ∀ (n : String) fn0, F[n]? = some fn0 → G[n]? = some (g fn0)
  get' : ∀ (n : String) fn, G[n]? = some fn → ∃ fn0, F[n]? = some fn0 ∧ fn = g fn0

/-- `g` changes only attributes, keeps whether a function short-circuits, and leaves
    constructors as they are. -/
structure AttrOnly (g : LFunc T → LFunc T) : Prop where
  eq : ∀ f, g f = { f with attr := (g f).attr }
  shortCircuit : ∀ f, Strata.DL.Util.FuncAttr.hasShortCircuit (g f).attr = Bool.true →
    Strata.DL.Util.FuncAttr.hasShortCircuit f.attr = Bool.true
  constr : ∀ c d, g (constrFunc c d) = constrFunc c d

/-- A map of a factory holds exactly the names the factory holds. -/
theorem IsMapOf.mem_iff {F G : @Factory T} {g} (h : IsMapOf F G g) (n : String) :
    n ∈ G ↔ n ∈ F := by
  rw [mem_iff_getElem?_isSome, mem_iff_getElem?_isSome]
  constructor
  · intro hs
    obtain ⟨fn, hfn⟩ := Option.isSome_iff_exists.mp hs
    obtain ⟨fn0, h0, -⟩ := h.get' n fn hfn
    simp [h0]
  · intro hs
    obtain ⟨fn0, h0⟩ := Option.isSome_iff_exists.mp hs
    simp [h.get n fn0 h0]

/-- A map of a factory finds, under each name, the image of what the factory finds. -/
theorem IsMapOf.getElem {F G : @Factory T} {g} (h : IsMapOf F G g) {n : String} (hn : n ∈ G) :
    G[n]'hn = g (F[n]'((h.mem_iff n).mp hn)) := by
  have hF : F[n]? = some (F[n]'((h.mem_iff n).mp hn)) := by
    obtain ⟨fn, hfn⟩ := Option.isSome_iff_exists.mp
      ((mem_iff_getElem?_isSome F n).mp ((h.mem_iff n).mp hn))
    rw [hfn, getElem?_some_getElem hfn]
  exact getElem?_some_getElem (h.get n _ hF)

/-- A map changing only attributes keeps the type substitution an operator call gets. -/
theorem AttrOnly.opTypeSubst {g : LFunc T → LFunc T} (hg : AttrOnly g) (fn : LFunc T)
    (e : LExpr T.mono) : LFunc.opTypeSubst (g fn) e = LFunc.opTypeSubst fn e := by
  rw [hg.eq fn]; rfl

/-- Every function of a map of a factory is the image of one of its functions. -/
theorem IsMapOf.mem_toArray {F G : @Factory T} {g} (h : IsMapOf F G g) {fn : LFunc T}
    (hfn : fn ∈ G.toArray) : ∃ fn0 ∈ F.toArray, fn = g fn0 := h.mem fn hfn

/-- Maps of factories compose. -/
theorem IsMapOf.trans {F G H : @Factory T} {g g'} (h : IsMapOf F G g) (h' : IsMapOf G H g') :
    IsMapOf F H (g' ∘ g) where
  mem fn hfn := by
    obtain ⟨fn1, h1, rfl⟩ := h'.mem fn hfn
    obtain ⟨fn0, h0, rfl⟩ := h.mem fn1 h1
    exact ⟨fn0, h0, rfl⟩
  get n fn0 hF := h'.get n _ (h.get n fn0 hF)
  get' n fn hH := by
    obtain ⟨fn1, h1, rfl⟩ := h'.get' n fn hH
    obtain ⟨fn0, h0, rfl⟩ := h.get' n fn1 h1
    exact ⟨fn0, h0, rfl⟩

/-- The identity changes only attributes. -/
theorem AttrOnly.id : AttrOnly (T := T) id := ⟨fun _ => rfl, fun _ h => h, fun _ _ => rfl⟩

/-- **A factory built from a map of another's functions is a map of it**, when the map keeps
    names. -/
theorem isMapOf_ofArray_map (F : @Factory T) (g : LFunc T → LFunc T)
    (hname : ∀ f, (g f).name.name = f.name.name) : IsMapOf F (Factory.ofArray (F.toArray.map g)) g
        := by
  have hnd : List.Nodup ((F.toArray.map g).toList.map (·.name.name)) := by
    simp only [Array.toList_map, List.map_map]
    have : (fun f : LFunc T => f.name.name) ∘ g = fun f => f.name.name := funext hname
    rw [this]
    exact name_nodup F
  refine ⟨fun fn hfn => ?_, fun n fn0 hF => ?_, fun n fn hG => ?_⟩
  · obtain ⟨fn0, h0, rfl⟩ := Array.mem_map.mp (ofArray_mem hfn)
    exact ⟨fn0, h0, rfl⟩
  · have hmem := getElem?_is_some_implies_mem hF
    have hn := getElem?_name hF
    have hget := get?_ofArray_of_mem (Array.mem_map_of_mem (f := g) hmem) hnd
    rw [hname, hn] at hget
    exact hget
  · have hmem := getElem?_is_some_implies_mem hG
    obtain ⟨fn0, h0, rfl⟩ := Array.mem_map.mp (ofArray_mem hmem)
    have hn := getElem?_name hG
    rw [hname] at hn
    exact ⟨fn0, hn ▸ getElem?_of_mem_toArray F fn0 h0, rfl⟩

/-! ### Lookups as list searches -/

/-- Looking a name up finds the first function of that name. -/
theorem getElem?_eq_find? (F : @Factory T) (n : String) :
    F[n]? = F.toArray.toList.find? (fun f => f.name.name == n) := by
  rcases hf : F.toArray.toList.find? (fun f => f.name.name == n) with _ | fn
  · rcases hg : F[n]? with _ | fn
    · rw [hf]
    · have hmem := getElem?_is_some_implies_mem hg
      have hn := getElem?_name hg
      have := List.find?_eq_none.mp hf fn (Array.mem_def.mp hmem)
      simp [hn] at this
  · have hmem := Array.mem_def.mpr (List.mem_of_find?_eq_some hf)
    have hn : fn.name.name = n := by simpa using List.find?_some hf
    rw [hf, ← hn]
    exact getElem?_of_mem_toArray F fn hmem

/-- `pushIfNew` adds a function under its name only when the name is free. -/
theorem getElem?_pushIfNew (F : @Factory T) (fn : LFunc T) (n : String) :
    (F.pushIfNew fn)[n]? = (F[n]?).or (if fn.name.name = n then some fn else none) := by
  rw [getElem?_eq_find?, getElem?_eq_find?, toArray_pushIfNew]
  split
  · rename_i hin
    split
    · rename_i hn
      subst hn
      obtain ⟨g, hg⟩ := Option.isSome_iff_exists.mp ((mem_iff_getElem?_isSome F _).mp hin)
      rw [getElem?_eq_find? F] at hg
      rw [hg]; rfl
    · simp
  · rw [Array.toList_push, List.find?_append]
    split <;> simp_all

/-- Pushing a list of functions finds a name in the factory first, then in the list. -/
theorem getElem?_foldl_pushIfNew (L : List (LFunc T)) (F : @Factory T) (n : String) :
    (L.foldl pushIfNew F)[n]? = (F[n]?).or (L.find? (fun f => f.name.name == n)) := by
  induction L generalizing F with
  | nil => simp
  | cons fn rest ih =>
    simp only [List.foldl_cons, ih, getElem?_pushIfNew, List.find?_cons]
    by_cases h : fn.name.name = n
    · simp [h]
    · have : (fn.name.name == n) = Bool.false := by simpa using h
      simp [h, this]

/-- A factory built from an array finds a name at the first function of that name. -/
theorem getElem?_ofArray (a : Array (LFunc T)) (n : String) :
    (Factory.ofArray a)[n]? = a.toList.find? (fun f => f.name.name == n) := by
  unfold Factory.ofArray Factory.append
  rw [← Array.foldl_toList, getElem?_foldl_pushIfNew]
  have : (Factory.default : @Factory T)[n]? = none := by
    rw [getElem?_eq_find?]; simp
  rw [this]; rfl

/-- Adding functions that all succeed in being added is pushing them. -/
private theorem foldlM_tryPush_eq (L : List (LFunc T)) [Inhabited T.Metadata]
    [Std.ToFormat T.IDMeta] (F F' : @Factory T)
    (h : L.foldlM (fun F fn => Factory.tryPush F fn) F = .ok F') :
    F' = L.foldl pushIfNew F := by
  induction L generalizing F with
  | nil => simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h; exact h.symm
  | cons fn rest ih =>
    simp only [List.foldlM_cons, bind, Except.bind] at h
    rcases hp : F.tryPush fn with _ | F1
    · rw [hp] at h; cases h
    · rw [hp] at h
      unfold tryPush at hp
      split at hp
      · cases hp
      · rename_i hfresh
        simp only [Except.ok.injEq] at hp
        subst hp
        simp only [List.foldl_cons, pushIfNew, hfresh, dite_false]
        exact ih _ h

/-- Adding a factory finds a name in the first one, then in the second. -/
theorem getElem?_addFactory [Inhabited T.Metadata] [Std.ToFormat T.IDMeta] {F G F' : @Factory T}
    (h : F.addFactory G = .ok F') (n : String) : F'[n]? = (F[n]?).or (G[n]?) := by
  unfold addFactory tryAddAll at h
  rw [← Array.foldlM_toList] at h
  rw [foldlM_tryPush_eq _ F F' h, getElem?_foldl_pushIfNew, getElem?_eq_find? G]

/-- Two factories with the same lookups hold the same functions. -/
theorem isMapOf_id_of_getElem? {F G : @Factory T} (h : ∀ n : String, G[n]? = F[n]?) :
    IsMapOf F G id where
  mem fn hfn := by
    have hg := getElem?_of_mem_toArray G fn hfn
    rw [h] at hg
    exact ⟨fn, getElem?_is_some_implies_mem hg, rfl⟩
  get n fn0 hF := by rw [h]; exact hF
  get' n fn hG := ⟨fn, by rw [← h]; exact hG, rfl⟩

/-- A factory built from the images of another's functions finds the image of what that one
    finds. -/
theorem getElem?_ofArray_map (F : @Factory T) (g : LFunc T → LFunc T)
    (hname : ∀ f, (g f).name.name = f.name.name) (n : String) :
    (Factory.ofArray (F.toArray.map g))[n]? = (F[n]?).map g := by
  have h := isMapOf_ofArray_map F g hname
  rcases hF : F[n]? with _ | fn
  · rcases hG : (Factory.ofArray (F.toArray.map g))[n]? with _ | fn'
    · rfl
    · obtain ⟨fn0, h0, -⟩ := h.get' n fn' hG; rw [hF] at h0; cases h0
  · exact h.get n fn hF

/-- Pushing the same function onto factories with the same lookups keeps their lookups equal. -/
theorem lookup_pushIfNew_congr {T : LExprParams} {F1 F2 : Factory T}
    (h : ∀ n : String, F1[n]? = F2[n]?) (f : LFunc T) :
    ∀ n : String, (F1.pushIfNew f)[n]? = (F2.pushIfNew f)[n]? := by
  intro n
  rw [getElem?_pushIfNew, getElem?_pushIfNew, h n]

/-- A successful `tryPush` is `pushIfNew`. -/
theorem tryPush_eq_pushIfNew {T : LExprParams} [Inhabited T.Metadata] [Std.ToFormat T.IDMeta]
    {F F' : Factory T} {f : LFunc T} (h : F.tryPush f = .ok F') : F' = F.pushIfNew f := by
  unfold tryPush at h
  unfold pushIfNew
  split at h
  · cases h
  · rename_i hn
    cases h
    simp [hn]

/-- **A successful `tryPush` fold has the lookups of the `pushIfNew` fold**, from factories with
    the same lookups. -/
theorem lookup_tryAddAll_congr {T : LExprParams} [Inhabited T.Metadata] [Std.ToFormat T.IDMeta] :
    ∀ (l : List (LFunc T)) {F1 F2 F1' : Factory T}, (∀ n : String, F1[n]? = F2[n]?) →
      (l.foldlM (·.tryPush ·) F1 : Except Strata.Message (Factory T)) = .ok F1' →
      ∀ n : String, F1'[n]? = (l.foldl pushIfNew F2)[n]?
  | [], F1, F2, F1', h, hok => by
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at hok
    subst hok
    exact h
  | f :: l, F1, F2, F1', h, hok => by
    simp only [List.foldlM_cons, bind, Except.bind] at hok
    split at hok
    · cases hok
    · rename_i G hG
      rw [tryPush_eq_pushIfNew hG] at hok
      exact lookup_tryAddAll_congr l (lookup_pushIfNew_congr h f) hok

end Maps

end Factory

end Lambda
