/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import all Strata.DL.Lambda.Factory

/-!
## Properties of `Lambda.Factory`

Theorems about `Factory`, `Factory.callOfLFunc`, `getLFuncCall`, and related
definitions.

### `callOfLFunc` / `getLFuncCall`
These characterize what a successful call decomposition tells you: `callOfLFunc`
yields an `.op` callee that resolves to a factory function of matching arity
(`callOfLFunc_eq_some`, `callOfLFunc_arity`, `callOfLFunc_getElem?`), whose
callee/args coincide with `getLFuncCall`'s decomposition (`callOfLFunc_getLFuncCall`)
and whose function is a member of the factory (`callOfLFunc_func_mem`). It fails on
free variables (`callOfLFunc_fvar_none`). A set of size lemmas (`getLFuncCall.go_size`,
`getLFuncCall_smaller`, `callOfLFunc_smaller`) shows extracted arguments are
structurally smaller than the original expression, which is used for termination.

### Factory membership / lookup (`namespace Factory`)
These relate the three views of a factory — its name set, its backing array, and
`get?`/`get` lookups. Names are unique (`name_nodup`), the default factory is empty
(`toArray_default`, `default_mem_is_false`), and `push`/`pushIfNew` update membership
and lookups predictably (`push_mem_iff`, `push_mem_match`, `mem_iff_mem_names`). A
family of `getElem?_*`/`mem_name_eq_getElem` lemmas connects a successful lookup to
array membership and names, and the `ofArray`/`get?_foldl_pushIfNew_*` lemmas lift
these facts to factories built from arrays.

### `LFunc` conversions and type substitution
These are the algebraic facts about `LFunc` plumbing. The `LFuncDefined ↔ LFunc`
conversions are mutually inverse (`LFuncDefined.toLFunc_toFunc`,
`LFunc.toFunc_toLFunc`). The remaining lemmas unfold type-substitution helpers:
`applySubst` reduces to `replaceUserProvidedType`
(`LExpr.applySubst_eq_replaceUserProvidedType`) and `computeTypeSubst` agrees with
`opTypeSubst` whenever the latter succeeds (`LFunc.computeTypeSubst_of_opTypeSubst`).
-/

namespace Lambda

theorem callOfLFunc_eq_some {GenericTy} {F : Factory T}
    {e callee : LExpr ⟨T, GenericTy⟩} {args : List (LExpr ⟨T, GenericTy⟩)} {fn : LFunc T}
    (hcall : Factory.callOfLFunc F e = some (callee, args, fn))
    : ∃ m name ty, callee = .op m name ty ∧
      F[name.name]? = some fn ∧ args.length = fn.inputs.length := by
  simp [Factory.callOfLFunc] at hcall
  split at hcall <;> simp_all
  split at hcall <;> try contradiction
  split at hcall <;> try contradiction
  cases hcall
  grind

theorem callOfLFunc_getLFuncCall {GenericTy} {F : Factory T}
    {e callee : LExpr ⟨T, GenericTy⟩} {args : List (LExpr ⟨T, GenericTy⟩)} {fn : LFunc T}
    {aPA : Bool}
    (hcall : Factory.callOfLFunc F e (allowPartialApp := aPA) = some (callee, args, fn))
    : getLFuncCall e = (callee, args) := by
  simp [Factory.callOfLFunc] at hcall
  split at hcall <;> simp_all
  split at hcall <;> try contradiction
  cases aPA <;> simp at hcall <;> split at hcall <;> simp at hcall
  all_goals (obtain ⟨rfl, rfl, rfl⟩ := hcall; exact Prod.ext ‹_› rfl)

theorem getLFuncCall.go_size {T: LExprParamsT} {e: LExpr T} {op args acc} : getLFuncCall.go e acc = (op, args) →
op.sizeOf + List.sum (args.map LExpr.sizeOf) <= e.sizeOf + List.sum (acc.map LExpr.sizeOf) := by
  fun_induction go generalizing op args
  case case1 acc e' arg1 arg2 IH =>
    intros Hgo; specialize (IH Hgo); simp_all; omega
  case case2 acc fn fnty arg1 =>
    simp_all; intros op_eq args_eq; subst op args; simp; omega
  case case3 op' args' _ _ => intros Hop; cases Hop; omega

theorem getLFuncCall_smaller {T} {e: LExpr T} {op args} : getLFuncCall e = (op, args) → (forall a, a ∈ args → a.sizeOf < e.sizeOf) := by
  unfold getLFuncCall
  intros Hgo
  have Hsize := (getLFuncCall.go_size Hgo)
  simp_all
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
  simp[Factory.callOfLFunc]; cases Hfunc: (getLFuncCall e) with | mk op args;
  simp; cases op <;> simp
  rename_i o ty; cases F[o.name]? <;> simp
  rename_i F'
  cases allowPartialMatch
  · cases (args.length == List.length F'.inputs) <;> simp; intros op_eq args_eq F_eq
    subst op args F'; exact (getLFuncCall_smaller Hfunc)
  · cases (Nat.ble args.length (List.length F'.inputs)) <;> simp
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
  simp [Factory.callOfLFunc] at hcall
  split at hcall <;> simp_all
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
  simp [Factory.callOfLFunc] at hcall
  split at hcall <;> simp_all
  split at hcall <;> try contradiction
  cases aPA <;> simp at hcall <;> split at hcall <;> simp at hcall
  all_goals (obtain ⟨rfl, rfl, rfl⟩ := hcall; grind)

theorem LExpr.applySubst_eq_replaceUserProvidedType {T : LExprParams}
    (e : LExpr T.mono) (S : Subst) :
    e.applySubst S = replaceUserProvidedType e (LMonoTy.subst S) := by
  unfold applySubst
  split
  case isTrue h_empty =>
    have h_id : LMonoTy.subst S = id := funext (fun ty => LMonoTy.subst_emptyS h_empty)
    rw [h_id]
    induction e <;> unfold replaceUserProvidedType <;> grind
  case isFalse => rfl

/-- When `opTypeSubst` succeeds, `computeTypeSubst` agrees with it. -/
theorem LFunc.computeTypeSubst_of_opTypeSubst {T : LExprParams}
    {fn : LFunc T} {callee : LExpr T.mono} {args : List (LExpr T.mono)} {s : Subst}
    (h : fn.opTypeSubst callee = some s)
    : fn.computeTypeSubst callee args = some s := by
  unfold LFunc.computeTypeSubst
  rw [h]

/-- Lifting an `LFuncDefined` to the full `LFunc` then projecting back recovers
    the original. -/
theorem LFuncDefined.toLFunc_toFunc {T : LExprParams} (f : LFuncDefined T)
    (ce : Option (T.Metadata → List (LExpr T.mono) → Option (LExpr T.mono))) :
    (f.toLFunc ce).toFunc = f := rfl

/-- Projecting an `LFunc` to its base then lifting back (restoring
    `concreteEval`) recovers the original. -/
theorem LFunc.toFunc_toLFunc {T : LExprParams} (l : LFunc T) :
    LFuncDefined.toLFunc l.toFunc l.concreteEval = l := rfl

/-- `callOfLFunc` returns `none` for free-variable expressions. -/
theorem callOfLFunc_fvar_none {Tbase : LExprParams} {GenericTy} (F : @Factory Tbase)
    (m : Tbase.Metadata) (v : Tbase.Identifier) (ty : Option GenericTy) :
    Factory.callOfLFunc F (.fvar m v ty : LExpr ⟨Tbase, GenericTy⟩) = none := by
  cases h : Factory.callOfLFunc F (.fvar m v ty : LExpr ⟨Tbase, GenericTy⟩) with
  | none => rfl
  | some val =>
    obtain ⟨callee, args, fn⟩ := val
    have hgl := callOfLFunc_getLFuncCall h
    have hfvar : getLFuncCall (.fvar m v ty : LExpr ⟨Tbase, GenericTy⟩) = (.fvar m v ty, []) := by
      unfold getLFuncCall getLFuncCall.go; rfl
    rw [hfvar] at hgl
    have ⟨_, _, _, hop, _, _⟩ := callOfLFunc_eq_some h
    rw [← (Prod.mk.inj hgl).1] at hop
    exact absurd hop (by simp)


namespace Factory

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
  simp [Factory.default] at q
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
    exact ⟨f.nameMap[s], by simp [Array.size_map]; exact hvalid, by simp [Array.getElem_map]; exact hcons⟩
  · intro hs
    rw [Array.mem_iff_getElem] at hs
    obtain ⟨i, hi, hname⟩ := hs
    simp [Array.size_map] at hi
    simp [Array.getElem_map] at hname
    have := f.toArrayDefined ⟨i, hi⟩
    simp +instances [instMem, Factory.mem]
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
  simp +instances [instGetElem?, Factory.get?, Factory.get] at eq ⊢
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
    rw [push_mem_match, if_neg (fun h => hne h.symm)]
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
        unfold Factory.pushIfNew; rw [dif_neg hnew_g]
      have hpres : (F.pushIfNew g)[g.name.name]? = some g := by
        rw [hpush, push_mem_match, if_pos rfl]
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
  cases op' <;> simp at h
  rename_i m_op name_op ty_op
  cases h_gf : F[name_op.name]? with
  | none => simp [h_gf] at h
  | some func' =>
    simp only [h_gf] at h
    cases aPA <;> simp at h <;> split at h <;> simp at h
    all_goals (obtain ⟨_, _, rfl⟩ := h; exact Factory.getElem?_is_some_implies_mem h_gf)

end Lambda
