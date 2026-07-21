/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import all Strata.DL.Lambda.Factory

/-!
## Properties of `Lambda.Factory`

Theorems about `Factory.callOfLFunc`, `getLFuncCall`, and related definitions.

Note: several theorems currently live in `Strata.DL.Lambda.Factory` itself
(e.g. `callOfLFunc_eq_some`, `callOfLFunc_getLFuncCall`, `callOfLFunc_smaller`).
They will be migrated here in a future cleanup.
-/

namespace Lambda

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

end Lambda
