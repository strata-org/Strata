/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import all Strata.Languages.Core.FunctionTypeSpec
import all Strata.Languages.Core.FunctionType
import all Strata.DL.Lambda.Factory
import all Strata.DL.Lambda.LExprResolveProps
import all Strata.DL.Lambda.LExprTypeSpec
import all Strata.DL.Lambda.Denote.LExprDenoteTySubst
import all Strata.DL.Util.Nodup

/-! ## Soundness of Function Typechecker

Relates the executable function typechecker `Function.typeCheck` to the
declarative typing specifications `FuncHasType` and `FuncHasTypeA`.
-/

namespace Core
namespace TypeSpec

open Lambda LExpr Imperative

/-! ### Helper Lemmas -/

/-- If `LFunc.type` succeeds, the type args are nodup. -/
theorem LFunc.type_typeArgs_nodup {T : LExprParams} [DecidableEq T.IDMeta]
    (f : LFunc T) (ty : LTy) (h : f.type = .ok ty) :
    f.typeArgs.Nodup := by
  simp only [LFunc.type, bind, Except.bind] at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  rename_i _ h_tyargs_neg
  simp at h_tyargs_neg
  exact h_tyargs_neg

/-- If `LTy.freeVars (forAll xs m) = []`, then all free vars of `m` are in `xs`. -/
theorem LTy.freeVars_nil_imp_mem (xs : List TyIdentifier) (m : LMonoTy)
    (h : LTy.freeVars (.forAll xs m) = []) :
    ∀ v, v ∈ LMonoTy.freeVars m → v ∈ xs := by
  intro v hv
  simp only [LTy.freeVars] at h
  rcases Decidable.em (v ∈ xs) with hmem | hc
  · exact hmem
  · exfalso
    have hin : v ∈ (LMonoTy.freeVars m).removeAll xs := by
      simp only [List.removeAll, List.mem_filter, List.elem_eq_mem, Bool.not_eq_eq_eq_not,
        Bool.not_true, decide_eq_false_iff_not]
      exact ⟨hv, hc⟩
    rw [h] at hin
    exact absurd hin List.not_mem_nil

/-- Applying a type substitution to an `AbsWF` `LExprT` preserves `HasTypeA`,
    mapping the type through `subst S`. The `AbsWF` precondition (every abs
    subnode has arrow-typed metadata) is essential: it is what makes `applySubstT`
    (rewriting metadata) commute with `applySubst` (rewriting annotation fields).
    It is established for `resolve` outputs by `resolve_AbsWF`. -/
theorem applySubstT_unresolved_HasTypeA {T : LExprParams} [DecidableEq T.IDMeta]
    (et : LExprT T.mono) (S : Subst) (Δ : List LMonoTy)
    (h_wf : LExprT.AbsWF et)
    (h : LExpr.HasTypeA Δ et.unresolved (et.toLMonoTy)) :
    LExpr.HasTypeA (Δ.map (LMonoTy.subst S)) (applySubstT et S).unresolved
      ((applySubstT et S).toLMonoTy) := by
  rw [applySubstT_toLMonoTy, applySubstT_unresolved_eq_applySubst et S h_wf]
  exact applySubst_typeCheck S h

/-- The filterMap building the renameSubst preserves keys: a key of the filtered map
    was already a key of `L`. (The kept entries have first component `p.1`.) -/
private theorem mem_keys_renameMap_imp
    (L : List (TyIdentifier × TyIdentifier)) (y : TyIdentifier)
    (h : y ∈ (L.filterMap
        (fun p => if p.1 == p.2 then none else some (p.1, LMonoTy.ftvar p.2))).map Prod.fst) :
    y ∈ L.map Prod.fst := by
  obtain ⟨q, hq_mem, hq_fst⟩ := List.mem_map.mp h
  obtain ⟨p, hp_mem, hp_eq⟩ := List.mem_filterMap.mp hq_mem
  refine List.mem_map.mpr ⟨p, hp_mem, ?_⟩
  by_cases hpf : p.1 == p.2
  · rw [if_pos hpf] at hp_eq; exact absurd hp_eq (by simp)
  · rw [if_neg hpf] at hp_eq
    rw [Option.some.injEq] at hp_eq
    rw [← hq_fst, ← hp_eq]

/-- Lookup in the renameSubst map built from a key-distinct association list `L`.
    For an entry `(y, x) ∈ L`, the filtered map sends `y` to `ftvar x` unless the entry
    was a fixed point (`y = x`), in which case `y` is absent. Used with `L := bwdMap.toList`,
    whose keys are distinct (`Std.HashMap.distinct_keys_toList`). -/
private theorem find?_renameMap_of_mem
    (L : List (TyIdentifier × TyIdentifier))
    (hnd : (L.map Prod.fst).Nodup)
    (y x : TyIdentifier) (hmem : (y, x) ∈ L) :
    Map.find?
      (L.filterMap (fun p => if p.1 == p.2 then none else some (p.1, LMonoTy.ftvar p.2))) y
      = if y = x then none else some (LMonoTy.ftvar x) := by
  induction L with
  | nil => simp at hmem
  | cons hd rest ih =>
    obtain ⟨k, v⟩ := hd
    simp only [List.map_cons, List.nodup_cons] at hnd
    obtain ⟨hk_notin, hnd_rest⟩ := hnd
    rw [List.filterMap_cons]
    simp only [beq_iff_eq]
    rcases List.mem_cons.mp hmem with h_mem_hd | h_mem_rest
    · -- the head is exactly the entry we look up
      cases h_mem_hd
      by_cases h_fix : y = x
      · -- fixed point: head filtered out; y absent from rest (key-distinct)
        rw [if_pos h_fix, if_pos h_fix]
        show Map.find? (rest.filterMap _) y = none
        apply Map.findNone_eq_notmem_mapfst.mp
        intro hc
        refine hk_notin (mem_keys_renameMap_imp rest y ?_)
        simpa only [beq_iff_eq] using hc
      · -- non-fixed-point: head kept as (y, ftvar x); find? hits it immediately
        rw [if_neg h_fix, if_neg h_fix]
        show Map.find? ((y, LMonoTy.ftvar x) :: _) y = some (LMonoTy.ftvar x)
        rw [Map.find?, if_pos rfl]
    · -- entry is in the tail; head key k ≠ y so find? skips it, recurse
      have hy_in_rest : y ∈ rest.map Prod.fst :=
        List.mem_map.mpr ⟨(y, x), h_mem_rest, rfl⟩
      have hk_ne_y : k ≠ y := fun heq => hk_notin (heq ▸ hy_in_rest)
      have ih' : Map.find?
          (rest.filterMap fun p => if p.1 = p.2 then none else some (p.1, LMonoTy.ftvar p.2)) y
          = if y = x then none else some (LMonoTy.ftvar x) := by
        have := ih hnd_rest h_mem_rest
        simpa only [beq_iff_eq] using this
      by_cases hkv : k = v
      · rw [if_pos hkv]; exact ih'
      · rw [if_neg hkv, Map.find?, if_neg hk_ne_y]; exact ih'

/-- Monotonicity of the backward map across `goList`: existing entries are never
    overwritten. Parameterized by the per-element monotonicity of `go` (supplied by the
    structural IH at the `tcons` case of `go_bwd_mono`). -/
private theorem goList_bwd_mono (ts1 : List LMonoTy)
    (hgo : ∀ a ∈ ts1, ∀ (t2 : LMonoTy) (fwd bwd fwd' bwd' : Std.HashMap TyIdentifier TyIdentifier),
        LMonoTy.alphaEquivMap.go a t2 fwd bwd = some (fwd', bwd') →
        ∀ (y x : TyIdentifier), bwd[y]? = some x → bwd'[y]? = some x) :
    ∀ (ts2 : List LMonoTy) (fwd bwd fwd' bwd' : Std.HashMap TyIdentifier TyIdentifier),
      LMonoTy.alphaEquivMap.goList ts1 ts2 fwd bwd = some (fwd', bwd') →
      ∀ (y x : TyIdentifier), bwd[y]? = some x → bwd'[y]? = some x := by
  induction ts1 with
  | nil =>
    intro ts2 fwd bwd fwd' bwd' hgl y x hyx
    cases ts2 with
    | nil =>
      unfold LMonoTy.alphaEquivMap.goList at hgl
      simp only [Option.some.injEq, Prod.mk.injEq] at hgl
      obtain ⟨_, hb⟩ := hgl; rw [← hb]; exact hyx
    | cons b bs =>
      exact absurd hgl (by unfold LMonoTy.alphaEquivMap.goList; simp)
  | cons a as ih =>
    intro ts2 fwd bwd fwd' bwd' hgl y x hyx
    cases ts2 with
    | nil => exact absurd hgl (by unfold LMonoTy.alphaEquivMap.goList; simp)
    | cons b bs =>
      unfold LMonoTy.alphaEquivMap.goList at hgl
      cases hga : LMonoTy.alphaEquivMap.go a b fwd bwd with
      | none => rw [hga] at hgl; exact absurd hgl (by simp)
      | some fb =>
        obtain ⟨f1, b1⟩ := fb
        rw [hga] at hgl
        have hmono_a := hgo a (List.mem_cons_self ..) b fwd bwd f1 b1 hga y x hyx
        exact ih (fun c hc => hgo c (List.mem_cons_of_mem a hc)) bs f1 b1 fwd' bwd' hgl y x hmono_a

/-- Monotonicity of the backward map across `go`: existing entries are never overwritten. -/
private theorem go_bwd_mono (t1 : LMonoTy) :
    ∀ (t2 : LMonoTy) (fwd bwd fwd' bwd' : Std.HashMap TyIdentifier TyIdentifier),
      LMonoTy.alphaEquivMap.go t1 t2 fwd bwd = some (fwd', bwd') →
      ∀ (y x : TyIdentifier), bwd[y]? = some x → bwd'[y]? = some x := by
  induction t1 with
  | ftvar x1 =>
    intro t2 fwd bwd fwd' bwd' hgo y x hyx
    cases t2 with
    | ftvar y1 =>
      unfold LMonoTy.alphaEquivMap.go at hgo
      cases hfwd : fwd[x1]? with
      | some y' =>
        simp only [hfwd] at hgo
        by_cases hb : y' == y1
        · rw [if_pos hb] at hgo
          simp only [Option.some.injEq, Prod.mk.injEq] at hgo
          obtain ⟨_, hbeq⟩ := hgo; rw [← hbeq]; exact hyx
        · rw [if_neg hb] at hgo; exact absurd hgo (by simp)
      | none =>
        simp only [hfwd] at hgo
        cases hbwd : bwd[y1]? with
        | some x' =>
          simp only [hbwd] at hgo
          by_cases hb : x' == x1
          · rw [if_pos hb] at hgo
            simp only [Option.some.injEq, Prod.mk.injEq] at hgo
            obtain ⟨_, hbeq⟩ := hgo; rw [← hbeq]; exact hyx
          · rw [if_neg hb] at hgo; exact absurd hgo (by simp)
        | none =>
          simp only [hbwd] at hgo
          simp only [Option.some.injEq, Prod.mk.injEq] at hgo
          obtain ⟨_, hbeq⟩ := hgo
          rw [← hbeq]
          -- bwd' = bwd.insert y1 x1; entry at y (≠ y1, since bwd[y1]? = none ≠ some x) preserved
          have hy_ne : y1 ≠ y := by
            intro h; rw [h] at hbwd; rw [hbwd] at hyx; exact absurd hyx (by simp)
          rw [Std.HashMap.getElem?_insert]
          rw [if_neg (by simpa only [beq_iff_eq] using hy_ne)]
          exact hyx
    | bitvec n => exact absurd hgo (by unfold LMonoTy.alphaEquivMap.go; simp)
    | tcons n args => exact absurd hgo (by unfold LMonoTy.alphaEquivMap.go; simp)
  | bitvec n1 =>
    intro t2 fwd bwd fwd' bwd' hgo y x hyx
    cases t2 with
    | bitvec n2 =>
      unfold LMonoTy.alphaEquivMap.go at hgo
      by_cases hn : n1 == n2
      · rw [if_pos hn] at hgo
        simp only [Option.some.injEq, Prod.mk.injEq] at hgo
        obtain ⟨_, hbeq⟩ := hgo; rw [← hbeq]; exact hyx
      · rw [if_neg hn] at hgo; exact absurd hgo (by simp)
    | ftvar y1 => exact absurd hgo (by unfold LMonoTy.alphaEquivMap.go; simp)
    | tcons n args => exact absurd hgo (by unfold LMonoTy.alphaEquivMap.go; simp)
  | tcons name1 args1 ih =>
    intro t2 fwd bwd fwd' bwd' hgo y x hyx
    cases t2 with
    | tcons name2 args2 =>
      unfold LMonoTy.alphaEquivMap.go at hgo
      by_cases hname : name1 != name2
      · rw [if_pos hname] at hgo; exact absurd hgo (by simp)
      · rw [if_neg hname] at hgo
        exact goList_bwd_mono args1 ih args2 fwd bwd fwd' bwd' hgo y x hyx
    | ftvar y1 => exact absurd hgo (by unfold LMonoTy.alphaEquivMap.go; simp)
    | bitvec n => exact absurd hgo (by unfold LMonoTy.alphaEquivMap.go; simp)

/-- Inversion invariant for `goList`, threaded element by element. Given (P1) `bwd`
    inverts `S` and (P2) `fwd`/`bwd` are mutual inverses, success of
    `goList ts1 (ts1.map (subst S)) fwd bwd` preserves both, and the resulting `bwd'`
    contains a witness `(y, x)` for every free variable `x` of `ts1`. Parameterized by the
    per-element `go` inversion (supplied by the structural IH at `go_bwd_inverts`'s tcons). -/
private theorem goList_bwd_inverts (S : Subst) (ts1 : List LMonoTy)
    (ih : ∀ a ∈ ts1, ∀ (fwd bwd fwd' bwd' : Std.HashMap TyIdentifier TyIdentifier),
        LMonoTy.alphaEquivMap.go a (LMonoTy.subst S a) fwd bwd = some (fwd', bwd') →
        (∀ y x, bwd[y]? = some x → LMonoTy.subst S (.ftvar x) = .ftvar y) →
        (∀ (x y : TyIdentifier), fwd[x]? = some y → bwd[y]? = some x) →
        ((∀ y x, bwd'[y]? = some x → LMonoTy.subst S (.ftvar x) = .ftvar y) ∧
         (∀ (x y : TyIdentifier), fwd'[x]? = some y → bwd'[y]? = some x)) ∧
        (∀ x ∈ LMonoTy.freeVars a,
          ∃ y, LMonoTy.subst S (.ftvar x) = .ftvar y ∧ bwd'[y]? = some x)) :
    ∀ (fwd bwd fwd' bwd' : Std.HashMap TyIdentifier TyIdentifier),
      LMonoTy.alphaEquivMap.goList ts1 (ts1.map (LMonoTy.subst S)) fwd bwd = some (fwd', bwd') →
      (∀ y x, bwd[y]? = some x → LMonoTy.subst S (.ftvar x) = .ftvar y) →
      (∀ (x y : TyIdentifier), fwd[x]? = some y → bwd[y]? = some x) →
      ((∀ y x, bwd'[y]? = some x → LMonoTy.subst S (.ftvar x) = .ftvar y) ∧
       (∀ (x y : TyIdentifier), fwd'[x]? = some y → bwd'[y]? = some x)) ∧
      (∀ x ∈ LMonoTys.freeVars ts1,
        ∃ y, LMonoTy.subst S (.ftvar x) = .ftvar y ∧ bwd'[y]? = some x) := by
  induction ts1 with
  | nil =>
    intro fwd bwd fwd' bwd' hgl hP1 hP2
    rw [List.map_nil] at hgl
    unfold LMonoTy.alphaEquivMap.goList at hgl
    simp only [Option.some.injEq, Prod.mk.injEq] at hgl
    obtain ⟨hf, hb⟩ := hgl
    subst hf hb
    refine ⟨⟨hP1, hP2⟩, ?_⟩
    intro x hx
    simp only [LMonoTys.freeVars] at hx
    exact absurd hx (by simp)
  | cons a as ih_tail =>
    intro fwd bwd fwd' bwd' hgl hP1 hP2
    rw [List.map_cons] at hgl
    unfold LMonoTy.alphaEquivMap.goList at hgl
    cases hga : LMonoTy.alphaEquivMap.go a (LMonoTy.subst S a) fwd bwd with
    | none => rw [hga] at hgl; exact absurd hgl (by simp)
    | some fb =>
      obtain ⟨f1, b1⟩ := fb
      rw [hga] at hgl
      have hhead := ih a (List.mem_cons_self ..) fwd bwd f1 b1 hga hP1 hP2
      obtain ⟨⟨hP1_1, hP2_1⟩, hex_head⟩ := hhead
      have htail := ih_tail (fun c hc => ih c (List.mem_cons_of_mem a hc))
        f1 b1 fwd' bwd' hgl hP1_1 hP2_1
      obtain ⟨⟨hP1', hP2'⟩, hex_tail⟩ := htail
      refine ⟨⟨hP1', hP2'⟩, ?_⟩
      intro x hx
      simp only [LMonoTys.freeVars_of_cons, List.mem_append] at hx
      cases hx with
      | inl hx_a =>
        obtain ⟨y, hsy, hb1y⟩ := hex_head x hx_a
        have hmono := goList_bwd_mono as (fun c _ => go_bwd_mono c)
          (as.map (LMonoTy.subst S)) f1 b1 fwd' bwd' hgl y x hb1y
        exact ⟨y, hsy, hmono⟩
      | inr hx_as => exact hex_tail x hx_as

/-- Inversion invariant for `go`: success of `go t1 (subst S t1) fwd bwd` preserves
    (P1) `bwd` inverts `S` and (P2) `fwd`/`bwd` mutual-inverse, and yields a witness in
    `bwd'` for every free variable of `t1`. The `ftvar` fwd-hit branch is exactly where
    P2 is consumed (to recover `bwd[y]? = some x` from `fwd[x]? = some y`). -/
private theorem go_bwd_inverts (S : Subst) (t1 : LMonoTy) :
    ∀ (fwd bwd fwd' bwd' : Std.HashMap TyIdentifier TyIdentifier),
      LMonoTy.alphaEquivMap.go t1 (LMonoTy.subst S t1) fwd bwd = some (fwd', bwd') →
      (∀ y x, bwd[y]? = some x → LMonoTy.subst S (.ftvar x) = .ftvar y) →
      (∀ (x y : TyIdentifier), fwd[x]? = some y → bwd[y]? = some x) →
      ((∀ y x, bwd'[y]? = some x → LMonoTy.subst S (.ftvar x) = .ftvar y) ∧
       (∀ (x y : TyIdentifier), fwd'[x]? = some y → bwd'[y]? = some x)) ∧
      (∀ x ∈ LMonoTy.freeVars t1,
        ∃ y, LMonoTy.subst S (.ftvar x) = .ftvar y ∧ bwd'[y]? = some x) := by
  induction t1 with
  | ftvar x1 =>
    intro fwd bwd fwd' bwd' hgo hP1 hP2
    cases hsub : LMonoTy.subst S (.ftvar x1) with
    | bitvec n =>
      rw [hsub] at hgo; exact absurd hgo (by unfold LMonoTy.alphaEquivMap.go; simp)
    | tcons nm ar =>
      rw [hsub] at hgo; exact absurd hgo (by unfold LMonoTy.alphaEquivMap.go; simp)
    | ftvar y1 =>
      rw [hsub] at hgo
      unfold LMonoTy.alphaEquivMap.go at hgo
      cases hfwd : fwd[x1]? with
      | some y' =>
        simp only [hfwd] at hgo
        by_cases hb : y' == y1
        · rw [if_pos hb] at hgo
          simp only [Option.some.injEq, Prod.mk.injEq] at hgo
          obtain ⟨hf, hbb⟩ := hgo
          subst hf hbb
          refine ⟨⟨hP1, hP2⟩, ?_⟩
          intro x hx
          simp only [LMonoTy.freeVars, List.mem_singleton] at hx
          subst hx
          refine ⟨y1, hsub, ?_⟩
          have hy : y' = y1 := by simpa only [beq_iff_eq] using hb
          rw [hy] at hfwd
          exact hP2 x y1 hfwd
        · rw [if_neg hb] at hgo; exact absurd hgo (by simp)
      | none =>
        simp only [hfwd] at hgo
        cases hbwd : bwd[y1]? with
        | some x' =>
          simp only [hbwd] at hgo
          by_cases hb : x' == x1
          · rw [if_pos hb] at hgo
            simp only [Option.some.injEq, Prod.mk.injEq] at hgo
            obtain ⟨hf, hbb⟩ := hgo
            subst hf hbb
            refine ⟨⟨hP1, hP2⟩, ?_⟩
            intro x hx
            simp only [LMonoTy.freeVars, List.mem_singleton] at hx
            subst hx
            refine ⟨y1, hsub, ?_⟩
            have hx' : x' = x := by simpa only [beq_iff_eq] using hb
            rw [hx'] at hbwd; exact hbwd
          · rw [if_neg hb] at hgo; exact absurd hgo (by simp)
        | none =>
          simp only [hbwd] at hgo
          simp only [Option.some.injEq, Prod.mk.injEq] at hgo
          obtain ⟨hf, hbb⟩ := hgo
          subst hf hbb
          refine ⟨⟨?_, ?_⟩, ?_⟩
          · intro y x hyx
            rw [Std.HashMap.getElem?_insert] at hyx
            by_cases hyy1 : y1 == y
            · rw [if_pos hyy1] at hyx
              simp only [Option.some.injEq] at hyx
              subst hyx
              have hyeq : y1 = y := by simpa only [beq_iff_eq] using hyy1
              rw [← hyeq]; exact hsub
            · rw [if_neg hyy1] at hyx; exact hP1 y x hyx
          · intro x y hxy
            rw [Std.HashMap.getElem?_insert] at hxy
            rw [Std.HashMap.getElem?_insert]
            by_cases hxx1 : x1 == x
            · rw [if_pos hxx1] at hxy
              simp only [Option.some.injEq] at hxy
              subst hxy
              have hx1x : x1 = x := by simpa only [beq_iff_eq] using hxx1
              rw [if_pos (by simp), hx1x]
            · rw [if_neg hxx1] at hxy
              have hbwy := hP2 x y hxy
              by_cases hyy1 : y1 == y
              · have hyeq : y1 = y := by simpa only [beq_iff_eq] using hyy1
                rw [hyeq] at hbwd; rw [hbwd] at hbwy; exact absurd hbwy (by simp)
              · rw [if_neg hyy1]; exact hbwy
          · intro x hx
            simp only [LMonoTy.freeVars, List.mem_singleton] at hx
            subst hx
            refine ⟨y1, hsub, ?_⟩
            rw [Std.HashMap.getElem?_insert]; simp
  | bitvec n1 =>
    intro fwd bwd fwd' bwd' hgo hP1 hP2
    rw [LMonoTy.subst_bitvec] at hgo
    unfold LMonoTy.alphaEquivMap.go at hgo
    simp only [beq_self_eq_true, if_true, Option.some.injEq, Prod.mk.injEq] at hgo
    obtain ⟨hf, hbb⟩ := hgo
    subst hf hbb
    refine ⟨⟨hP1, hP2⟩, ?_⟩
    intro x hx
    simp only [LMonoTy.freeVars] at hx
    exact absurd hx (by simp)
  | tcons name1 args1 ih =>
    intro fwd bwd fwd' bwd' hgo hP1 hP2
    rw [LMonoTy.subst_unfold] at hgo
    unfold LMonoTy.alphaEquivMap.go at hgo
    by_cases hname : name1 != name1
    · rw [if_pos hname] at hgo; exact absurd hgo (by simp)
    · rw [if_neg hname] at hgo
      have hres := goList_bwd_inverts S args1 ih fwd bwd fwd' bwd' hgo hP1 hP2
      obtain ⟨hinv, hex⟩ := hres
      refine ⟨hinv, ?_⟩
      intro x hx
      simp only [LMonoTy.freeVars] at hx
      exact hex x hx

/-- Top-level specialization of `go_bwd_inverts`: when `alphaEquivMap monoty (subst S monoty)`
    succeeds with `bwdMap`, every free variable `x` of `monoty` has an image `y` with
    `subst S (ftvar x) = ftvar y` and `bwdMap[y]? = some x`. Obtained by running
    `go_bwd_inverts` at the empty accumulators (preconditions vacuous via `getElem?_empty`). -/
private theorem alphaEquivMap_self_subst_bwd (S : Subst) (monoty : LMonoTy)
    (bwdMap : Std.HashMap TyIdentifier TyIdentifier)
    (h_alpha : LMonoTy.alphaEquivMap monoty (LMonoTy.subst S monoty) = some bwdMap) :
    ∀ x ∈ LMonoTy.freeVars monoty,
      ∃ y, LMonoTy.subst S (.ftvar x) = .ftvar y ∧ bwdMap[y]? = some x := by
  unfold LMonoTy.alphaEquivMap at h_alpha
  cases hgo : LMonoTy.alphaEquivMap.go monoty (LMonoTy.subst S monoty) {} {} with
  | none => rw [hgo] at h_alpha; exact absurd h_alpha (by simp)
  | some fb =>
    obtain ⟨fwd0, bwd0⟩ := fb
    rw [hgo] at h_alpha
    simp only [Option.map_some, Option.some.injEq] at h_alpha
    subst h_alpha
    have hP1 : ∀ (y x : TyIdentifier),
        ({} : Std.HashMap TyIdentifier TyIdentifier)[y]? = some x →
        LMonoTy.subst S (.ftvar x) = .ftvar y := by
      intro y x hyx; rw [Std.HashMap.getElem?_empty] at hyx; exact absurd hyx (by simp)
    have hP2 : ∀ (x y : TyIdentifier),
        ({} : Std.HashMap TyIdentifier TyIdentifier)[x]? = some y →
        ({} : Std.HashMap TyIdentifier TyIdentifier)[y]? = some x := by
      intro x y hxy; rw [Std.HashMap.getElem?_empty] at hxy; exact absurd hxy (by simp)
    have hres := go_bwd_inverts S monoty {} {} fwd0 bwd0 hgo hP1 hP2
    exact hres.2

/-- Leaf case of `alphaEquivMap_renameSubst_inverse`: the renameSubst undoes `subst S`
    on any single free variable of `monoty`. The general statement follows by structural
    induction, reducing every `ftvar` leaf to this. -/
theorem alphaEquivMap_renameSubst_inverse_ftvar (monoty : LMonoTy) (S : Subst)
    (bwdMap : Std.HashMap TyIdentifier TyIdentifier)
    (h_alpha : LMonoTy.alphaEquivMap monoty (LMonoTy.subst S monoty) = some bwdMap)
    (x : TyIdentifier) (hx : x ∈ LMonoTy.freeVars monoty) :
    LMonoTy.subst
      [bwdMap.toList.filterMap (fun (k, v) => if k == v then none else some (k, LMonoTy.ftvar v))]
      (LMonoTy.subst S (.ftvar x)) = .ftvar x := by
  -- From H2: subst S (ftvar x) = ftvar y with bwdMap[y]? = some x.
  obtain ⟨y, hsy, hby⟩ := alphaEquivMap_self_subst_bwd S monoty bwdMap h_alpha x hx
  rw [hsy]
  -- The toList keys are distinct, so G1 (find?_renameMap_of_mem) applies to (y, x) ∈ toList.
  have hmem : (y, x) ∈ bwdMap.toList :=
    Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr hby
  have hnd : (bwdMap.toList.map Prod.fst).Nodup := by
    have hpw := Std.HashMap.distinct_keys_toList (m := bwdMap)
    rw [List.Nodup, List.pairwise_map]
    exact hpw.imp (fun {a b} h => by simp only [beq_eq_false_iff_ne, ne_eq] at h; exact h)
  have hfind := find?_renameMap_of_mem bwdMap.toList hnd y x hmem
  -- subst renameSubst (ftvar y) reads renameSubst.find? y; relate it to hfind.
  rw [LMonoTy.subst_unfold]
  simp only
  by_cases hyx : y = x
  · -- fixed point: y absent from renameSubst, so subst leaves ftvar y = ftvar x
    rw [if_pos hyx] at hfind
    rw [Maps.find?, hfind]; simp only [Maps.find?]; subst_vars; rfl
  · rw [if_neg hyx] at hfind
    rw [Maps.find?, hfind]

/-- The `alphaEquivMap`-derived renameSubst inverts the unification substitution.
    `subst renameSubst (subst S t) = t` whenever `alphaEquivMap monoty (subst S monoty) = some bwdMap`,
    renameSubst is derived from bwdMap, and every free variable of `t` is a free variable of
    `monoty` (so bwdMap covers every renaming `t` needs). At the call site `t` is the declared
    output monotype, a component of `monoty.destructArrow`, so its free vars are a subset. -/
theorem alphaEquivMap_renameSubst_inverse (monoty t : LMonoTy) (S : Subst)
    (bwdMap : Std.HashMap TyIdentifier TyIdentifier)
    (h_alpha : LMonoTy.alphaEquivMap monoty (LMonoTy.subst S monoty) = some bwdMap)
    (h_sub : ∀ v, v ∈ LMonoTy.freeVars t → v ∈ LMonoTy.freeVars monoty) :
    let renameSubst : Subst :=
      [bwdMap.toList.filterMap (fun (k, v) => if k == v then none else some (k, .ftvar v))]
    LMonoTy.subst renameSubst (LMonoTy.subst S t) = t := by
  intro renameSubst
  -- Induct on `t`; carry the freeVars-subset side condition through the recursion.
  revert h_sub
  induction t with
  | ftvar x =>
    intro h_sub
    have hx : x ∈ LMonoTy.freeVars monoty :=
      h_sub x (by simp only [LMonoTy.freeVars, List.mem_singleton])
    exact alphaEquivMap_renameSubst_inverse_ftvar monoty S bwdMap h_alpha x hx
  | bitvec n =>
    intro _
    rw [LMonoTy.subst_bitvec, LMonoTy.subst_bitvec]
  | tcons name args ih =>
    intro h_sub
    -- Use the `subst_unfold` view so both substs expose `args.map (subst _)`.
    rw [LMonoTy.subst_unfold S (.tcons name args)]
    rw [LMonoTy.subst_unfold renameSubst (.tcons name (args.map (LMonoTy.subst S)))]
    simp only [List.map_map]
    congr 1
    -- Reduce to: each element `a ∈ args` is fixed by `subst renameSubst ∘ subst S`.
    have h_args : ∀ a ∈ args,
        (LMonoTy.subst renameSubst ∘ LMonoTy.subst S) a = a := by
      intro a ha
      simp only [Function.comp_apply]
      refine ih a ha (fun v hv => h_sub v ?_)
      simp only [LMonoTy.freeVars]
      exact LMonoTys.freeVars_mem_subset ha hv
    rw [List.map_congr_left h_args]
    simp only [List.map_id_fun', id_eq]

/-- When unify solves `(output_mty, bodyty)` and alphaEquivMap provides a bwdMap,
    the composed substitution `subst userSubst (subst renameSubst (subst S bodyty))`
    equals `subst userSubst output_mty`. This captures the full type equality chain
    needed for bodyTyped. The `h_sub` precondition (output free vars ⊆ monoty free vars)
    is what lets `alphaEquivMap_renameSubst_inverse` apply to `output_mty`; it holds at the
    call site because `output_mty` is a component of `monoty.destructArrow`. -/
theorem typeCheck_body_type_eq
    (monoty output_mty bodyty : LMonoTy)
    (S : Subst)
    (bwdMap : Std.HashMap TyIdentifier TyIdentifier)
    (userSubst : Subst)
    (h_unify_eq : LMonoTy.subst S output_mty = LMonoTy.subst S bodyty)
    (h_alpha : LMonoTy.alphaEquivMap monoty (LMonoTy.subst S monoty) = some bwdMap)
    (h_sub : ∀ v, v ∈ LMonoTy.freeVars output_mty → v ∈ LMonoTy.freeVars monoty) :
    let renameSubst : Subst :=
      [bwdMap.toList.filterMap (fun (k, v) => if k == v then none else some (k, .ftvar v))]
    LMonoTy.subst userSubst (LMonoTy.subst renameSubst (LMonoTy.subst S bodyty)) =
      LMonoTy.subst userSubst output_mty := by
  intro renameSubst
  have h_inv := alphaEquivMap_renameSubst_inverse monoty output_mty S bwdMap h_alpha h_sub
  simp only at h_inv
  rw [← h_unify_eq, h_inv]

/-- The full body-typing chain: starting from a resolved, `AbsWF`, well-typed body,
    apply the three substitutions (`unify`, `rename`, `user`) and land at the
    declared output type. Abstracts plan steps 1–7; used identically in all measure
    branches of `bodyTyped`. -/
theorem bodyTyped_chain {T : LExprParams} [DecidableEq T.IDMeta]
    (et₀ : LExprT T.mono) (S userSubst : Subst)
    (monoty output_mty : LMonoTy)
    (bwdMap : Std.HashMap TyIdentifier TyIdentifier)
    (h_wf : LExprT.AbsWF et₀)
    (h_typed : LExpr.HasTypeA [] et₀.unresolved (et₀.toLMonoTy))
    (h_unify_eq : LMonoTy.subst S output_mty = LMonoTy.subst S et₀.toLMonoTy)
    (h_alpha : LMonoTy.alphaEquivMap monoty (LMonoTy.subst S monoty) = some bwdMap)
    (h_sub : ∀ v, v ∈ LMonoTy.freeVars output_mty → v ∈ LMonoTy.freeVars monoty) :
    LExpr.HasTypeA []
      (applySubstT
        (applySubstT
          (applySubstT et₀ S)
          [bwdMap.toList.filterMap (fun x => if x.1 == x.2 then none else some (x.1, .ftvar x.2))])
        userSubst).unresolved
      (LMonoTy.subst userSubst output_mty) := by
  let renameSubst : Subst := [bwdMap.toList.filterMap (fun x => if x.1 == x.2 then none else some (x.1, LMonoTy.ftvar x.2))]
  show LExpr.HasTypeA []
      (applySubstT (applySubstT (applySubstT et₀ S) renameSubst) userSubst).unresolved
      (LMonoTy.subst userSubst output_mty)
  -- Step 1→2: apply S
  have h1 := applySubstT_unresolved_HasTypeA et₀ S [] h_wf h_typed
  rw [List.map_nil] at h1
  -- Step 4: apply renameSubst
  have h_wf1 := applySubstT_AbsWF et₀ S h_wf
  have h2 := applySubstT_unresolved_HasTypeA (applySubstT et₀ S) renameSubst [] h_wf1 h1
  rw [List.map_nil] at h2
  -- Step 6: apply userSubst
  have h_wf2 := applySubstT_AbsWF (applySubstT et₀ S) renameSubst h_wf1
  have h3 := applySubstT_unresolved_HasTypeA
    (applySubstT (applySubstT et₀ S) renameSubst) userSubst [] h_wf2 h2
  rw [List.map_nil] at h3
  -- Rewrite the type: peel the three toLMonoTy substitutions, then use the
  -- alpha/unify type-equality.
  rw [applySubstT_toLMonoTy, applySubstT_toLMonoTy, applySubstT_toLMonoTy] at h3
  have h_eq := typeCheck_body_type_eq monoty output_mty et₀.toLMonoTy S bwdMap userSubst
    h_unify_eq h_alpha h_sub
  simp only at h_eq
  rw [h_eq] at h3
  exact h3

/-- The internal typing environment the body typechecker builds — push an empty
    scope, then insert the monomorphic input signature — is well-formed and
    aliases-resolved, given that each inserted input monotype is a component of
    `monoty.destructArrow` (which holds by construction: the inputs are
    `func.inputs.keys.zip (take n monoty.destructArrow)`). This packages the
    internal-env preservation chain so the three measure branches of `bodyTyped`
    can invoke `resolve_HasTypeA`/`resolve_AbsWF`. -/
theorem typeCheck_internalEnv_wf
    (type : LTy) (C : LContext CoreLParams) (Env : TEnv Unit)
    (monoty : LMonoTy) (Env_inst : TEnv Unit)
    (pairs : List (CoreLParams.Identifier × LMonoTy))
    (h_inst : LTy.instantiateWithCheck type C Env = .ok (monoty, Env_inst))
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_resolved : TContext.AliasesResolved Env.context)
    (h_sig : ∀ p ∈ pairs, p.2 ∈ monoty.destructArrow) :
    TEnvWF (T := CoreLParams) (Env_inst.pushEmptyContext.addInNewestContext (T := CoreLParams)
        (pairs.map (fun p => (p.1, LTy.forAll [] p.2))))
    ∧ TContext.AliasesResolved (Env_inst.pushEmptyContext.addInNewestContext (T := CoreLParams)
        (pairs.map (fun p => (p.1, LTy.forAll [] p.2)))).context := by
  have h_envwf_inst : TEnvWF (T := CoreLParams) Env_inst :=
    LTy_instantiateWithCheck_TEnvWF (T := CoreLParams) type C Env monoty Env_inst h_inst h_wf
  have h_ctx_inst : Env_inst.context = Env.context :=
    LTy_instantiateWithCheck_context (T := CoreLParams) type C Env monoty Env_inst h_inst
  have h_resolved_inst : TContext.AliasesResolved Env_inst.context := by
    rw [h_ctx_inst]; exact h_resolved
  have h_fresh : ∀ p ∈ pairs,
      ∀ v, v ∈ LMonoTy.freeVars p.2 →
        ∀ n, n ≥ Env_inst.genEnv.genState.tyGen → v ≠ TState.tyPrefix ++ toString n := by
    intro p hp v hv n hn
    exact instantiateWithCheck_destructArrow_mem_fresh (T := CoreLParams) type C Env monoty Env_inst
      h_inst p.2 (h_sig p hp) v hv n hn
  have h_envwf_push : TEnvWF (T := CoreLParams) Env_inst.pushEmptyContext :=
    TEnvWF.of_pushEmptyContext (T := CoreLParams) Env_inst h_envwf_inst
  have h_gen_push : Env_inst.pushEmptyContext.genEnv.genState = Env_inst.genEnv.genState := rfl
  have h_fresh_push : ∀ p ∈ pairs,
      ∀ v, v ∈ LMonoTy.freeVars p.2 →
        ∀ n, n ≥ Env_inst.pushEmptyContext.genEnv.genState.tyGen →
          v ≠ TState.tyPrefix ++ toString n := by
    rw [h_gen_push]; exact h_fresh
  refine ⟨?_, ?_⟩
  · exact TEnvWF.of_addInNewestContext_mono (T := CoreLParams) Env_inst.pushEmptyContext
      pairs h_envwf_push h_fresh_push
  · exact TContext.AliasesResolved.of_addInNewestContext (T := CoreLParams) _ _
      (TContext.AliasesResolved.of_pushEmptyContext (T := CoreLParams) Env_inst h_resolved_inst)

/-- WF-only variant of `typeCheck_internalEnv_wf`: the internal body-resolution
    environment is well-formed, needing only `TEnvWF Env` (no `AliasesResolved`).
    This is what `resolve_HasType_core` requires, and unlike the bundled helper it
    is available in `_instantiated`, which only carries `checkContextTypesClosed`. -/
theorem typeCheck_internalEnv_TEnvWF
    (type : LTy) (C : LContext CoreLParams) (Env : TEnv Unit)
    (monoty : LMonoTy) (Env_inst : TEnv Unit)
    (pairs : List (CoreLParams.Identifier × LMonoTy))
    (h_inst : LTy.instantiateWithCheck type C Env = .ok (monoty, Env_inst))
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_sig : ∀ p ∈ pairs, p.2 ∈ monoty.destructArrow) :
    TEnvWF (T := CoreLParams) (Env_inst.pushEmptyContext.addInNewestContext (T := CoreLParams)
        (pairs.map (fun p => (p.1, LTy.forAll [] p.2)))) := by
  have h_envwf_inst : TEnvWF (T := CoreLParams) Env_inst :=
    LTy_instantiateWithCheck_TEnvWF (T := CoreLParams) type C Env monoty Env_inst h_inst h_wf
  have h_fresh : ∀ p ∈ pairs,
      ∀ v, v ∈ LMonoTy.freeVars p.2 →
        ∀ n, n ≥ Env_inst.genEnv.genState.tyGen → v ≠ TState.tyPrefix ++ toString n := by
    intro p hp v hv n hn
    exact instantiateWithCheck_destructArrow_mem_fresh (T := CoreLParams) type C Env monoty Env_inst
      h_inst p.2 (h_sig p hp) v hv n hn
  have h_envwf_push : TEnvWF (T := CoreLParams) Env_inst.pushEmptyContext :=
    TEnvWF.of_pushEmptyContext (T := CoreLParams) Env_inst h_envwf_inst
  have h_gen_push : Env_inst.pushEmptyContext.genEnv.genState = Env_inst.genEnv.genState := rfl
  have h_fresh_push : ∀ p ∈ pairs,
      ∀ v, v ∈ LMonoTy.freeVars p.2 →
        ∀ n, n ≥ Env_inst.pushEmptyContext.genEnv.genState.tyGen →
          v ≠ TState.tyPrefix ++ toString n := by
    rw [h_gen_push]; exact h_fresh
  exact TEnvWF.of_addInNewestContext_mono (T := CoreLParams) Env_inst.pushEmptyContext
    pairs h_envwf_push h_fresh_push

/-! ### Per-field helper lemmas for annotated soundness -/

/-- The first projection of a zipped list is a sublist of the first list. -/
theorem List.map_fst_zip_sublist {α β : Type} (a : List α) (b : List β) :
    ((a.zip b).map Prod.fst).Sublist a := by
  induction a generalizing b with
  | nil => simp
  | cons x xs ih =>
    cases b with
    | nil => simp
    | cons y ys =>
      simp only [List.zip_cons_cons, List.map_cons]
      exact (ih ys).cons₂ x

/-- The second projection of a zipped list is a sublist of the second list. -/
theorem List.map_snd_zip_sublist {α β : Type} (a : List α) (b : List β) :
    ((a.zip b).map Prod.snd).Sublist b := by
  induction a generalizing b with
  | nil => simp
  | cons x xs ih =>
    cases b with
    | nil => simp
    | cons y ys =>
      simp only [List.zip_cons_cons, List.map_cons]
      exact (ih ys).cons₂ y

theorem Function.typeCheck_inputsNodup (C : LContext CoreLParams) (Env : TEnv Unit)
    (func func' : Function) (Env' : TEnv Unit)
    (h : Function.typeCheck C Env func = .ok (func', Env')) :
    func'.inputs.keys.Nodup := by
  have h_nodup : func.inputs.keys.Nodup := Function.typeCheck_inputs_nodup C Env func func' Env' h
  simp only [Function.typeCheck, bind, Except.bind] at h
  elim_err h
  rename_i type h_type
  elim_err h
  rename_i h_undecl
  elim_err h
  elim_err h
  rename_i v_inst h_inst
  -- In every `.ok` branch, `func'.inputs = map (fun x => (x.fst, _)) (func.inputs.keys.zip _)`,
  -- so its keys are a sublist of `func.inputs.keys`, which is `Nodup`.
  have h_close : ∀ (g : CoreLParams.Identifier × LMonoTy → CoreLParams.Identifier × LMonoTy)
      (mtys : List LMonoTy) (hg : ∀ p, (g p).fst = p.fst),
      (ListMap.keys ((func.inputs.keys.zip mtys).map g)).Nodup := by
    intro g mtys hg
    rw [ListMap.keys_eq_map_fst, List.map_map]
    have h_eq : (Prod.fst ∘ g) = (fun p : CoreLParams.Identifier × LMonoTy => p.fst) := by
      funext p; simp [Function.comp, hg p]
    rw [h_eq]
    exact (List.map_fst_zip_sublist func.inputs.keys mtys).nodup h_nodup
  split at h
  · -- body = none
    split at h
    · simp at h
    · cases h
      exact h_close _ _ (fun _ => rfl)
  · -- body = some
    rename_i body h_body_some
    elim_err h
    rename_i h_stray
    elim_err h
    elim_err h
    rename_i v_resolve h_resolve
    elim_err h
    rename_i v_unify h_unify
    split at h <;> try contradiction
    rename_i alphaMap h_alphaMap
    elim_err h
    rename_i bwdMap h_alpha
    elim_err h
    elim_err h
    split at h
    · -- measure = some
      split at h
      · -- fvar
        elim_err h; cases h
        exact h_close _ _ (fun _ => rfl)
      · -- non-fvar
        elim_err h
        rename_i v_measure h_measure_resolve
        elim_err h
        rename_i h_measure_ty
        elim_err h; cases h
        exact h_close _ _ (fun _ => rfl)
    · -- measure = none
      elim_err h; cases h
      exact h_close _ _ (fun _ => rfl)

theorem Function.typeCheck_typeArgsNodup (C : LContext CoreLParams) (Env : TEnv Unit)
    (func func' : Function) (Env' : TEnv Unit)
    (h : Function.typeCheck C Env func = .ok (func', Env')) :
    func'.typeArgs.Nodup := by
  have h_nodup : func.typeArgs.Nodup := by
    simp only [Function.typeCheck, bind, Except.bind] at h
    split at h <;> try contradiction
    rename_i type h_type
    exact LFunc.type_typeArgs_nodup func type h_type
  simp only [Function.typeCheck, bind, Except.bind] at h
  elim_err h
  rename_i type h_type
  elim_err h
  rename_i h_undecl
  elim_err h
  elim_err h
  rename_i v_inst h_inst
  -- In every `.ok` branch, `func'.typeArgs = map Prod.snd (_ .zip func.typeArgs)`,
  -- a sublist of `func.typeArgs`, which is `Nodup`.
  have h_close : ∀ (vs : List TyIdentifier),
      (List.map (fun x => x.snd) (vs.zip func.typeArgs)).Nodup := by
    intro vs
    exact (List.map_snd_zip_sublist vs func.typeArgs).nodup h_nodup
  split at h
  · -- body = none
    split at h
    · simp at h
    · cases h
      exact h_close _
  · -- body = some
    rename_i body h_body_some
    elim_err h
    rename_i h_stray
    elim_err h
    elim_err h
    rename_i v_resolve h_resolve
    elim_err h
    rename_i v_unify h_unify
    split at h <;> try contradiction
    rename_i alphaMap h_alphaMap
    elim_err h
    rename_i bwdMap h_alpha
    elim_err h
    elim_err h
    split at h
    · -- measure = some
      split at h
      · elim_err h; cases h
        exact h_close _
      · elim_err h
        rename_i v_measure h_measure_resolve
        elim_err h
        rename_i h_measure_ty
        elim_err h; cases h
        exact h_close _
    · -- measure = none
      elim_err h; cases h
      exact h_close _

/-- **D1 (rename-image).** Substituting the renaming `userSubst = [ids.zip (map ftvar tgts)]`
    into a monotype `W` whose free vars are all keys (`⊆ ids`) yields a monotype whose free
    vars are all renamed targets (`∈ (ids.zip tgts).map Prod.snd`). When `ids.length ≤
    tgts.length` (coverage), the keys are exactly `ids` and the targets are exactly
    `func'.typeArgs`. Reduces to the existing `LMonoTy.freeVars_subst_closed` with the fresh
    set instantiated to `tgts.take ids.length`. -/
private theorem freeVars_rename_subset
    (ids tgts : List TyIdentifier) (W : LMonoTy)
    (h_cov : ids.length ≤ tgts.length)
    (h_closed : ∀ v, v ∈ LMonoTy.freeVars W → v ∈ ids) :
    ∀ v, v ∈ LMonoTy.freeVars
        (LMonoTy.subst [(ids.zip tgts).map (fun x => (x.1, LMonoTy.ftvar x.2))] W) →
      v ∈ (ids.zip tgts).map Prod.snd := by
  -- Projecting the zip's snd component yields exactly the (truncated) target list.
  have e1 : ∀ (I T : List TyIdentifier), (I.zip T).map Prod.snd = T.take I.length := by
    intro I
    induction I with
    | nil => simp
    | cons a rest ih =>
      intro T
      cases T with
      | nil => simp
      | cons t trest =>
        simp only [List.zip_cons_cons, List.map_cons, List.length_cons, List.take_succ_cons, ih]
  -- The renaming substitution map equals the `zip ids (map ftvar …)` form `freeVars_subst_closed`
  -- expects, with the fresh set being `tgts.take ids.length`.
  have e2 : ∀ (I T : List TyIdentifier),
      (I.zip T).map (fun x => (x.1, LMonoTy.ftvar x.2)) =
        List.zip I (List.map LMonoTy.ftvar (T.take I.length)) := by
    intro I
    induction I with
    | nil => simp
    | cons a rest ih =>
      intro T
      cases T with
      | nil => simp
      | cons t trest =>
        simp only [List.zip_cons_cons, List.map_cons, List.length_cons, List.take_succ_cons, ih]
  intro v hv
  rw [e1 ids tgts]
  have h_len : (tgts.take ids.length).length = ids.length := by
    rw [List.length_take]; omega
  rw [e2 ids tgts] at hv
  -- `freeVars_subst_closed` requires a non-empty substitution scope. When `ids = []`,
  -- `h_closed` forces `W.freeVars = []`, so the conclusion is vacuous.
  cases ids with
  | nil =>
    simp only [List.length_nil, List.take_zero, List.zip_nil_left, List.map_nil] at hv
    rw [LMonoTy.subst_emptyS (by simp [Subst.hasEmptyScopes, Map.isEmpty])] at hv
    exact (h_closed v hv)
  | cons a rest =>
    have hSNE : Subst.hasEmptyScopes
        [List.zip (a :: rest) (List.map LMonoTy.ftvar (tgts.take (a :: rest).length))] = false := by
      cases h_tgts : tgts.take (a :: rest).length with
      | nil => rw [h_tgts] at h_len; simp at h_len
      | cons f frest => rfl
    exact LMonoTy.freeVars_subst_closed (a :: rest) (tgts.take (a :: rest).length) h_len W
      h_closed hSNE v hv

/-- **D2 (coverage).** The distinct free vars of an `LTy.instantiateWithCheck` output number
    at most the scheme's bound variables. The output's free vars are all freshly generated
    (`freeVars_subst_closed` + `resolveAliases` doesn't grow freeVars), and the fresh set is
    nodup with `length = boundVars.length`. -/
private theorem instantiateWithCheck_freeVars_eraseDups_length_le
    (type : LTy) (C : LContext CoreLParams) (Env : TEnv Unit)
    (monoty : LMonoTy) (Env' : TEnv Unit)
    (h : LTy.instantiateWithCheck type C Env = .ok (monoty, Env'))
    (h_closed : LTy.freeVars type = [])
    (h_aw : TContext.AliasesWF Env.context) :
    monoty.freeVars.eraseDups.length ≤ (LTy.boundVars type).length := by
  rcases type with ⟨xs, body⟩
  simp only [LTy.boundVars]
  -- The scheme is closed: every free var of the body is a bound var.
  have h_sub : ∀ v, v ∈ LMonoTy.freeVars body → v ∈ xs := by
    simp only [LTy.freeVars] at h_closed
    intro v hv
    rw [List.removeAll, List.filter_eq_nil_iff] at h_closed
    have hf := h_closed v hv
    simp_all
  -- Key: the instantiate-output free vars are covered by a fresh set whose length is `xs.length`.
  have h_fresh_cover : ∃ freshtvs : List TyIdentifier,
      freshtvs.length = xs.length ∧ ∀ v, v ∈ LMonoTy.freeVars monoty → v ∈ freshtvs := by
    simp only [LTy.instantiateWithCheck, Bind.bind, Except.bind] at h
    elim_err h
    rename_i v1 h_ra
    obtain ⟨mty_ra, Env_ra⟩ := v1
    elim_errs h
    cases h
    simp only [LTy.resolveAliases, Bind.bind, Except.bind] at h_ra
    elim_err h_ra
    rename_i v2 h_inst
    obtain ⟨mty_inst, genEnv1⟩ := v2
    dsimp only at h_ra
    have h_ctx_inst : genEnv1.context = Env.genEnv.context :=
      LTy.instantiate_context (LTy.forAll xs body) Env.genEnv mty_inst genEnv1 h_inst
    have h_aw_ra : TContext.AliasesWF
        ({ genEnv := genEnv1, stateSubstInfo := Env.stateSubstInfo } : TEnv Unit).context := by
      simp only [TEnv.context]; rw [h_ctx_inst]; exact h_aw
    have h_ra_sub : ∀ v, v ∈ mty_ra.freeVars → v ∈ mty_inst.freeVars :=
      LMonoTy_resolveAliases_freeVars_subset (T := CoreLParams) mty_inst
        { genEnv := genEnv1, stateSubstInfo := Env.stateSubstInfo } mty_ra Env_ra h_ra h_aw_ra
    have h_inst_cover : ∃ freshtvs : List TyIdentifier,
        freshtvs.length = xs.length ∧ ∀ v, v ∈ mty_inst.freeVars → v ∈ freshtvs := by
      cases xs with
      | nil =>
        refine ⟨[], rfl, ?_⟩
        simp only [LTy.instantiate] at h_inst
        cases h_inst
        intro v hv
        exact h_sub v hv
      | cons a rest =>
        simp only [LTy.instantiate, Bind.bind, Except.bind] at h_inst
        elim_err h_inst
        rename_i v1 h_gen
        obtain ⟨freshtvs, genEnv2⟩ := v1
        simp only [Except.ok.injEq, Prod.mk.injEq] at h_inst
        obtain ⟨h_mty, h_env⟩ := h_inst
        have h_flen : freshtvs.length = (a :: rest).length :=
          TGenEnv.genTyVars_length (a :: rest).length Env.genEnv freshtvs genEnv2 h_gen
        refine ⟨freshtvs, h_flen, ?_⟩
        rw [← h_mty]
        intro v hv
        have hSNE : Subst.hasEmptyScopes
            [List.zip (a :: rest) (List.map LMonoTy.ftvar freshtvs)] = false := by
          cases freshtvs with
          | nil => simp at h_flen
          | cons f frest => rfl
        exact LMonoTy.freeVars_subst_closed (a :: rest) freshtvs h_flen body h_sub hSNE v hv
    obtain ⟨freshtvs, h_len, h_cover_inst⟩ := h_inst_cover
    exact ⟨freshtvs, h_len, fun v hv => h_cover_inst v (h_ra_sub v hv)⟩
  obtain ⟨freshtvs, h_len, h_cover⟩ := h_fresh_cover
  -- `eraseDups` is nodup and ⊆ freshtvs, so its length ≤ freshtvs.length = xs.length.
  have h_nodup : monoty.freeVars.eraseDups.Nodup := eraseDups_Nodup _
  have h_sub_fresh : monoty.freeVars.eraseDups ⊆ freshtvs := by
    intro v hv
    exact h_cover v (List.mem_eraseDups.mp hv)
  calc monoty.freeVars.eraseDups.length
      ≤ freshtvs.length := List.subset_nodup_length h_nodup h_sub_fresh
    _ = xs.length := h_len

theorem Function.typeCheck_noUndeclaredVars (C : LContext CoreLParams) (Env : TEnv Unit)
    (func func' : Function) (Env' : TEnv Unit)
    (h : Function.typeCheck C Env func = .ok (func', Env'))
    (h_wf : TEnvWF (T := CoreLParams) Env) :
    ∀ v, v ∈ LMonoTy.freeVars (LMonoTy.mkArrow' func'.output func'.inputs.values) →
      v ∈ func'.typeArgs := by
  simp only [Function.typeCheck, bind, Except.bind] at h
  elim_err h
  rename_i type h_type
  elim_err h
  rename_i h_undecl
  elim_err h
  elim_err h
  rename_i v_inst h_inst
  -- Coverage: distinct free vars of `monoty` number at most `type.boundVars` = `func.typeArgs`.
  have h_aw : TContext.AliasesWF Env.context := h_wf.aliasesWF
  have h_bv : LTy.boundVars type = func.typeArgs :=
    LFunc.type_boundVars_eq_typeArgs (T := CoreLParams) func type h_type
  have h_closed : LTy.freeVars type = [] := by
    simp only [bne_iff_ne, ne_eq, Decidable.not_not] at h_undecl
    exact h_undecl
  have h_cov : v_inst.fst.freeVars.eraseDups.length ≤ func.typeArgs.length := by
    rw [← h_bv]
    exact instantiateWithCheck_freeVars_eraseDups_length_le type C Env v_inst.fst v_inst.snd
      (by rw [Prod.eta]; exact h_inst) h_closed h_aw
  -- Every free var of `monoty` is a key (`∈ ids`) of `userSubst`.
  have h_in_ids : ∀ v, v ∈ v_inst.fst.freeVars → v ∈ v_inst.fst.freeVars.eraseDups :=
    fun v hv => List.mem_eraseDups.mpr hv
  -- The shared "closing" fact: any constructed `func'` of the branch shape has the property.
  -- `W` is the pre-rename signature monotype; its free vars are all in `monoty.freeVars`.
  -- `h_close` works on the *whole* `subst userSubst (mkArrow' RO ins)` term (RO = reconstructed
  -- output). Its free vars are all in `monoty.freeVars` (inputs are destructArrow slices, RO is
  -- the reconstructed output), so D1 applies.
  have h_close : ∀ v, v ∈ LMonoTy.freeVars
      (LMonoTy.subst
          [(v_inst.fst.freeVars.eraseDups.zip func.typeArgs).map (fun x => (x.1, LMonoTy.ftvar x.2))]
        (LMonoTy.mkArrow'
          (((List.drop func.inputs.keys.length v_inst.fst.destructArrow).getLast?.getD
              (List.getLast v_inst.fst.destructArrow (LMonoTy.destructArrow_non_empty v_inst.fst))).mkArrow'
            (List.drop func.inputs.keys.length v_inst.fst.destructArrow).dropLast)
          ((func.inputs.keys.zip (List.take func.inputs.keys.length v_inst.fst.destructArrow)).map
            (fun x => x.2)))) →
      v ∈ (v_inst.fst.freeVars.eraseDups.zip func.typeArgs).map Prod.snd := by
    intro v hv
    refine freeVars_rename_subset v_inst.fst.freeVars.eraseDups func.typeArgs _ h_cov ?_ v hv
    intro w hw
    apply h_in_ids
    rw [LMonoTy.freeVars_mkArrow', List.mem_append] at hw
    cases hw with
    | inl h_args =>
      -- w is a free var of some input monotype (a `take` of `destructArrow`).
      obtain ⟨x, hx_mem, hx_w⟩ := LMonoTys.freeVars_exists h_args
      simp only [List.mem_map] at hx_mem
      obtain ⟨p, hp_mem, hp_eq⟩ := hx_mem
      have h_p2_destr : p.2 ∈ v_inst.fst.destructArrow :=
        List.mem_of_mem_take (List.of_mem_zip hp_mem).2
      rw [← hp_eq] at hx_w
      exact LMonoTy.mem_destructArrow_freeVars_subset v_inst.fst p.2 h_p2_destr hx_w
    | inr h_ret =>
      -- `h_ret : w ∈ freeVars RO`; `RO` is exactly the reconstructed output.
      exact LMonoTy.freeVars_reconstructedOutput_subset v_inst.fst func.inputs.keys.length w h_ret
  -- `mkArrow' func'.output func'.inputs.values = subst userSubst (mkArrow' RO ins)` by
  -- `subst_mkArrow'` (output) and `ListMap.values`/`map_map` (inputs); `h_close` then closes.
  have h_finish : ∀ v, v ∈ LMonoTy.freeVars
      ((LMonoTy.subst
          [(v_inst.fst.freeVars.eraseDups.zip func.typeArgs).map (fun x => (x.1, LMonoTy.ftvar x.2))]
          (((List.drop func.inputs.keys.length v_inst.fst.destructArrow).getLast?.getD
              (List.getLast v_inst.fst.destructArrow (LMonoTy.destructArrow_non_empty v_inst.fst))).mkArrow'
            (List.drop func.inputs.keys.length v_inst.fst.destructArrow).dropLast)).mkArrow'
        ((func.inputs.keys.zip (List.take func.inputs.keys.length v_inst.fst.destructArrow)).map
          (fun x => LMonoTy.subst
            [(v_inst.fst.freeVars.eraseDups.zip func.typeArgs).map (fun x => (x.1, LMonoTy.ftvar x.2))]
            x.2))) →
      v ∈ (v_inst.fst.freeVars.eraseDups.zip func.typeArgs).map Prod.snd := by
    intro v hv
    apply h_close v
    rw [subst_mkArrow', List.map_map]
    exact hv
  split at h
  · -- body = none
    split at h
    · simp at h
    · cases h
      intro v hv
      rw [ListMap.values_eq_map_snd, List.map_map] at hv
      exact h_finish v hv
  · -- body = some
    rename_i body h_body_some
    elim_err h
    rename_i h_stray
    elim_err h
    elim_err h
    rename_i v_resolve h_resolve
    elim_err h
    rename_i v_unify h_unify
    split at h <;> try contradiction
    rename_i alphaMap h_alphaMap
    elim_err h
    rename_i bwdMap h_alpha
    elim_err h
    elim_err h
    split at h
    · split at h
      · elim_err h; cases h
        intro v hv
        rw [ListMap.values_eq_map_snd, List.map_map] at hv
        exact h_finish v hv
      · elim_err h
        rename_i v_measure h_measure_resolve
        elim_err h
        rename_i h_measure_ty
        elim_err h; cases h
        intro v hv
        rw [ListMap.values_eq_map_snd, List.map_map] at hv
        exact h_finish v hv
    · elim_err h; cases h
      intro v hv
      rw [ListMap.values_eq_map_snd, List.map_map] at hv
      exact h_finish v hv

theorem Function.typeCheck_bodyTyped_annotated (C : LContext CoreLParams) (Env : TEnv Unit)
    (func func' : Function) (Env' : TEnv Unit)
    (h : Function.typeCheck C Env func = .ok (func', Env'))
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions)
    (h_resolved : TContext.AliasesResolved Env.context) :
    ∀ body, func'.body = some body →
      LExpr.HasTypeA [] body (func'.output) := by
  simp only [Function.typeCheck, bind, Except.bind] at h
  elim_err h
  rename_i type h_type
  elim_err h
  rename_i h_undecl
  elim_err h
  elim_err h
  rename_i v_inst h_inst
  split at h
  · -- body = none: func'.body = func.body = none, so bodyTyped is vacuous
    rename_i h_body_none
    split at h
    · simp at h
    · cases h
      intro body h_eq
      simp_all
  · -- body = some
    rename_i body h_body_some
    elim_err h
    rename_i h_stray
    elim_err h
    elim_err h
    rename_i v_resolve h_resolve
    elim_err h
    rename_i v_unify h_unify
    -- alphaEquivMap + measure handling
    split at h <;> try contradiction
    · -- alphaEquivMap = some
      rename_i alphaMap h_alphaMap
      elim_err h
      rename_i bwdMap h_alpha
      -- The input pairs inserted into the internal env, and the reconstructed
      -- output monotype. Both are built from `v_inst.fst.destructArrow`.
      have h_pairs_sig : ∀ p ∈ func.inputs.keys.zip
          (List.take func.inputs.keys.length v_inst.fst.destructArrow),
          p.2 ∈ v_inst.fst.destructArrow := by
        intro p hp
        exact List.mem_of_mem_take (List.of_mem_zip hp).2
      -- Internal env WF + aliases-resolved, via the packaged helper.
      have h_internal := typeCheck_internalEnv_wf type C Env v_inst.fst v_inst.snd
        (func.inputs.keys.zip (List.take func.inputs.keys.length v_inst.fst.destructArrow))
        h_inst h_wf h_resolved h_pairs_sig
      obtain ⟨h_envwf_internal, h_resolved_internal⟩ := h_internal
      -- Body resolution facts on the internal env. The internal env in `h_resolve`
      -- is defeq to the one in `h_internal` (`inputMonoSignature` unfolds to the
      -- mapped pairs).
      have h_body_wf : LExprT.AbsWF v_resolve.fst :=
        resolve_AbsWF body v_resolve.fst C _ v_resolve.snd
          (by rw [Prod.eta]; exact h_resolve) h_envwf_internal h_fwf
      have h_body_typed : LExpr.HasTypeA [] v_resolve.fst.unresolved v_resolve.fst.toLMonoTy :=
        resolve_HasTypeA body v_resolve.fst C _ v_resolve.snd
          (by rw [Prod.eta]; exact h_resolve) h_envwf_internal h_fwf h_resolved_internal
      -- Unify soundness gives the type equality the chain needs.
      have h_unify' : Constraints.unify
          [(LMonoTy.mkArrow'
              ((List.drop func.inputs.keys.length v_inst.fst.destructArrow).getLast?.getD
                (List.getLast v_inst.fst.destructArrow (LMonoTy.destructArrow_non_empty v_inst.fst)))
              (List.drop func.inputs.keys.length v_inst.fst.destructArrow).dropLast,
            v_resolve.fst.toLMonoTy)] v_resolve.snd.stateSubstInfo = .ok v_unify := by
        cases hc : Constraints.unify
            [(LMonoTy.mkArrow'
                ((List.drop func.inputs.keys.length v_inst.fst.destructArrow).getLast?.getD
                  (List.getLast v_inst.fst.destructArrow (LMonoTy.destructArrow_non_empty v_inst.fst)))
                (List.drop func.inputs.keys.length v_inst.fst.destructArrow).dropLast,
              v_resolve.fst.toLMonoTy)] v_resolve.snd.stateSubstInfo with
        | error e => rw [hc] at h_unify; simp [Except.mapError] at h_unify
        | ok w => rw [hc] at h_unify; simp [Except.mapError] at h_unify; rw [h_unify]
      have h_unify_eq := Constraints.unify_sound _ _ _ h_unify' _ List.mem_cons_self
      -- The full body-typing chain.
      have h_m_eq : alphaMap = bwdMap := by cases h_alpha; rfl
      have h_chain := bodyTyped_chain v_resolve.fst v_unify.subst
        [(v_inst.fst.freeVars.eraseDups.zip func.typeArgs).map (fun x => (x.1, LMonoTy.ftvar x.2))]
        v_inst.fst _ bwdMap h_body_wf h_body_typed h_unify_eq
        (by rw [h_alphaMap, h_m_eq])
        (LMonoTy.freeVars_reconstructedOutput_subset v_inst.fst func.inputs.keys.length)
      -- measure cases: split on func.measure then on fvar/non-fvar.
      -- All three branches define the same body/output, so they all close via h_chain.
      elim_err h
      elim_err h
      split at h
      · -- measure = some
        split at h
        · -- fvar case
          elim_err h; cases h
          intro body' h_eq
          injection h_eq with h_eq'
          subst h_eq'
          exact h_chain
        · -- non-fvar case
          elim_err h
          rename_i v_measure h_measure_resolve
          elim_err h
          rename_i h_measure_ty
          elim_err h; cases h
          intro body' h_eq
          injection h_eq with h_eq'
          subst h_eq'
          exact h_chain
      · -- measure = none
        elim_err h; cases h
        intro body' h_eq
        injection h_eq with h_eq'
        subst h_eq'
        exact h_chain

theorem Function.typeCheck_measureTyped_annotated (C : LContext CoreLParams) (Env : TEnv Unit)
    (func func' : Function) (Env' : TEnv Unit)
    (h : Function.typeCheck C Env func = .ok (func', Env'))
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions)
    (h_resolved : TContext.AliasesResolved Env.context) :
    ∀ m, func'.measure = some m →
      (∀ mid x ann, m ≠ .fvar mid x ann) →
      LExpr.HasTypeA [] m .int := by
  simp only [Function.typeCheck, bind, Except.bind] at h
  elim_err h
  rename_i type h_type
  elim_err h
  rename_i h_undecl
  elim_err h
  elim_err h
  rename_i v_inst h_inst
  split at h
  · -- body = none: the typechecker now rejects a measure on a bodiless function,
    -- so on the success path `func.measure = none`, hence `func'.measure = none`
    -- and the obligation is vacuous.
    rename_i h_body_none
    split at h
    · simp at h
    · rename_i h_measure_none
      cases h
      intro m h_eq h_nonfvar
      rw [Option.not_isSome_iff_eq_none] at h_measure_none
      simp_all
  · -- body = some
    rename_i body h_body_some
    elim_err h
    rename_i h_stray
    elim_err h
    elim_err h
    rename_i v_resolve h_resolve
    elim_err h
    rename_i v_unify h_unify
    split at h <;> try contradiction
    · -- alphaEquivMap = some
      rename_i alphaMap h_alphaMap
      elim_err h
      rename_i bwdMap h_alpha
      -- Internal env WF + aliases-resolved, via the packaged helper.
      have h_pairs_sig : ∀ p ∈ func.inputs.keys.zip
          (List.take func.inputs.keys.length v_inst.fst.destructArrow),
          p.2 ∈ v_inst.fst.destructArrow := by
        intro p hp
        exact List.mem_of_mem_take (List.of_mem_zip hp).2
      have h_internal := typeCheck_internalEnv_wf type C Env v_inst.fst v_inst.snd
        (func.inputs.keys.zip (List.take func.inputs.keys.length v_inst.fst.destructArrow))
        h_inst h_wf h_resolved h_pairs_sig
      obtain ⟨h_envwf_internal, h_resolved_internal⟩ := h_internal
      -- Well-formedness and aliases-resolved of the body-resolve output env.
      have h_body_envwf : TEnvWF (T := CoreLParams) v_resolve.snd :=
        resolve_TEnvWF body v_resolve.fst C _ v_resolve.snd
          (by rw [Prod.eta]; exact h_resolve) h_envwf_internal h_fwf
      have h_body_props := resolve_properties body v_resolve.fst C _ v_resolve.snd
        (by rw [Prod.eta]; exact h_resolve) h_envwf_internal h_fwf h_resolved_internal
      -- The unify result is gen-fresh for the body env: discharge via
      -- `unify_preserves_SubstFreshForGen`.
      have h_unify' : Constraints.unify
          [(LMonoTy.mkArrow'
              ((List.drop func.inputs.keys.length v_inst.fst.destructArrow).getLast?.getD
                (List.getLast v_inst.fst.destructArrow (LMonoTy.destructArrow_non_empty v_inst.fst)))
              (List.drop func.inputs.keys.length v_inst.fst.destructArrow).dropLast,
            v_resolve.fst.toLMonoTy)] v_resolve.snd.stateSubstInfo = .ok v_unify := by
        cases hc : Constraints.unify
            [(LMonoTy.mkArrow'
                ((List.drop func.inputs.keys.length v_inst.fst.destructArrow).getLast?.getD
                  (List.getLast v_inst.fst.destructArrow (LMonoTy.destructArrow_non_empty v_inst.fst)))
                (List.drop func.inputs.keys.length v_inst.fst.destructArrow).dropLast,
              v_resolve.fst.toLMonoTy)] v_resolve.snd.stateSubstInfo with
        | error e => rw [hc] at h_unify; simp [Except.mapError] at h_unify
        | ok w => rw [hc] at h_unify; simp [Except.mapError] at h_unify; rw [h_unify]
      -- Constraint free vars are gen-fresh for the body env's gen state.
      have h_fresh_cs : ∀ v, v ∈ Constraints.freeVars
          [(LMonoTy.mkArrow'
              ((List.drop func.inputs.keys.length v_inst.fst.destructArrow).getLast?.getD
                (List.getLast v_inst.fst.destructArrow (LMonoTy.destructArrow_non_empty v_inst.fst)))
              (List.drop func.inputs.keys.length v_inst.fst.destructArrow).dropLast,
            v_resolve.fst.toLMonoTy)] →
          ∀ n, n ≥ v_resolve.snd.genEnv.genState.tyGen → v ≠ TState.tyPrefix ++ toString n := by
        intro v hv n hn
        simp only [Constraints.freeVars, Constraint.freeVars, List.append_nil,
          List.mem_append] at hv
        cases hv with
        | inl h_ret =>
          -- retty's free vars ⊆ freeVars v_inst.fst, fresh for Env_inst. The body
          -- env's gen counter is ≥ Env_inst's (push/addInNewest preserve it,
          -- resolve is monotone), so freshness carries up.
          have h_in_mono : v ∈ LMonoTy.freeVars v_inst.fst :=
            LMonoTy.freeVars_reconstructedOutput_subset v_inst.fst func.inputs.keys.length v h_ret
          have h_internal_gen :
              v_resolve.snd.genEnv.genState.tyGen ≥ v_inst.snd.genEnv.genState.tyGen := by
            have h_mono := h_body_props.1
            rw [show (v_inst.snd.pushEmptyContext.addInNewestContext
                (List.map (fun p => (p.fst, LTy.forAll [] p.snd))
                  (func.inputs.keys.zip
                    (List.take func.inputs.keys.length v_inst.fst.destructArrow)))).genEnv.genState
                = v_inst.snd.genEnv.genState from rfl] at h_mono
            exact h_mono
          exact LTy_instantiateWithCheck_freeVars_fresh type C Env v_inst.fst v_inst.snd
            h_inst v h_in_mono n (Nat.le_trans h_internal_gen hn)
        | inr h_body =>
          -- bodyty = v_resolve.fst.toLMonoTy, fresh for the body env by resolve_properties.
          exact h_body_props.2.2 v h_body n hn
      have h_sf : SubstFreshForGen v_unify v_resolve.snd.genEnv.genState :=
        unify_preserves_SubstFreshForGen h_unify' h_body_envwf.substFreshForGen h_fresh_cs
      -- WF + aliases-resolved of the measure env (post-updateSubst).
      have h_envwf_measure : TEnvWF (T := CoreLParams) (v_resolve.snd.updateSubst v_unify) :=
        TEnvWF.of_updateSubst h_body_envwf h_sf
      have h_resolved_measure :
          TContext.AliasesResolved (v_resolve.snd.updateSubst v_unify).context :=
        h_body_props.2.1
      -- Measure split.
      elim_err h
      elim_err h
      split at h
      · -- measure = some
        split at h
        · -- fvar case: func'.measure = func.measure = some (.fvar ...), which the
          -- non-fvar hypothesis forbids.
          rename_i fmeta fname fann h_measure_fvar
          elim_err h
          rename_i v_meas h_meas
          cases h
          intro m h_eq h_nonfvar
          dsimp only at h_eq
          rw [show (pure func.measure : Except Std.Format _) = Except.ok func.measure from rfl]
            at h_meas
          injection h_meas with h_meas'
          rw [← h_meas', h_measure_fvar] at h_eq
          injection h_eq with h_m
          exact absurd h_m.symm (h_nonfvar fmeta fname fann)
        · -- non-fvar case: measure resolved on the measure env, type int.
          rename_i h_not_fvar
          elim_err h
          rename_i v_measure h_measure_resolve
          elim_err h
          rename_i h_measure_ty
          elim_err h
          rename_i v_final h_final
          cases h
          intro m h_eq h_nonfvar
          dsimp only at h_eq
          -- `m` is the userSubst-renamed resolved measure.
          rw [show (pure (some (unresolved
              (applySubstT v_measure.fst
                [List.map (fun x => (x.fst, LMonoTy.ftvar x.snd))
                  (v_inst.fst.freeVars.eraseDups.zip func.typeArgs)]))) :
              Except Std.Format _) =
            Except.ok (some (unresolved
              (applySubstT v_measure.fst
                [List.map (fun x => (x.fst, LMonoTy.ftvar x.snd))
                  (v_inst.fst.freeVars.eraseDups.zip func.typeArgs)]))) from rfl] at h_final
          injection h_final with h_final'
          rw [← h_final'] at h_eq
          injection h_eq with h_meq
          subst h_meq
          -- Resolve the measure and apply userSubst.
          have h_measure_typed : LExpr.HasTypeA [] v_measure.fst.unresolved v_measure.fst.toLMonoTy :=
            resolve_HasTypeA _ v_measure.fst C _ v_measure.snd
              (by rw [Prod.eta]; exact h_measure_resolve) h_envwf_measure h_fwf h_resolved_measure
          have h_measure_abswf : LExprT.AbsWF v_measure.fst :=
            resolve_AbsWF _ v_measure.fst C _ v_measure.snd
              (by rw [Prod.eta]; exact h_measure_resolve) h_envwf_measure h_fwf
          have h_measure_int : v_measure.fst.toLMonoTy = .int := by
            simp only [bne_iff_ne, ne_eq, Decidable.not_not] at h_measure_ty
            exact h_measure_ty
          have h_applied := applySubstT_unresolved_HasTypeA v_measure.fst
            [(v_inst.fst.freeVars.eraseDups.zip func.typeArgs).map (fun x => (x.1, LMonoTy.ftvar x.2))]
            [] h_measure_abswf h_measure_typed
          rw [List.map_nil, applySubstT_toLMonoTy, h_measure_int] at h_applied
          rw [LMonoTy.int, LMonoTy.subst_tcons, LMonoTys.subst_nil] at h_applied
          exact h_applied
      · -- measure = none: func'.measure = none, vacuous.
        elim_err h
        rename_i v_none h_none
        cases h
        intro m h_eq h_nonfvar
        dsimp only at h_eq
        rw [show (pure none : Except Std.Format (Option (LExpr CoreLParams.mono))) = Except.ok none
          from rfl] at h_none
        injection h_none with h_none'
        rw [← h_none'] at h_eq
        exact absurd h_eq (by simp)

/-! ### Soundness Theorems -/

/--
Annotated soundness: if `Function.typeCheck` succeeds, the output function
satisfies `FuncHasTypeA`.
-/
theorem Function.typeCheck_annotated_sound (C : LContext CoreLParams) (Env : TEnv Unit)
    (func func' : Function) (Env' : TEnv Unit)
    (h : Function.typeCheck C Env func = .ok (func', Env'))
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions)
    (h_resolved : TContext.AliasesResolved Env.context) :
    ∀ Γ, FuncHasTypeA C Γ func' := by
  intro Γ
  exact {
    inputsNodup := Function.typeCheck_inputsNodup C Env func func' Env' h
    typeArgsNodup := Function.typeCheck_typeArgsNodup C Env func func' Env' h
    noUndeclaredVars := Function.typeCheck_noUndeclaredVars C Env func func' Env' h h_wf
    bodyTyped := Function.typeCheck_bodyTyped_annotated C Env func func' Env' h h_wf h_fwf h_resolved
    measureTyped := Function.typeCheck_measureTyped_annotated C Env func func' Env' h h_wf h_fwf h_resolved
  }

/-! ### Field lemmas for polymorphic soundness (about the *original* `func`)

These mirror the `func'` field lemmas above, but conclude about the original
`func`, as required by `FuncHasType C func`. -/

/-- `inputsNodup` for the original function: recoverable from `func.type` succeeding. -/
theorem Function.typeCheck_inputsNodup_orig (C : LContext CoreLParams) (Env : TEnv Unit)
    (func func' : Function) (Env' : TEnv Unit)
    (h : Function.typeCheck C Env func = .ok (func', Env')) :
    func.inputs.keys.Nodup :=
  Function.typeCheck_inputs_nodup C Env func func' Env' h

/-- `typeArgsNodup` for the original function: recoverable from `func.type` succeeding. -/
theorem Function.typeCheck_typeArgsNodup_orig (C : LContext CoreLParams) (Env : TEnv Unit)
    (func func' : Function) (Env' : TEnv Unit)
    (h : Function.typeCheck C Env func = .ok (func', Env')) :
    func.typeArgs.Nodup := by
  simp only [Function.typeCheck, bind, Except.bind] at h
  split at h <;> try contradiction
  rename_i type h_type
  exact LFunc.type_typeArgs_nodup func type h_type

mutual
/-- Reverse of `LMonoTy.freeVars_destructArrow_subset`: every free variable of a
    monotype is a free variable of its `destructArrow` decomposition. -/
theorem LMonoTy.freeVars_subset_destructArrow (mty : LMonoTy) :
    LMonoTy.freeVars mty ⊆ LMonoTys.freeVars (LMonoTy.destructArrow mty) := by
  unfold LMonoTy.destructArrow
  split
  · rename_i t1 trest
    simp only [LMonoTy.freeVars, LMonoTys.freeVars_of_cons]
    intro v hv
    rw [List.mem_append] at hv ⊢
    rcases hv with h | h
    · left; exact h
    · right; exact LMonoTys.freeVars_subset_destructArrow trest h
  · intro v hv
    simp only [LMonoTys.freeVars, List.append_nil]
    exact hv

/-- List-level reverse: free variables of `mtys` are free variables of its
    `destructArrow`. -/
theorem LMonoTys.freeVars_subset_destructArrow (mtys : LMonoTys) :
    LMonoTys.freeVars mtys ⊆ LMonoTys.freeVars (LMonoTys.destructArrow mtys) := by
  cases mtys with
  | nil => simp only [LMonoTys.destructArrow, List.Subset.refl]
  | cons ty rest =>
    simp only [LMonoTys.destructArrow, LMonoTys.freeVars_of_cons]
    intro v hv
    rw [LMonoTys.freeVars_append, List.mem_append] at *
    rcases hv with h | h
    · left; exact LMonoTy.freeVars_subset_destructArrow ty h
    · right; exact LMonoTys.freeVars_subset_destructArrow rest h
end

/-- `noUndeclaredVars` for the original function: all free type variables of the
    signature monotype are declared in `typeArgs`. -/
theorem Function.typeCheck_noUndeclaredVars_orig (C : LContext CoreLParams) (Env : TEnv Unit)
    (func func' : Function) (Env' : TEnv Unit)
    (h : Function.typeCheck C Env func = .ok (func', Env'))
    (h_wf : TEnvWF (T := CoreLParams) Env) :
    ∀ v, v ∈ LMonoTy.freeVars (LMonoTy.mkArrow' func.output func.inputs.values) →
      v ∈ func.typeArgs := by
  -- Recover `func.type = .ok type` and the undeclared-vars guard `LTy.freeVars type = []`.
  simp only [Function.typeCheck, bind, Except.bind] at h
  elim_err h
  rename_i type h_type
  elim_err h
  rename_i h_undecl
  have h_closed : LTy.freeVars type = [] := by
    simp only [bne_iff_ne, ne_eq, Decidable.not_not] at h_undecl
    exact h_undecl
  -- Decompose `func.type` to get `type = .forAll func.typeArgs sigBody` with an explicit `sigBody`
  -- determined by `func.inputs.values`.
  simp only [LFunc.type, bind, Except.bind, pure, Except.pure] at h_type
  split at h_type <;> try contradiction
  split at h_type <;> try contradiction
  -- A common closing step shared by both `inputs.values` cases: from `v ∈ sigBody.freeVars`,
  -- the guard `sigBody.freeVars.removeAll func.typeArgs = []` gives `v ∈ func.typeArgs`.
  have h_guard : ∀ sigBody : LMonoTy, type = LTy.forAll func.typeArgs sigBody →
      ∀ w, w ∈ LMonoTy.freeVars sigBody → w ∈ func.typeArgs := by
    intro sigBody h_ty w hw
    rw [h_ty, LTy.freeVars, List.removeAll, List.filter_eq_nil_iff] at h_closed
    have h_not := h_closed w hw
    simp only [List.elem_eq_mem, Bool.not_eq_eq_eq_not, Bool.not_true,
      decide_eq_false_iff_not, Decidable.not_not] at h_not
    exact h_not
  intro v hv
  rw [LMonoTy.freeVars_mkArrow', List.mem_append] at hv
  split at h_type
  · -- inputs.values = []: sigBody = func.output
    rename_i h_iv
    rw [Except.ok.injEq] at h_type
    refine h_guard func.output h_type.symm v ?_
    rcases hv with h | h
    · rw [h_iv, LMonoTys.freeVars] at h; exact absurd h (List.not_mem_nil)
    · exact h
  · -- inputs.values = ity :: irest: sigBody = mkArrow ity (irest ++ destructArrow output)
    rename_i ity irest h_iv
    rw [Except.ok.injEq] at h_type
    refine h_guard (ity.mkArrow (irest ++ LMonoTy.destructArrow func.output)) h_type.symm v ?_
    rw [LMonoTy.freeVars_mkArrow, LMonoTys.freeVars_append, List.mem_append, List.mem_append]
    rw [h_iv, LMonoTys.freeVars_of_cons, List.mem_append] at hv
    rcases hv with h | h
    · rcases h with h | h
      · left; exact h
      · right; left; exact h
    · right; right; exact LMonoTy.freeVars_subset_destructArrow func.output h

/-- **Shared per-component alias adapter.** Consumes the general structural inverse
    `LTy_instantiateWithCheck_inverse` (which gives a renaming `ρ` with
    `resolveAliases SIG = subst ρ v_inst.fst`, where `SIG = toMonoTypeUnsafe type` is the
    raw signature monotype) and produces the two *per-component* alias facts the
    `_instantiated` lemmas need, for BOTH `bodyTyped` and `measureTyped`:

    - **output:** `AliasEquiv aliases (subst ρ RO) func.output`, where `RO` is the
      reconstructed output (`mkArrow'` of the `drop n` destructArrow slice);
    - **inputs:** `AliasEquivList aliases (subst ρ (take n da)) func.inputs.values`.

    Both follow by peeling the `n = inputs.length` leading arrows of `SIG` (valid because
    no alias is named `"arrow"`, so `resolveAliases` distributes over the arrow spine),
    then `resolveAliases_aliasEquiv` on each raw component. The arrow-spine slicing is
    sound even for arrow-bodied aliases: inputs sit in atomic `t1` positions of
    `destructArrow`, so `take n` recovers exactly the `n` resolved inputs (verified). -/
theorem Function.typeCheck_inverse_components (C : LContext CoreLParams) (Env : TEnv Unit)
    (func : Function) (type : LTy) (v_inst : LMonoTy × TEnv Unit) (ρ : Subst) (Env_r : TEnv Unit)
    (h_type : LFunc.type func = .ok type)
    (h_ra : LMonoTy.resolveAliases (LTy.toMonoTypeUnsafe type) Env
      = .ok (LMonoTy.subst ρ v_inst.fst, Env_r))
    (h_aw : TContext.AliasesWF Env.context)
    (h_aliases_not_known : ∀ a ∈ Env.context.aliases, a.name ≠ "arrow") :
    -- output component
    (Lambda.AliasEquiv Env.context.aliases
      (LMonoTy.subst ρ
        (((List.drop func.inputs.keys.length v_inst.fst.destructArrow).getLast?.getD
            (List.getLast v_inst.fst.destructArrow (LMonoTy.destructArrow_non_empty v_inst.fst))).mkArrow'
          (List.drop func.inputs.keys.length v_inst.fst.destructArrow).dropLast))
      func.output) ∧
    -- input components
    (Lambda.AliasEquivList Env.context.aliases
      (LMonoTy.subst ρ <$> (List.take func.inputs.keys.length v_inst.fst.destructArrow))
      func.inputs.values) := by
  sorry

/-- **Instantiated body judgment.** The `typeCheck` pipeline resolves the body in
    an *instantiated* context `Γ_inst` (formals bound to fresh-tyvar, alias-resolved
    monotypes) at an instantiated output `output_inst`, and constructs a renaming
    `ρ` (fresh → user names). Applying `ρ` to the whole judgment recovers the
    user-facing context/output *up to type-alias equivalence* (the body is checked
    against alias-resolved types, but the spec uses the raw `func` signature). The
    top-level `typeCheck_bodyTyped` then chains three bridges: `HasType_TContext_subst`
    (rename `ρ`), `talias` (output alias), `HasType_context_aliasEquiv` (context alias). -/
theorem Function.typeCheck_bodyTyped_instantiated (C : LContext CoreLParams) (Env : TEnv Unit)
    (func func' : Function) (Env' : TEnv Unit)
    (h : Function.typeCheck C Env func = .ok (func', Env'))
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions)
    (h_ws : ∀ body, func.body = some body → WellScoped body Env.context)
    (h_fresh : Subst.allKeysFresh (T := CoreLParams) Env.stateSubstInfo.subst Env.context)
    (h_closed : LExpr.checkContextTypesClosed (T := CoreLParams) Env)
    -- TODO(preservation): every context alias name is a non-reserved (non-knownType) name.
    -- This is enforced by `TEnv.addTypeAlias` (LExprTypeEnv:1348, which rejects type decls whose
    -- name collides with `C.knownTypes`) but is not yet captured as a context invariant. It must
    -- be threaded as a property preserved by the type-decl / function typechecker and discharged at
    -- the call site. Needed to decompose the signature `AliasEquiv` along the arrow spine
    -- (`"arrow" ∈ C.knownTypes`, so no alias can restructure an arrow).
    (h_aliases_not_known :
      ∀ a ∈ Env.context.aliases, a.name ≠ "arrow")
    -- TODO(preservation): every free tyvar in an ambient binding is rigid (∈ C.rigidTypeVars).
    -- *Established* by ProcedureType.setupInputEnv: params are added using exactly the fresh
    -- vars registered as rigidTypeVars. *Preserved* by checkAnnotCompat (var-decls store the
    -- closed annotation and reject rigid-var refinement) and goBlock (empty scopes). *Vacuous*
    -- at top level (rigidTypeVars = []).
    (h_ambient_rigid : ∀ x ty, Env.context.types.find? x = some ty →
      ∀ v ∈ LTy.freeVars ty, v ∈ C.rigidTypeVars) :
    ∀ body, func.body = some body →
      ∃ (Γ_inst : TContext Unit) (output_inst : LMonoTy) (ρ : Subst),
        HasType C Γ_inst body (.forAll [] output_inst) ∧
        SubstWF ρ ∧
        (TContext.subst Γ_inst ρ).aliases = (funcContext Env.context func).aliases ∧
        TContextAliasEquiv (T := CoreLParams) (funcContext Env.context func).aliases
          (TContext.subst Γ_inst ρ) (funcContext Env.context func) ∧
        _root_.Lambda.AliasEquiv (funcContext Env.context func).aliases
          (LMonoTy.subst ρ output_inst) func.output := by
  intro body h_body
  simp only [Function.typeCheck, bind, Except.bind] at h
  elim_err h
  rename_i type h_type
  elim_err h
  rename_i h_undecl
  elim_err h
  elim_err h
  rename_i v_inst h_inst
  rw [h_body] at h
  simp only at h
  -- undeclared type-variable guard on the body
  split at h
  · simp only [reduceCtorEq] at h
  -- body = some branch, guard passed
  elim_err h
  rename_i v_resolve h_resolve
  elim_err h
  rename_i v_unify h_unify
  split at h <;> try contradiction
  -- alphaEquivMap = some
  rename_i alphaMap h_alphaMap
  elim_err h
  rename_i bwdMap h_alpha
  clear h
  -- Abbreviations matching the typechecker's terms (no `set`: Strata has no Mathlib).
  let renameSubst : Subst :=
    [bwdMap.toList.filterMap (fun x => if (x.1 == x.2) = true then none else some (x.1, LMonoTy.ftvar x.2))]
  let userSubst : Subst :=
    [(v_inst.fst.freeVars.eraseDups.zip func.typeArgs).map (fun x => (x.1, LMonoTy.ftvar x.2))]
  let bodyty : LMonoTy := v_resolve.fst.toLMonoTy
  -- The input signature pairs inserted into the internal env.
  have h_pairs_sig : ∀ p ∈ func.inputs.keys.zip
      (List.take func.inputs.keys.length v_inst.fst.destructArrow),
      p.2 ∈ v_inst.fst.destructArrow := by
    intro p hp
    exact List.mem_of_mem_take (List.of_mem_zip hp).2
  -- Internal env well-formedness (no AliasesResolved needed).
  have h_internalwf := typeCheck_internalEnv_TEnvWF type C Env v_inst.fst v_inst.snd
    (func.inputs.keys.zip (List.take func.inputs.keys.length v_inst.fst.destructArrow))
    (by rw [Prod.eta]; exact h_inst) h_wf h_pairs_sig
  -- Unwrap the mapError on the unify result.
  have h_unify' : Constraints.unify
      [(LMonoTy.mkArrow'
          ((List.drop func.inputs.keys.length v_inst.fst.destructArrow).getLast?.getD
            (List.getLast v_inst.fst.destructArrow (LMonoTy.destructArrow_non_empty v_inst.fst)))
        (List.drop func.inputs.keys.length v_inst.fst.destructArrow).dropLast,
        v_resolve.fst.toLMonoTy)] v_resolve.snd.stateSubstInfo = .ok v_unify := by
    cases hc : Constraints.unify
        [(LMonoTy.mkArrow'
            ((List.drop func.inputs.keys.length v_inst.fst.destructArrow).getLast?.getD
              (List.getLast v_inst.fst.destructArrow (LMonoTy.destructArrow_non_empty v_inst.fst)))
          (List.drop func.inputs.keys.length v_inst.fst.destructArrow).dropLast,
          v_resolve.fst.toLMonoTy)] v_resolve.snd.stateSubstInfo with
    | error e => rw [hc] at h_unify; simp [Except.mapError] at h_unify
    | ok w => rw [hc] at h_unify; simp [Except.mapError] at h_unify; rw [h_unify]
  -- SubstWF facts.
  have h_wf_unify : SubstWF v_unify.subst := v_unify.isWF
  have h_wf_rename : SubstWF renameSubst := by sorry
  -- WellScoped on the internal env (knownVars only grows).
  have h_ws_internal : WellScoped body (v_inst.snd.pushEmptyContext.addInNewestContext
      (LFunc.inputMonoSignature
        { name := func.name, typeArgs := v_inst.fst.freeVars.eraseDups, isConstr := func.isConstr,
          isRecursive := func.isRecursive,
          inputs := func.inputs.keys.zip (List.take func.inputs.keys.length v_inst.fst.destructArrow),
          output :=
            ((List.drop func.inputs.keys.length v_inst.fst.destructArrow).getLast?.getD
                  (List.getLast v_inst.fst.destructArrow (LMonoTy.destructArrow_non_empty v_inst.fst))).mkArrow'
              (List.drop func.inputs.keys.length v_inst.fst.destructArrow).dropLast,
          body := some body, attr := func.attr, concreteEval := func.concreteEval, axioms := func.axioms,
          preconditions := func.preconditions, measure := func.measure })).context := by sorry
  -- The resolve-core typing judgment, universally over absorbing substitutions.
  have h_core := resolve_HasType_core body v_resolve.fst C _ v_resolve.snd
    (by rw [Prod.eta]; exact h_resolve) h_internalwf h_fwf h_ws_internal
  -- Instantiate S := v_unify.subst.
  have h_absorbs : Subst.absorbs v_unify.subst v_resolve.snd.stateSubstInfo.subst :=
    Constraints.unify_absorbs _ _ _ h_unify'
  have h_unify_typed := h_core.1 v_unify.subst h_absorbs h_wf_unify (by sorry)
  -- Apply the renaming substitution to the whole judgment.
  have h_renamed := HasType_TContext_subst C _ body (.forAll [] (LMonoTy.subst v_unify.subst bodyty))
    renameSubst h_unify_typed h_wf_rename
  rw [LTy.subst_forAll_nil] at h_renamed
  -- `output_inst = subst renameSubst (subst v_unify.subst bodyty)` equals the reconstructed
  -- output RO (in fresh declaration-order instantiation vars); `renameSubst` inverts unify's
  -- renaming via `alphaEquivMap_renameSubst_inverse`. (Note: NO `userSubst`; see §10g.)
  have h_unify_eq := Constraints.unify_sound _ _ _ h_unify' _ List.mem_cons_self
  have h_m_eq : alphaMap = bwdMap := by cases h_alpha; rfl
  have h_out_eq : LMonoTy.subst renameSubst (LMonoTy.subst v_unify.subst bodyty) =
      ((List.drop func.inputs.keys.length v_inst.fst.destructArrow).getLast?.getD
          (List.getLast v_inst.fst.destructArrow (LMonoTy.destructArrow_non_empty v_inst.fst))).mkArrow'
        (List.drop func.inputs.keys.length v_inst.fst.destructArrow).dropLast := by
    have h_inv := alphaEquivMap_renameSubst_inverse v_inst.fst
      (((List.drop func.inputs.keys.length v_inst.fst.destructArrow).getLast?.getD
          (List.getLast v_inst.fst.destructArrow (LMonoTy.destructArrow_non_empty v_inst.fst))).mkArrow'
        (List.drop func.inputs.keys.length v_inst.fst.destructArrow).dropLast)
      v_unify.subst bwdMap (by rw [h_alphaMap, h_m_eq])
      (LMonoTy.freeVars_reconstructedOutput_subset v_inst.fst func.inputs.keys.length)
    simp only at h_inv
    rw [← h_unify_eq]; exact h_inv
  -- The declaration-order instantiation inverse `ρ` (NOT the appearance-order `userSubst`):
  -- `resolveAliases SIG = subst ρ v_inst.fst` (structural, general form).
  obtain ⟨ρ, Env_r, h_wf_ρ, h_ra⟩ :=
    LTy_instantiateWithCheck_inverse type C Env v_inst.fst v_inst.snd
      (by rw [Prod.eta]; exact h_inst) h_wf.aliasesWF
  -- Per-component alias facts (shared adapter), used by both the output and context conjuncts.
  obtain ⟨h_ae_out, h_ae_ins⟩ :=
    Function.typeCheck_inverse_components C Env func type v_inst ρ Env_r h_type h_ra
      h_wf.aliasesWF h_aliases_not_known
  -- Assemble the existential.
  refine ⟨_, _, ρ, h_renamed, h_wf_ρ, ?_, ?_, ?_⟩
  · -- aliases equality
    rw [TContext.subst_aliases, TContext.subst_aliases, TContext.subst_aliases]
    have h_ctx_eq : v_inst.snd.context = Env.context :=
      LTy_instantiateWithCheck_context' type C Env v_inst.fst v_inst.snd
        (by rw [Prod.eta]; exact h_inst)
    have h_lhs : (v_inst.snd.pushEmptyContext.addInNewestContext
        (List.map (fun p => (p.fst, LTy.forAll [] p.snd))
          (func.inputs.keys.zip (List.take func.inputs.keys.length v_inst.fst.destructArrow)))).context.aliases
        = v_inst.snd.context.aliases := rfl
    rw [h_lhs, h_ctx_eq]
    rfl
  · -- TContextAliasEquiv
    sorry
  · -- output AliasEquiv
    rw [h_out_eq]
    show Lambda.AliasEquiv Env.context.aliases _ func.output
    exact h_ae_out

/-- `bodyTyped` for the original function: the unresolved body has the declared
    return type polymorphically in the formal-parameter context. Top-down: extract
    the instantiated judgment + renaming, then chain the three bridges
    (`HasType_TContext_subst` for tyvars, `talias` for the output alias,
    `HasType_context_aliasEquiv` for the context alias). -/
theorem Function.typeCheck_bodyTyped (C : LContext CoreLParams) (Env : TEnv Unit)
    (func func' : Function) (Env' : TEnv Unit)
    (h : Function.typeCheck C Env func = .ok (func', Env'))
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions)
    (h_ws : ∀ body, func.body = some body → WellScoped body Env.context)
    (h_fresh : Subst.allKeysFresh (T := CoreLParams) Env.stateSubstInfo.subst Env.context)
    (h_closed : LExpr.checkContextTypesClosed (T := CoreLParams) Env)
    -- TODO(preservation): see `typeCheck_bodyTyped_instantiated`. Context alias names are
    -- non-reserved (enforced by `TEnv.addTypeAlias`); to be discharged as a preserved invariant.
    (h_aliases_not_known :
      ∀ a ∈ Env.context.aliases, a.name ≠ "arrow")
    -- Ambient-rigidity invariant; see `typeCheck_bodyTyped_instantiated`.
    (h_ambient_rigid : ∀ x ty, Env.context.types.find? x = some ty →
      ∀ v ∈ LTy.freeVars ty, v ∈ C.rigidTypeVars) :
    ∀ body, func.body = some body →
      HasType C (funcContext Env.context func) body (.forAll [] func.output) := by
  intro body h_body
  obtain ⟨Γ_inst, output_inst, ρ, h_ht, h_wf_ρ, h_alias_eq, h_ctx_ae, h_out_ae⟩ :=
    Function.typeCheck_bodyTyped_instantiated C Env func func' Env' h h_wf h_fwf h_ws h_fresh
      h_closed h_aliases_not_known h_ambient_rigid body h_body
  -- Bridge 1: rename type variables (fresh → user) on the whole judgment.
  have h_renamed := HasType_TContext_subst C Γ_inst body (.forAll [] output_inst) ρ h_ht h_wf_ρ
  rw [LTy.subst_forAll_nil] at h_renamed
  -- Bridge 2: alias-bridge the output type `subst ρ output_inst ↝ func.output`.
  have h_out_bridged : HasType C (TContext.subst Γ_inst ρ) body (.forAll [] func.output) := by
    rw [← h_alias_eq] at h_out_ae
    exact HasType.talias _ body _ _ h_out_ae h_renamed
  -- Bridge 3: alias-bridge the context `Γ_inst.subst ρ ↝ funcContext Env.context func`.
  -- `HasType_context_aliasEquiv` moves a judgment from Γ (= Γ_inst.subst ρ) to Γ'
  -- (= funcContext …), needing `Γ'.aliases = Γ.aliases` and the equivalence stated
  -- over `Γ.aliases`. Both come from `h_alias_eq` / `h_ctx_ae` after orienting.
  refine HasType_context_aliasEquiv C (TContext.subst Γ_inst ρ) (funcContext Env.context func)
    body (.forAll [] func.output) h_out_bridged h_alias_eq.symm ?_
  rw [h_alias_eq]; exact h_ctx_ae

/-- **Instantiated measure judgment.** As `typeCheck_bodyTyped_instantiated`, but
    for a non-variable measure: the measure resolves at type `int` in the
    instantiated context, and the renaming `ρ` recovers `funcContext func`'s context
    up to type-alias equivalence. The output type is `.int`, which is alias-free and
    fixed by `ρ`, so only the *context* alias bridge is needed (no output bridge). -/
theorem Function.typeCheck_measureTyped_instantiated (C : LContext CoreLParams) (Env : TEnv Unit)
    (func func' : Function) (Env' : TEnv Unit)
    (h : Function.typeCheck C Env func = .ok (func', Env'))
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions)
    (h_ws : ∀ body, func.body = some body → WellScoped body Env.context)
    (h_fresh : Subst.allKeysFresh (T := CoreLParams) Env.stateSubstInfo.subst Env.context)
    (h_closed : LExpr.checkContextTypesClosed (T := CoreLParams) Env)
    -- TODO(preservation): see `typeCheck_bodyTyped_instantiated`. Context alias names are
    -- non-reserved (enforced by `TEnv.addTypeAlias`); to be discharged as a preserved invariant.
    (h_aliases_not_known :
      ∀ a ∈ Env.context.aliases, a.name ≠ "arrow")
    -- Ambient-rigidity invariant; see `typeCheck_bodyTyped_instantiated`.
    (h_ambient_rigid : ∀ x ty, Env.context.types.find? x = some ty →
      ∀ v ∈ LTy.freeVars ty, v ∈ C.rigidTypeVars) :
    ∀ m, func.measure = some m →
      (∀ mid x ann, m ≠ .fvar mid x ann) →
      ∃ (Γ_inst : TContext Unit) (ρ : Subst),
        HasType C Γ_inst m (.forAll [] .int) ∧
        SubstWF ρ ∧
        (TContext.subst Γ_inst ρ).aliases = (funcContext Env.context func).aliases ∧
        TContextAliasEquiv (T := CoreLParams) (funcContext Env.context func).aliases
          (TContext.subst Γ_inst ρ) (funcContext Env.context func) := by
  sorry

/-- `measureTyped` for the original function: a non-variable measure has type `int`. -/
theorem Function.typeCheck_measureTyped (C : LContext CoreLParams) (Env : TEnv Unit)
    (func func' : Function) (Env' : TEnv Unit)
    (h : Function.typeCheck C Env func = .ok (func', Env'))
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions)
    (h_ws : ∀ body, func.body = some body → WellScoped body Env.context)
    (h_fresh : Subst.allKeysFresh (T := CoreLParams) Env.stateSubstInfo.subst Env.context)
    (h_closed : LExpr.checkContextTypesClosed (T := CoreLParams) Env)
    -- TODO(preservation): see `typeCheck_bodyTyped_instantiated`. Context alias names are
    -- non-reserved (enforced by `TEnv.addTypeAlias`); to be discharged as a preserved invariant.
    (h_aliases_not_known :
      ∀ a ∈ Env.context.aliases, a.name ≠ "arrow")
    -- Ambient-rigidity invariant; see `typeCheck_bodyTyped_instantiated`.
    (h_ambient_rigid : ∀ x ty, Env.context.types.find? x = some ty →
      ∀ v ∈ LTy.freeVars ty, v ∈ C.rigidTypeVars) :
    ∀ m, func.measure = some m →
      (∀ mid x ann, m ≠ .fvar mid x ann) →
      HasType C (funcContext Env.context func) m (.forAll [] .int) := by
  intro m h_measure h_nonfvar
  obtain ⟨Γ_inst, ρ, h_ht, h_wf_ρ, h_alias_eq, h_ctx_ae⟩ :=
    Function.typeCheck_measureTyped_instantiated C Env func func' Env' h h_wf h_fwf h_ws h_fresh
      h_closed h_aliases_not_known h_ambient_rigid m h_measure h_nonfvar
  -- Bridge 1: rename type variables on the whole judgment (output `.int` is fixed).
  have h_renamed := HasType_TContext_subst C Γ_inst m (.forAll [] .int) ρ h_ht h_wf_ρ
  rw [LTy.subst_forAll_nil, LMonoTy.int, LMonoTy.subst_tcons, LMonoTys.subst_nil] at h_renamed
  -- Bridge 3 only: alias-bridge the context (the `.int` output needs no bridge).
  refine HasType_context_aliasEquiv C (TContext.subst Γ_inst ρ) (funcContext Env.context func)
    m (.forAll [] .int) h_renamed h_alias_eq.symm ?_
  rw [h_alias_eq]; exact h_ctx_ae

/--
Polymorphic soundness: if `Function.typeCheck` succeeds, the original function
satisfies `FuncHasType`.
-/
theorem Function.typeCheck_sound (C : LContext CoreLParams) (Env : TEnv Unit)
    (func func' : Function) (Env' : TEnv Unit)
    (h : Function.typeCheck C Env func = .ok (func', Env'))
    (h_wf : TEnvWF (T := CoreLParams) Env)
    (h_fwf : FactoryWF C.functions)
    (h_ws : ∀ body, func.body = some body → WellScoped body Env.context)
    (h_fresh : Subst.allKeysFresh (T := CoreLParams) Env.stateSubstInfo.subst Env.context)
    (h_closed : LExpr.checkContextTypesClosed (T := CoreLParams) Env)
    -- TODO(preservation): see `typeCheck_bodyTyped_instantiated`. Context alias names are
    -- non-reserved (enforced by `TEnv.addTypeAlias`); to be discharged as a preserved invariant.
    (h_aliases_not_known :
      ∀ a ∈ Env.context.aliases, a.name ≠ "arrow")
    -- Ambient-rigidity invariant; see `typeCheck_bodyTyped_instantiated`.
    (h_ambient_rigid : ∀ x ty, Env.context.types.find? x = some ty →
      ∀ v ∈ LTy.freeVars ty, v ∈ C.rigidTypeVars) :
    FuncHasType C Env.context func := by
  exact {
    inputsNodup := Function.typeCheck_inputsNodup_orig C Env func func' Env' h
    typeArgsNodup := Function.typeCheck_typeArgsNodup_orig C Env func func' Env' h
    noUndeclaredVars := Function.typeCheck_noUndeclaredVars_orig C Env func func' Env' h h_wf
    bodyTyped := Function.typeCheck_bodyTyped C Env func func' Env' h h_wf h_fwf h_ws h_fresh h_closed h_aliases_not_known h_ambient_rigid
    measureTyped := Function.typeCheck_measureTyped C Env func func' Env' h h_wf h_fwf h_ws h_fresh h_closed h_aliases_not_known h_ambient_rigid
  }

end TypeSpec
end Core
