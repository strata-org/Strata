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

/-! ## Per-component alias inverse (`typeCheck_inverse_components`)

Helper lemmas + the shared per-component alias adapter, extracted to its own file to keep
`FunctionTypeSpecProps` from growing by ~1100 lines. -/

namespace Core
namespace TypeSpec

open Lambda LExpr Imperative

/-- Well-formedness of the arrow constructor in a context: `"arrow"` is registered at arity 2.
    True of `KnownTypes.default` and any extending context (`KnownTypes` is name-keyed, so `"arrow"`
    has at most one arity, and it is 2). This is the only extra `C`-hypothesis the soundness chain
    needs to know the reconstructed/resolved arrow spine is binary. -/
def ArrowKnownBinary (C : LContext CoreLParams) : Prop :=
  C.knownTypes.contains { name := "arrow", metadata := 2 } = true

/-- From `ArrowKnownBinary` (arrow registered at arity 2), any `"arrow"` node that is a known
    instance has arity exactly 2. Uses that `KnownTypes` is name-keyed (`Identifiers.contains`
    looks up by name, so at most one arity per name). -/
theorem ArrowKnownBinary.arrow_arity_eq_two {C : LContext CoreLParams} (h : ArrowKnownBinary C) :
    ∀ k, C.knownTypes.contains { name := "arrow", metadata := k } = true → k = 2 := by
  intro k hk
  unfold ArrowKnownBinary at h
  simp only [Lambda.KnownTypes.contains, Lambda.Identifiers.contains] at h hk
  -- both are `match C.knownTypes["arrow"]? with | some i => _ == i | none => false`
  cases h_lookup : C.knownTypes["arrow"]? with
  | none => rw [h_lookup] at h; simp at h
  | some i =>
    rw [h_lookup] at h hk
    simp only [beq_iff_eq] at h hk
    -- h : 2 = i, hk : k = i  ⇒  k = 2
    subst h; exact hk

/-- A successful `instantiateWithCheck` guarantees its result is a known instance: the checker
    returns `.ok` only after the `isInstanceOfKnownType` guard passes. Extracted here so both call
    sites of `typeCheck_inverse_components` can discharge the `h_known` hypothesis from `h_inst`. -/
theorem knownInstance_of_instantiateWithCheck (type : LTy) (C : LContext CoreLParams)
    (Env : TEnv Unit) (v_inst : LMonoTy × TEnv Unit)
    (h_inst : LTy.instantiateWithCheck type C Env = .ok v_inst) :
    LMonoTy.knownInstance v_inst.fst C.knownTypes = true := by
  have h := h_inst
  rw [← Prod.eta v_inst] at h
  simp only [LTy.instantiateWithCheck, Bind.bind, Except.bind] at h
  elim_err h
  rename_i v1 h_res; obtain ⟨m0, E1⟩ := v1
  dsimp only at h
  -- First guard: checkNoFutureGenVars.
  split at h
  · simp only [reduceCtorEq] at h
  · -- Second guard: isInstanceOfKnownType.
    split at h
    · rename_i h_isknown
      simp only [Pure.pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
      rw [← h.1]
      simpa only [isInstanceOfKnownType] using h_isknown
    · simp only [reduceCtorEq] at h

-- Size measure for the mutual induction over `LMonoTy`/`LMonoTys`.
mutual
private def icSize (mty : LMonoTy) : Nat :=
  match mty with
  | .ftvar _ => 1
  | .bitvec _ => 1
  | .tcons _ args => 1 + icSizes args
private def icSizes (mtys : LMonoTys) : Nat :=
  match mtys with
  | [] => 0
  | mty :: rest => 1 + icSize mty + icSizes rest
end

/-- `destructArrow` of a type variable is the singleton list. -/
private theorem destructArrow_ftvar (w : TyIdentifier) :
    (LMonoTy.ftvar w).destructArrow = [LMonoTy.ftvar w] := by
  simp only [LMonoTy.destructArrow]

/-- Under an ftvar-renaming `ρ`, `subst ρ` of a type variable is again a type variable. -/
private theorem subst_ftvar_is_ftvar (ρ : Subst)
    (h_ρ_ftvar : ∀ mty ∈ Maps.values ρ, ∃ w, mty = LMonoTy.ftvar w)
    (x : TyIdentifier) :
    ∃ w, LMonoTy.subst ρ (LMonoTy.ftvar x) = LMonoTy.ftvar w := by
  simp only [LMonoTy.subst_unfold]
  cases h_find : Maps.find? ρ x with
  | none => exact ⟨x, rfl⟩
  | some sty =>
    have h_mem : sty ∈ Maps.values ρ := Maps.find?_mem_values _ h_find
    obtain ⟨w, h_w⟩ := h_ρ_ftvar sty h_mem
    exact ⟨w, h_w⟩

/-- `LMonoTys.subst` is `map (LMonoTy.subst ρ)`. -/
private theorem subst_list_eq_map (ρ : Subst) (mtys : LMonoTys) :
    LMonoTys.subst ρ mtys = mtys.map (LMonoTy.subst ρ) := by
  induction mtys with
  | nil => simp only [LMonoTys.subst_nil, List.map_nil]
  | cons hd tl ih => rw [subst_cons_eq', ih, List.map_cons]

/-- Combined mutual claim: under an ftvar-renaming `ρ`, `subst ρ` commutes with
`destructArrow`. -/
private theorem destructArrow_subst_combined (ρ : Subst)
    (h_ρ_ftvar : ∀ mty ∈ Maps.values ρ, ∃ w, mty = LMonoTy.ftvar w) (n : Nat) :
    (∀ (mty : LMonoTy), icSize mty ≤ n →
      (LMonoTy.subst ρ mty).destructArrow
        = mty.destructArrow.map (LMonoTy.subst ρ)) ∧
    (∀ (mtys : LMonoTys), icSizes mtys ≤ n →
      LMonoTys.destructArrow (mtys.map (LMonoTy.subst ρ))
        = (LMonoTys.destructArrow mtys).map (LMonoTy.subst ρ)) := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
  refine ⟨?_, ?_⟩
  · -- single type case
    intro mty h_sz
    match mty with
    | .ftvar x =>
      obtain ⟨w, h_w⟩ := subst_ftvar_is_ftvar ρ h_ρ_ftvar x
      rw [h_w, destructArrow_ftvar, destructArrow_ftvar]
      simp only [List.map_cons, List.map_nil, h_w]
    | .bitvec k =>
      rw [LMonoTy.subst_bitvec]
      simp only [LMonoTy.destructArrow, LMonoTy.subst_bitvec, List.map_cons, List.map_nil]
    | .tcons name args =>
      rw [LMonoTy.subst_tcons, subst_list_eq_map]
      -- destructArrow only cares about the arrow shape: `tcons "arrow" (t1 :: trest)`.
      by_cases h_shape : (name = "arrow" ∧ ∃ t1 trest, args = t1 :: trest)
      · -- arrow case both sides
        obtain ⟨h_name, t1, trest, h_args⟩ := h_shape
        subst h_name; subst h_args
        simp only [List.map_cons, LMonoTy.destructArrow]
        have h_trest_sz : icSizes trest < n := by
          simp only [icSize, icSizes] at h_sz ⊢; omega
        have h_ih := (ih (icSizes trest) h_trest_sz).2 trest (Nat.le_refl _)
        rw [h_ih]
      · -- non-arrow: destructArrow returns the singleton on both sides
        have h_ds_l : LMonoTy.destructArrow
            (.tcons name (args.map (LMonoTy.subst ρ)))
            = [LMonoTy.tcons name (args.map (LMonoTy.subst ρ))] := by
          unfold LMonoTy.destructArrow
          split
          · rename_i h_m
            injection h_m with h_nm h_as
            subst h_nm
            obtain ⟨t1, trest, h_ts⟩ := List.map_eq_cons_iff.mp h_as
            exact absurd ⟨rfl, t1, trest, h_ts.1⟩ h_shape
          · rfl
        have h_ds_r : LMonoTy.destructArrow (.tcons name args)
            = [LMonoTy.tcons name args] := by
          unfold LMonoTy.destructArrow
          split
          · rename_i h_m
            injection h_m with h_nm h_as
            subst h_nm
            exact absurd ⟨rfl, _, _, h_as⟩ h_shape
          · rfl
        rw [h_ds_l, h_ds_r, List.map_cons, List.map_nil, LMonoTy.subst_tcons,
          subst_list_eq_map]
  · -- list case
    intro mtys h_sz
    match mtys with
    | [] => simp only [List.map_nil, LMonoTys.destructArrow]
    | mty :: mrest =>
      simp only [List.map_cons, LMonoTys.destructArrow]
      have h_mty_sz : icSize mty < n := by
        simp only [icSizes] at h_sz; omega
      have h_mrest_sz : icSizes mrest < n := by
        simp only [icSizes] at h_sz; omega
      have h_ih_mty := (ih (icSize mty) h_mty_sz).1 mty (Nat.le_refl _)
      have h_ih_mrest := (ih (icSizes mrest) h_mrest_sz).2 mrest (Nat.le_refl _)
      rw [h_ih_mty, h_ih_mrest, List.map_append]

/-- `destructArrow` of a binary arrow peels the domain and recurses on the codomain. -/
private theorem destructArrow_arrow (t1 t2 : LMonoTy) :
    (LMonoTy.arrow t1 t2).destructArrow = t1 :: t2.destructArrow := by
  simp only [LMonoTy.arrow, LMonoTy.destructArrow, LMonoTys.destructArrow, List.append_nil]

/-- `destructArrow (mkArrow' ret args) = args ++ ret.destructArrow`: the domain args are kept
whole (each is one element), and the codomain `ret` is flattened. -/
private theorem destructArrow_mkArrow' (ret : LMonoTy) (args : LMonoTys) :
    (LMonoTy.mkArrow' ret args).destructArrow = args ++ ret.destructArrow := by
  induction args with
  | nil => simp only [LMonoTy.mkArrow'_nil, List.nil_append]
  | cons a as ih =>
    rw [LMonoTy.mkArrow'_cons, destructArrow_arrow, ih, List.cons_append]

/-- Convenience corollary of the combined helper: under an ftvar-renaming `ρ`,
`(subst ρ mty).destructArrow = mty.destructArrow.map (subst ρ)`. -/
private theorem destructArrow_subst (ρ : Subst)
    (h_ρ_ftvar : ∀ mty ∈ Maps.values ρ, ∃ w, mty = LMonoTy.ftvar w) (mty : LMonoTy) :
    (LMonoTy.subst ρ mty).destructArrow = mty.destructArrow.map (LMonoTy.subst ρ) :=
  (destructArrow_subst_combined ρ h_ρ_ftvar (icSize mty)).1 mty (Nat.le_refl _)

/-- `destructArrow (mkArrow hd tl)` peels the domains `hd` and every element of `tl` WHOLE,
then flattens only the final return (`tl.getLast`). For nonempty `tl`:
`destructArrow (mkArrow hd tl) = hd :: tl.dropLast ++ destructArrow (tl.getLast)`. -/
private theorem destructArrow_mkArrow_cons (hd x : LMonoTy) (xs : LMonoTys) :
    (LMonoTy.mkArrow hd (x :: xs)).destructArrow
      = (hd :: (x :: xs).dropLast) ++ ((x :: xs).getLast (by simp)).destructArrow := by
  induction xs generalizing hd x with
  | nil =>
    show (LMonoTy.arrow hd (LMonoTy.mkArrow x [])).destructArrow = _
    rw [LMonoTy.mkArrow, destructArrow_arrow]
    show hd :: x.destructArrow = (hd :: [x].dropLast) ++ x.destructArrow
    rfl
  | cons y ys ih =>
    show (LMonoTy.arrow hd (LMonoTy.mkArrow x (y :: ys))).destructArrow = _
    rw [destructArrow_arrow, ih x y]
    simp only [List.dropLast_cons₂, List.getLast_cons_cons, List.cons_append]

/-- `LMonoTys.destructArrow` distributes over append. -/
private theorem destructArrowList_append (as bs : LMonoTys) :
    LMonoTys.destructArrow (as ++ bs)
      = LMonoTys.destructArrow as ++ LMonoTys.destructArrow bs := by
  induction as with
  | nil => simp only [List.nil_append, LMonoTys.destructArrow]
  | cons a as ih =>
    simp only [List.cons_append, LMonoTys.destructArrow, ih, List.append_assoc]

/-- A monotype whose head is not a positive-arity `"arrow"` destructs to itself. -/
private theorem destructArrow_singleton_of_not_arrow (mty : LMonoTy)
    (h : ¬ ∃ t1 trest, mty = LMonoTy.tcons "arrow" (t1 :: trest)) :
    mty.destructArrow = [mty] := by
  unfold LMonoTy.destructArrow
  split
  · rename_i t1 trest
    exact absurd ⟨t1, trest, rfl⟩ h
  · rfl


/-- The last element of a `destructArrow` output destructs to itself. Guarded by
    `knownInstance`/`h_arrow2`: without the binary invariant a malformed unary `tcons "arrow" [t1]`
    could put a non-atomic kept-whole domain last. Stated over `getLast?` to avoid dependent
    `getLast` proofs. -/
private theorem getLast?_destructArrow_atomic (ks : Lambda.KnownTypes)
    (h_arrow2 : ∀ k, ks.contains { name := "arrow", metadata := k } = true → k = 2) (n : Nat) :
    (∀ (mty : LMonoTy), icSize mty ≤ n → LMonoTy.knownInstance mty ks = true →
      ∀ z, mty.destructArrow.getLast? = some z → z.destructArrow = [z]) ∧
    (∀ (mtys : LMonoTys), icSizes mtys ≤ n → LMonoTys.knownInstances mtys ks = true →
      ∀ z, (LMonoTys.destructArrow mtys).getLast? = some z → z.destructArrow = [z]) := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
  refine ⟨?_, ?_⟩
  · intro mty h_sz h_ki z h_last
    match mty with
    | .ftvar x =>
      rw [destructArrow_ftvar, List.getLast?_singleton] at h_last
      injection h_last with h_z; subst h_z; exact destructArrow_ftvar x
    | .bitvec k =>
      have h_bv : (LMonoTy.bitvec k).destructArrow = [LMonoTy.bitvec k] := by
        simp only [LMonoTy.destructArrow]
      rw [h_bv, List.getLast?_singleton] at h_last
      injection h_last with h_z; subst h_z; exact h_bv
    | .tcons name args =>
      by_cases h_shape : name = "arrow" ∧ ∃ t1 trest, args = t1 :: trest
      · obtain ⟨h_name, t1, trest, h_args⟩ := h_shape
        subst h_name; subst h_args
        have h_da : (LMonoTy.tcons "arrow" (t1 :: trest)).destructArrow
            = t1 :: LMonoTys.destructArrow trest := by simp only [LMonoTy.destructArrow]
        rw [h_da] at h_last
        have h_trest_sz : icSizes trest < n := by simp only [icSize, icSizes] at h_sz ⊢; omega
        -- knownInstance forces arity 2: args = t1 :: trest has length 2, so trest = [t2].
        simp only [LMonoTy.knownInstance, Bool.and_eq_true] at h_ki
        obtain ⟨h_contains, h_ki_args⟩ := h_ki
        have h_len2 : (t1 :: trest).length = 2 := h_arrow2 _ h_contains
        obtain ⟨t2, h_t2⟩ : ∃ t2, trest = [t2] := by
          match trest with
          | [] => simp only [List.length_cons, List.length_nil] at h_len2; omega
          | [t2] => exact ⟨t2, rfl⟩
          | _ :: _ :: _ => simp only [List.length_cons] at h_len2; omega
        subst h_t2
        -- knownInstance t2
        have h_ki_t2 : LMonoTy.knownInstance t2 ks = true := by
          simp only [LMonoTys.knownInstances] at h_ki_args
          split at h_ki_args
          · rename_i h_ki_t1
            split at h_ki_args
            · rename_i h; exact h
            · exact absurd h_ki_args (by simp)
          · exact absurd h_ki_args (by simp)
        -- da = t1 :: destructArrow t2 (nonempty), last = last of destructArrow t2.
        have h_dt_ne : (LMonoTy.destructArrow t2) ≠ [] := LMonoTy.destructArrow_non_empty t2
        have h_dt2 : LMonoTys.destructArrow [t2] = LMonoTy.destructArrow t2 := by
          simp only [LMonoTys.destructArrow, List.append_nil]
        rw [h_dt2] at h_last
        rw [List.getLast?_cons] at h_last
        obtain ⟨u, h_u⟩ : ∃ u, (LMonoTy.destructArrow t2).getLast? = some u := by
          cases h_g : (LMonoTy.destructArrow t2).getLast? with
          | none => exact absurd (List.getLast?_eq_none_iff.mp h_g) h_dt_ne
          | some u => exact ⟨u, rfl⟩
        rw [h_u, Option.getD_some] at h_last
        injection h_last with h_z; subst h_z
        have h_t2_sz : icSize t2 < n := by simp only [icSize, icSizes] at h_sz ⊢; omega
        exact (ih (icSize t2) h_t2_sz).1 t2 (Nat.le_refl _) h_ki_t2 u h_u
      · have h_ds : (LMonoTy.tcons name args).destructArrow = [LMonoTy.tcons name args] := by
          apply destructArrow_singleton_of_not_arrow
          rintro ⟨t1, trest, h_eq⟩; injection h_eq with h_nm h_as
          exact h_shape ⟨h_nm, t1, trest, h_as⟩
        rw [h_ds, List.getLast?_singleton] at h_last
        injection h_last with h_z; subst h_z; exact h_ds
  · intro mtys h_sz h_ki z h_last
    match mtys with
    | [] =>
      simp only [LMonoTys.destructArrow, List.getLast?_nil] at h_last
      exact absurd h_last (by simp)
    | mty :: mrest =>
      have h_da : LMonoTys.destructArrow (mty :: mrest)
          = mty.destructArrow ++ LMonoTys.destructArrow mrest := by
        simp only [LMonoTys.destructArrow]
      rw [h_da, List.getLast?_append] at h_last
      have h_mty_sz : icSize mty < n := by simp only [icSizes] at h_sz; omega
      have h_mrest_sz : icSizes mrest < n := by simp only [icSizes] at h_sz; omega
      -- knownInstances (mty :: mrest) gives knownInstance mty AND knownInstances mrest.
      have h_ki_split : LMonoTy.knownInstance mty ks = true ∧ LMonoTys.knownInstances mrest ks = true := by
        simp only [LMonoTys.knownInstances] at h_ki
        split at h_ki
        · rename_i h_m; exact ⟨h_m, h_ki⟩
        · exact absurd h_ki (by simp)
      cases h_mr : (LMonoTys.destructArrow mrest).getLast? with
      | none =>
        rw [h_mr, Option.none_or] at h_last
        exact (ih (icSize mty) h_mty_sz).1 mty (Nat.le_refl _) h_ki_split.1 z h_last
      | some w =>
        rw [h_mr, Option.some_or] at h_last
        injection h_last with h_wz; subst h_wz
        exact (ih (icSizes mrest) h_mrest_sz).2 mrest (Nat.le_refl _) h_ki_split.2 w h_mr

/-- Roundtrip: for a monotype whose `"arrow"` tcons nodes are all binary (arity 2), rebuilding
via `mkArrow'` from the flattened `destructArrow` spine recovers the original type.  The binary
condition is derived from `knownInstance` together with the fact that the known-types table
registers `"arrow"` only at arity 2. -/
private theorem mkArrow'_destructArrow_roundtrip (ks : Lambda.KnownTypes)
    (h_arrow2 : ∀ k, ks.contains { name := "arrow", metadata := k } = true → k = 2)
    (d : LMonoTy) (n : Nat) :
    ∀ (mty : LMonoTy), icSize mty ≤ n →
      LMonoTy.knownInstance mty ks = true →
      LMonoTy.mkArrow' (mty.destructArrow.getLast?.getD d) mty.destructArrow.dropLast = mty := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro mty h_sz h_known
  match mty with
  | .ftvar x =>
    rw [destructArrow_ftvar]; rfl
  | .bitvec k =>
    show ([LMonoTy.bitvec k].getLast?.getD d).mkArrow' [LMonoTy.bitvec k].dropLast = _
    rfl
  | .tcons name args =>
    by_cases h_arrow : name = "arrow" ∧ ∃ t1 trest, args = t1 :: trest
    · obtain ⟨h_name, t1, trest, h_args⟩ := h_arrow
      subst h_name; subst h_args
      -- knownInstance gives arity 2 and knownInstance of the codomain.
      simp only [LMonoTy.knownInstance, Bool.and_eq_true] at h_known
      obtain ⟨h_contains, h_ki_args⟩ := h_known
      have h_len2 : (t1 :: trest).length = 2 := h_arrow2 _ h_contains
      -- trest is a singleton [t2]
      have h_trest : ∃ t2, trest = [t2] := by
        match trest with
        | [] => simp only [List.length_cons, List.length_nil] at h_len2; omega
        | [t2] => exact ⟨t2, rfl⟩
        | _ :: _ :: _ => simp only [List.length_cons] at h_len2; omega
      obtain ⟨t2, h_t2⟩ := h_trest
      subst h_t2
      -- knownInstance t2
      have h_ki_t2 : LMonoTy.knownInstance t2 ks = true := by
        simp only [LMonoTys.knownInstances] at h_ki_args
        split at h_ki_args
        · rename_i h_ki_t1
          split at h_ki_args
          · rename_i h; exact h
          · exact absurd h_ki_args (by simp)
        · exact absurd h_ki_args (by simp)
      -- destructArrow (arrow t1 t2) = t1 :: destructArrow t2
      have h_da : (LMonoTy.tcons "arrow" [t1, t2]).destructArrow = t1 :: t2.destructArrow := by
        rw [show LMonoTy.tcons "arrow" [t1, t2] = LMonoTy.arrow t1 t2 from rfl]
        exact destructArrow_arrow t1 t2
      rw [h_da]
      -- destructArrow t2 is nonempty
      have h_ne := LMonoTy.destructArrow_non_empty t2
      obtain ⟨b, rest, h_da2⟩ : ∃ b rest, t2.destructArrow = b :: rest := by
        match h : t2.destructArrow with
        | [] => exact absurd h h_ne
        | b :: rest => exact ⟨b, rest, rfl⟩
      rw [h_da2, List.getLast?_cons_cons, List.dropLast_cons₂, LMonoTy.mkArrow'_cons]
      -- IH on t2
      have h_sz_t2 : icSize t2 < n := by
        simp only [icSize, icSizes] at h_sz; omega
      have h_rt_t2 := ih (icSize t2) h_sz_t2 t2 (Nat.le_refl _) h_ki_t2
      rw [h_da2] at h_rt_t2
      rw [h_rt_t2]; rfl
    · -- non-arrow head: destructArrow returns the singleton
      have h_not : ¬ ∃ t1 trest, LMonoTy.tcons name args = LMonoTy.tcons "arrow" (t1 :: trest) := by
        rintro ⟨t1, trest, h_eq⟩
        injection h_eq with h_nm h_as
        exact h_arrow ⟨h_nm, t1, trest, h_as⟩
      rw [destructArrow_singleton_of_not_arrow _ h_not]; rfl

/-- Roundtrip from `arrowsBinary` (context-free): if every `"arrow"` node of `mty` is binary, then
    rebuilding via `mkArrow'` from the `destructArrow` spine recovers `mty`. Mirror of
    `mkArrow'_destructArrow_roundtrip` but keyed on the structural `arrowsBinary` predicate rather
    than `knownInstance`, so it applies to `func.output` (guarded by `LFunc.type`). -/
private theorem mkArrow'_destructArrow_roundtrip_binary (d : LMonoTy) (n : Nat) :
    ∀ (mty : LMonoTy), icSize mty ≤ n →
      LMonoTy.arrowsBinary mty = true →
      LMonoTy.mkArrow' (mty.destructArrow.getLast?.getD d) mty.destructArrow.dropLast = mty := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
  intro mty h_sz h_bin
  match mty with
  | .ftvar x => rw [destructArrow_ftvar]; rfl
  | .bitvec k =>
    show ([LMonoTy.bitvec k].getLast?.getD d).mkArrow' [LMonoTy.bitvec k].dropLast = _
    rfl
  | .tcons name args =>
    by_cases h_arrow : name = "arrow" ∧ ∃ t1 trest, args = t1 :: trest
    · obtain ⟨h_name, t1, trest, h_args⟩ := h_arrow
      subst h_name; subst h_args
      -- arrowsBinary gives arity 2 and arrowsBinary of the args.
      simp only [LMonoTy.arrowsBinary, if_pos, Bool.and_eq_true, beq_iff_eq] at h_bin
      obtain ⟨h_len2, h_bin_args⟩ := h_bin
      obtain ⟨t2, h_t2⟩ : ∃ t2, trest = [t2] := by
        match trest with
        | [] => simp only [List.length_cons, List.length_nil] at h_len2; omega
        | [t2] => exact ⟨t2, rfl⟩
        | _ :: _ :: _ => simp only [List.length_cons] at h_len2; omega
      subst h_t2
      have h_bin_t2 : LMonoTy.arrowsBinary t2 = true := by
        simp only [LMonoTys.arrowsBinary, Bool.and_eq_true] at h_bin_args
        exact h_bin_args.2.1
      have h_da : (LMonoTy.tcons "arrow" [t1, t2]).destructArrow = t1 :: t2.destructArrow := by
        rw [show LMonoTy.tcons "arrow" [t1, t2] = LMonoTy.arrow t1 t2 from rfl]
        exact destructArrow_arrow t1 t2
      rw [h_da]
      have h_ne := LMonoTy.destructArrow_non_empty t2
      obtain ⟨b, rest, h_da2⟩ : ∃ b rest, t2.destructArrow = b :: rest := by
        match h : t2.destructArrow with
        | [] => exact absurd h h_ne
        | b :: rest => exact ⟨b, rest, rfl⟩
      rw [h_da2, List.getLast?_cons_cons, List.dropLast_cons₂, LMonoTy.mkArrow'_cons]
      have h_sz_t2 : icSize t2 < n := by simp only [icSize, icSizes] at h_sz; omega
      have h_rt_t2 := ih (icSize t2) h_sz_t2 t2 (Nat.le_refl _) h_bin_t2
      rw [h_da2] at h_rt_t2
      rw [h_rt_t2]; rfl
    · have h_not : ¬ ∃ t1 trest, LMonoTy.tcons name args = LMonoTy.tcons "arrow" (t1 :: trest) := by
        rintro ⟨t1, trest, h_eq⟩
        injection h_eq with h_nm h_as
        exact h_arrow ⟨h_nm, t1, trest, h_as⟩
      rw [destructArrow_singleton_of_not_arrow _ h_not]; rfl

/-- `destructArrow (mkArrow hd (init ++ [last])) = hd :: init ++ last.destructArrow`: the domains
    `hd` and `init` are kept whole, and only the final codomain `last` is flattened. -/
private theorem destructArrow_mkArrow_snoc (hd : LMonoTy) (init : LMonoTys) (last : LMonoTy) :
    (LMonoTy.mkArrow hd (init ++ [last])).destructArrow
      = (hd :: init) ++ last.destructArrow := by
  induction init generalizing hd with
  | nil =>
    -- mkArrow hd [last] = arrow hd last
    show (LMonoTy.mkArrow hd [last]).destructArrow = _
    rw [show LMonoTy.mkArrow hd [last] = LMonoTy.arrow hd (LMonoTy.mkArrow last []) from rfl,
      show LMonoTy.mkArrow last [] = last from rfl, destructArrow_arrow]
    simp only [List.nil_append, List.cons_append]
  | cons a as ih =>
    show (LMonoTy.mkArrow hd (a :: (as ++ [last]))).destructArrow = _
    rw [show LMonoTy.mkArrow hd (a :: (as ++ [last]))
        = LMonoTy.arrow hd (LMonoTy.mkArrow a (as ++ [last])) from rfl, destructArrow_arrow, ih a]
    simp only [List.cons_append]

/-- `subst` distributes over `mkArrow'`: `subst ρ (mkArrow' ret args) = mkArrow' (subst ρ ret) (map (subst ρ) args)`. -/
private theorem subst_mkArrow' (ρ : Subst) (ret : LMonoTy) (args : LMonoTys) :
    LMonoTy.subst ρ (LMonoTy.mkArrow' ret args)
      = LMonoTy.mkArrow' (LMonoTy.subst ρ ret) (args.map (LMonoTy.subst ρ)) := by
  induction args with
  | nil => simp only [LMonoTy.mkArrow'_nil, List.map_nil]
  | cons a as ih =>
    rw [LMonoTy.mkArrow'_cons, List.map_cons, LMonoTy.mkArrow'_cons,
      show LMonoTy.arrow a (LMonoTy.mkArrow' ret as) = LMonoTy.tcons "arrow" [a, LMonoTy.mkArrow' ret as] from rfl,
      LMonoTy.subst_tcons]
    simp only [subst_list_eq_map, List.map_cons, List.map_nil]
    rw [ih]; rfl

/-- Generalized crux: `destructArrow (mkArrow hd tl) = hd :: tl` when `tl` is nonempty and its
    LAST element is arrow-atomic (destructs to itself). The domains `hd` and `tl.dropLast` are kept
    whole; only the final codomain `tl.getLast` is re-destructed, and by hypothesis it's atomic. -/
private theorem destructArrow_mkArrow_flat_of_atomic (hd : LMonoTy) (tl : LMonoTys)
    (h_ne : tl ≠ [])
    (h_last_atomic : ∀ z, tl.getLast? = some z → z.destructArrow = [z]) :
    (LMonoTy.mkArrow hd tl).destructArrow = hd :: tl := by
  obtain ⟨x, xs, h_xxs⟩ : ∃ x xs, tl = x :: xs := by
    cases h_c : tl with
    | nil => exact absurd h_c h_ne
    | cons a as => exact ⟨a, as, rfl⟩
  subst h_xxs
  rw [destructArrow_mkArrow_cons]
  obtain ⟨u, h_u⟩ : ∃ u, (x :: xs).getLast? = some u := by
    cases h_g : (x :: xs).getLast? with
    | none => exact absurd (List.getLast?_eq_none_iff.mp h_g) (by simp)
    | some u => exact ⟨u, rfl⟩
  have h_gl_val : (x :: xs).getLast (by simp) = u := by
    have h_e := List.getLast?_eq_some_getLast (l := x :: xs) (by simp)
    rw [h_u] at h_e; injection h_e with h; exact h.symm
  rw [h_gl_val, h_last_atomic u h_u]
  have h_reassemble : (x :: xs).dropLast ++ [(x :: xs).getLast (by simp)] = x :: xs :=
    List.dropLast_concat_getLast (by simp)
  rw [h_gl_val] at h_reassemble
  rw [List.cons_append, h_reassemble]

/-- Crux structural equation: destructing the signature arrow chain
    `mkArrow hd (mids ++ tl)` (with `tl` a `destructArrow` output, so its last element is atomic)
    recovers `hd :: mids ++ tl`. The domains `hd`, `mids`, and `tl.dropLast` are kept whole; only
    the final codomain `tl.getLast` is re-destructed, and it's atomic (destructs to itself). -/
private theorem destructArrow_mkArrow_flat (hd : LMonoTy) (mids : LMonoTys) (base : LMonoTy)
    (ks : Lambda.KnownTypes)
    (h_arrow2 : ∀ k, ks.contains { name := "arrow", metadata := k } = true → k = 2)
    (h_ki_base : LMonoTy.knownInstance base ks = true) :
    (LMonoTy.mkArrow hd (mids ++ base.destructArrow)).destructArrow
      = hd :: (mids ++ base.destructArrow) := by
  -- `tl := mids ++ base.destructArrow` is nonempty (base.destructArrow ≠ []).
  have h_tl_ne : mids ++ base.destructArrow ≠ [] := by
    intro h_eq
    exact absurd (List.append_eq_nil_iff.mp h_eq).2 (LMonoTy.destructArrow_non_empty base)
  -- Peel with destructArrow_mkArrow_cons: need tl in `x :: xs` form.
  obtain ⟨x, xs, h_xxs⟩ : ∃ x xs, mids ++ base.destructArrow = x :: xs := by
    cases h_c : mids ++ base.destructArrow with
    | nil => exact absurd h_c h_tl_ne
    | cons a as => exact ⟨a, as, rfl⟩
  -- The last element `u` of `x::xs` (= mids ++ base.destructArrow) comes from base.destructArrow's
  -- last, hence is atomic. Get it via getLast? to avoid dependent getLast proofs.
  have h_base_ne := LMonoTy.destructArrow_non_empty base
  obtain ⟨u, h_u⟩ : ∃ u, base.destructArrow.getLast? = some u := by
    cases h_g : base.destructArrow.getLast? with
    | none => exact absurd (List.getLast?_eq_none_iff.mp h_g) h_base_ne
    | some u => exact ⟨u, rfl⟩
  have h_xxs_gl : (x :: xs).getLast? = some u := by
    rw [← h_xxs, List.getLast?_append, h_u, Option.some_or]
  have h_gl_val : (x :: xs).getLast (by simp) = u := by
    have h_e := List.getLast?_eq_some_getLast (l := x :: xs) (by simp)
    rw [h_xxs_gl] at h_e; injection h_e with h; exact h.symm
  have h_u_atomic : u.destructArrow = [u] :=
    (getLast?_destructArrow_atomic ks h_arrow2 (icSize base)).1 base (Nat.le_refl _) h_ki_base u h_u
  rw [h_xxs, destructArrow_mkArrow_cons, h_gl_val, h_u_atomic]
  -- (hd :: (x::xs).dropLast) ++ [u] = hd :: (x :: xs), where u = (x::xs).getLast
  have h_reassemble : (x :: xs).dropLast ++ [(x :: xs).getLast (by simp)] = x :: xs :=
    List.dropLast_concat_getLast (by simp)
  rw [h_gl_val] at h_reassemble
  rw [List.cons_append, h_reassemble]

/-- When `"arrow"` is not an alias name, `tconsAliasSimple "arrow" args aliases = tcons "arrow" args`
    (no alias matches, so the raw tcons is returned). -/
private theorem tconsAliasSimple_arrow_not_alias (args : LMonoTys) (aliases : List TypeAlias)
    (h_na : ∀ a ∈ aliases, a.name ≠ "arrow") :
    LMonoTy.tconsAliasSimple "arrow" args aliases = LMonoTy.tcons "arrow" args := by
  simp only [LMonoTy.tconsAliasSimple]
  have h_none : aliases.find? (fun a => a.name == "arrow" && a.typeArgs.length == args.length) = none := by
    rw [List.find?_eq_none]
    intro a h_a h_match
    simp only [Bool.and_eq_true, beq_iff_eq] at h_match
    exact h_na a h_a h_match.1
  rw [h_none]

/-- Resolving a binary arrow distributes: `resolveAliases (arrow t1 t2) = arrow (resolve t1) (resolve t2)`
    (given `"arrow"` is not aliased). Returns the componentwise results with the (unchanged) env. -/
private theorem resolveAliases_arrow (t1 t2 : LMonoTy) (Env : TEnv Unit) (r : LMonoTy) (Env' : TEnv Unit)
    (h_na : ∀ a ∈ Env.context.aliases, a.name ≠ "arrow")
    (h : LMonoTy.resolveAliases (LMonoTy.arrow t1 t2) Env = .ok (r, Env')) :
    ∃ r1 r2, LMonoTy.resolveAliases t1 Env = .ok (r1, Env)
      ∧ LMonoTy.resolveAliases t2 Env = .ok (r2, Env)
      ∧ r = LMonoTy.arrow r1 r2 := by
  -- arrow t1 t2 = tcons "arrow" [t1, t2]
  rw [show LMonoTy.arrow t1 t2 = LMonoTy.tcons "arrow" [t1, t2] from rfl] at h
  simp only [LMonoTy.resolveAliases, Bind.bind, Except.bind] at h
  elim_err h
  rename_i v1 h_args; obtain ⟨args', Env1⟩ := v1; simp only at h h_args
  -- Resolve the 2-element list [t1, t2] via nested binds.
  simp only [LMonoTys.resolveAliases, Bind.bind, Except.bind] at h_args
  elim_err h_args
  rename_i w1 h_r1; obtain ⟨r1, E1⟩ := w1; simp only at h_args h_r1
  elim_err h_args
  rename_i w2 h_r2; obtain ⟨r2, E2⟩ := w2; simp only at h_args h_r2
  -- h_r2 : (match t2.resolveAliases E1 ...) = .ok (r2, E2); peel it.
  elim_err h_r2
  rename_i w3 h_r2a; obtain ⟨r2a, E3⟩ := w3; simp only at h_r2 h_r2a
  simp only [pure, Except.pure] at h_r2
  rw [Except.ok.injEq, Prod.mk.injEq] at h_r2
  obtain ⟨h_r2list, h_E2⟩ := h_r2
  simp only [pure, Except.pure] at h_args
  rw [Except.ok.injEq, Prod.mk.injEq] at h_args
  obtain ⟨h_args1, h_env1⟩ := h_args
  have hE1 : E1 = Env := LMonoTy.resolveAliases_env t1 Env r1 E1 h_r1
  have hE3 : E3 = E1 := LMonoTy.resolveAliases_env t2 E1 r2a E3 h_r2a
  -- Chain env equalities: E3 = E1 = Env; E2 = E3; Env1 = E2.  (h_env1 : E2 = Env1)
  subst hE1; subst hE3
  subst h_E2      -- E2 := Env
  subst h_env1    -- Env1 := Env
  -- args' = r1 :: r2 = r1 :: [r2a] = [r1, r2a]
  rw [← h_r2list] at h_args1
  rw [← h_args1] at h
  rw [tconsAliasSimple_arrow_not_alias _ _ h_na] at h
  simp only [pure, Except.pure] at h
  rw [Except.ok.injEq, Prod.mk.injEq] at h
  exact ⟨r1, r2a, h_r1, h_r2a, by rw [← h.1]; rfl⟩

/-- Resolving `mkArrow hd tl` distributes: the result is `mkArrow (resolve hd) (resolve-each tl)`
    (given `"arrow"` not aliased). The env is unchanged. Proved by induction on `tl`. -/
private theorem resolveAliases_mkArrow (hd : LMonoTy) (tl : LMonoTys) (Env : TEnv Unit)
    (r : LMonoTy) (Env' : TEnv Unit)
    (h_na : ∀ a ∈ Env.context.aliases, a.name ≠ "arrow")
    (h : LMonoTy.resolveAliases (LMonoTy.mkArrow hd tl) Env = .ok (r, Env')) :
    ∃ rhd rtl, LMonoTy.resolveAliases hd Env = .ok (rhd, Env)
      ∧ LMonoTys.resolveAliases tl Env = .ok (rtl, Env)
      ∧ r = LMonoTy.mkArrow rhd rtl := by
  induction tl generalizing hd r Env' with
  | nil =>
    -- mkArrow hd [] = hd
    have h_mk : LMonoTy.mkArrow hd [] = hd := by simp only [LMonoTy.mkArrow]
    rw [h_mk] at h
    have h_env : Env' = Env := LMonoTy.resolveAliases_env hd Env r Env' h
    subst h_env
    exact ⟨r, [], h, by simp only [LMonoTys.resolveAliases, pure, Except.pure], by
      simp only [LMonoTy.mkArrow]⟩
  | cons x xs ih =>
    -- mkArrow hd (x :: xs) = arrow hd (mkArrow x xs)
    have h_mk : LMonoTy.mkArrow hd (x :: xs) = LMonoTy.arrow hd (LMonoTy.mkArrow x xs) := by
      simp only [LMonoTy.mkArrow]
    rw [h_mk] at h
    obtain ⟨r1, r2, h_r1, h_r2, h_req⟩ := resolveAliases_arrow hd (LMonoTy.mkArrow x xs) Env r Env' h_na h
    -- recurse on mkArrow x xs (env is Env, unchanged)
    obtain ⟨rx, rxs, h_rx, h_rxs, h_r2eq⟩ := ih x r2 Env h_r2
    refine ⟨r1, rx :: rxs, h_r1, ?_, ?_⟩
    · -- resolve (x :: xs) = rx :: rxs
      simp only [LMonoTys.resolveAliases, Bind.bind, Except.bind, h_rx, h_rxs, pure, Except.pure]
    · rw [h_req, h_r2eq]; simp only [LMonoTy.mkArrow]

/-- Resolving a list distributes over append: `resolveAliases (as ++ bs) = resolve as ++ resolve bs`
    (env unchanged throughout). Proved by induction on `as`. -/
private theorem resolveAliasesList_append (as bs : LMonoTys) (Env : TEnv Unit)
    (rab : LMonoTys) (Env' : TEnv Unit)
    (h : LMonoTys.resolveAliases (as ++ bs) Env = .ok (rab, Env')) :
    ∃ ras rbs, LMonoTys.resolveAliases as Env = .ok (ras, Env)
      ∧ LMonoTys.resolveAliases bs Env = .ok (rbs, Env)
      ∧ rab = ras ++ rbs := by
  induction as generalizing rab Env' with
  | nil =>
    rw [List.nil_append] at h
    have h_env : Env' = Env := LMonoTys.resolveAliases_env bs Env rab Env' h
    subst h_env
    exact ⟨[], rab, by simp only [LMonoTys.resolveAliases, pure, Except.pure], h, by rw [List.nil_append]⟩
  | cons a as ih =>
    rw [List.cons_append] at h
    -- resolve (a :: (as ++ bs)) = ra :: r_rest
    simp only [LMonoTys.resolveAliases, Bind.bind, Except.bind] at h
    elim_err h
    rename_i v1 h_a; obtain ⟨ra, E1⟩ := v1; simp only at h h_a
    elim_err h
    rename_i v2 h_rest; obtain ⟨rrest, E2⟩ := v2; simp only at h h_rest
    simp only [pure, Except.pure] at h
    rw [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨h_rab, h_env⟩ := h
    have hE1 : E1 = Env := LMonoTy.resolveAliases_env a Env ra E1 h_a
    subst hE1
    obtain ⟨ras, rbs, h_ras, h_rbs, h_split⟩ := ih rrest E2 h_rest
    refine ⟨ra :: ras, rbs, ?_, h_rbs, ?_⟩
    · simp only [LMonoTys.resolveAliases, Bind.bind, Except.bind, h_a, h_ras, pure, Except.pure]
    · rw [← h_rab, h_split, List.cons_append]

/-- An ftvar-renaming `ρ` preserves `knownInstance`: substituting variables for variables does not
    change any `tcons` head/arity, and `ftvar`/`bitvec` are always known instances. -/
private theorem knownInstance_subst_renaming (ρ : Subst) (ks : Lambda.KnownTypes)
    (h_ρ_ftvar : ∀ mty ∈ Maps.values ρ, ∃ w, mty = LMonoTy.ftvar w) (n : Nat) :
    (∀ (mty : LMonoTy), icSize mty ≤ n →
      LMonoTy.knownInstance mty ks = true → LMonoTy.knownInstance (LMonoTy.subst ρ mty) ks = true) ∧
    (∀ (mtys : LMonoTys), icSizes mtys ≤ n →
      LMonoTys.knownInstances mtys ks = true →
        LMonoTys.knownInstances (LMonoTys.subst ρ mtys) ks = true) := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
  refine ⟨?_, ?_⟩
  · intro mty h_sz h_ki
    match mty with
    | .ftvar x =>
      obtain ⟨w, h_w⟩ := subst_ftvar_is_ftvar ρ h_ρ_ftvar x
      rw [h_w]; simp only [LMonoTy.knownInstance]
    | .bitvec k => rw [LMonoTy.subst_bitvec]; simp only [LMonoTy.knownInstance]
    | .tcons name args =>
      rw [LMonoTy.subst_tcons]
      simp only [LMonoTy.knownInstance, Bool.and_eq_true] at h_ki ⊢
      obtain ⟨h_contains, h_ki_args⟩ := h_ki
      have h_args_sz : icSizes args < n := by simp only [icSize] at h_sz; omega
      refine ⟨?_, ?_⟩
      · -- subst preserves the arg-list length, so the arity lookup is unchanged.
        rwa [show (LMonoTys.subst ρ args).length = args.length from by
          rw [subst_list_eq_map, List.length_map]]
      · exact (ih (icSizes args) h_args_sz).2 args (Nat.le_refl _) h_ki_args
  · intro mtys h_sz h_ki
    match mtys with
    | [] => simp only [LMonoTys.subst_nil, LMonoTys.knownInstances]
    | mty :: mrest =>
      rw [subst_cons_eq']
      simp only [LMonoTys.knownInstances] at h_ki ⊢
      have h_mty_sz : icSize mty < n := by simp only [icSizes] at h_sz; omega
      have h_mrest_sz : icSizes mrest < n := by simp only [icSizes] at h_sz; omega
      split at h_ki
      · rename_i h_ki_mty
        rw [(ih (icSize mty) h_mty_sz).1 mty (Nat.le_refl _) h_ki_mty]
        exact (ih (icSizes mrest) h_mrest_sz).2 mrest (Nat.le_refl _) h_ki
      · exact absurd h_ki (by simp)

/-- `LMonoTys.resolveAliases` preserves list length. -/
private theorem resolveAliasesList_length (mtys : LMonoTys) (Env : TEnv Unit)
    (rs : LMonoTys) (Env' : TEnv Unit)
    (h : LMonoTys.resolveAliases mtys Env = .ok (rs, Env')) :
    rs.length = mtys.length := by
  induction mtys generalizing rs Env' Env with
  | nil =>
    simp only [LMonoTys.resolveAliases, pure, Except.pure] at h
    rw [Except.ok.injEq, Prod.mk.injEq] at h; rw [h.1]
  | cons a as ih =>
    simp only [LMonoTys.resolveAliases, Bind.bind, Except.bind] at h
    elim_err h
    rename_i v1 h_a; obtain ⟨ra, E1⟩ := v1; simp only at h h_a
    elim_err h
    rename_i v2 h_rest; obtain ⟨rrest, E2⟩ := v2; simp only at h h_rest
    simp only [pure, Except.pure] at h
    rw [Except.ok.injEq, Prod.mk.injEq] at h
    rw [← h.1, List.length_cons, List.length_cons, ih E1 rrest E2 h_rest]

/-- `knownInstance ⇒ arrowsBinary`: with `"arrow"` registered at arity 2 (`h_arrow2`), a known
    instance has every arrow node binary. -/
private theorem arrowsBinary_of_knownInstance (ks : Lambda.KnownTypes)
    (h_arrow2 : ∀ k, ks.contains { name := "arrow", metadata := k } = true → k = 2) (n : Nat) :
    (∀ (mty : LMonoTy), icSize mty ≤ n → LMonoTy.knownInstance mty ks = true →
      LMonoTy.arrowsBinary mty = true) ∧
    (∀ (mtys : LMonoTys), icSizes mtys ≤ n → LMonoTys.knownInstances mtys ks = true →
      LMonoTys.arrowsBinary mtys = true) := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
  refine ⟨?_, ?_⟩
  · intro mty h_sz h_ki
    match mty with
    | .ftvar _ => simp only [LMonoTy.arrowsBinary]
    | .bitvec _ => simp only [LMonoTy.arrowsBinary]
    | .tcons name args =>
      simp only [LMonoTy.knownInstance, Bool.and_eq_true] at h_ki
      obtain ⟨h_contains, h_ki_args⟩ := h_ki
      have h_args_sz : icSizes args < n := by simp only [icSize] at h_sz; omega
      simp only [LMonoTy.arrowsBinary, Bool.and_eq_true]
      refine ⟨?_, (ih (icSizes args) h_args_sz).2 args (Nat.le_refl _) h_ki_args⟩
      by_cases h_ar : name = "arrow"
      · subst h_ar
        simp only [if_pos, beq_iff_eq]
        exact h_arrow2 args.length h_contains
      · simp only [if_neg h_ar]
  · intro mtys h_sz h_ki
    match mtys with
    | [] => simp only [LMonoTys.arrowsBinary]
    | mty :: mrest =>
      simp only [LMonoTys.knownInstances] at h_ki
      have h_mty_sz : icSize mty < n := by simp only [icSizes] at h_sz; omega
      have h_mrest_sz : icSizes mrest < n := by simp only [icSizes] at h_sz; omega
      simp only [LMonoTys.arrowsBinary, Bool.and_eq_true]
      split at h_ki
      · rename_i h_m
        exact ⟨(ih (icSize mty) h_mty_sz).1 mty (Nat.le_refl _) h_m,
               (ih (icSizes mrest) h_mrest_sz).2 mrest (Nat.le_refl _) h_ki⟩
      · exact absurd h_ki (by simp)

/-- `arrowsBinary (mkArrow hd tl) ⇒ arrowsBinary` of every element of `tl` (and of `hd`). The
    domains `hd`, `tl` (except the last) are kept whole inside the arrow, so binary-ness propagates. -/
private theorem arrowsBinary_mkArrow_mem (hd : LMonoTy) (tl : LMonoTys)
    (h : LMonoTy.arrowsBinary (LMonoTy.mkArrow hd tl) = true) :
    LMonoTy.arrowsBinary hd = true ∧ ∀ x ∈ tl, LMonoTy.arrowsBinary x = true := by
  induction tl generalizing hd with
  | nil =>
    refine ⟨?_, by simp⟩
    simpa only [LMonoTy.mkArrow] using h
  | cons a as ih =>
    rw [show LMonoTy.mkArrow hd (a :: as) = LMonoTy.arrow hd (LMonoTy.mkArrow a as) from rfl,
      show LMonoTy.arrow hd (LMonoTy.mkArrow a as)
        = LMonoTy.tcons "arrow" [hd, LMonoTy.mkArrow a as] from rfl] at h
    simp only [LMonoTy.arrowsBinary, LMonoTys.arrowsBinary, if_pos, beq_iff_eq,
      Bool.and_eq_true] at h
    obtain ⟨_, h_hd, h_rec, _⟩ := h
    obtain ⟨h_a, h_as⟩ := ih a h_rec
    refine ⟨h_hd, ?_⟩
    intro x hx
    rcases List.mem_cons.mp hx with h_eq | h_mem
    · subst h_eq; exact h_a
    · exact h_as x h_mem

/-- Re-association of `mkArrow'` over an append of the argument list.
`mkArrow' ret (as ++ bs) = mkArrow' (mkArrow' ret bs) as`. -/
private theorem mkArrow'_append (ret : LMonoTy) (as bs : LMonoTys) :
    LMonoTy.mkArrow' ret (as ++ bs) = LMonoTy.mkArrow' (LMonoTy.mkArrow' ret bs) as := by
  induction as with
  | nil => simp only [List.nil_append, LMonoTy.mkArrow'_nil]
  | cons a as ih => rw [List.cons_append, LMonoTy.mkArrow'_cons, LMonoTy.mkArrow'_cons, ih]

/-- `mkArrow` with a snoc tail equals `mkArrow'` with the last element as the return type and
the head prepended to the initial segment. `mkArrow hd (init ++ [last]) = mkArrow' last (hd :: init)`. -/
private theorem mkArrow_snoc_eq_mkArrow' (hd : LMonoTy) (init : LMonoTys) (last : LMonoTy) :
    LMonoTy.mkArrow hd (init ++ [last]) = LMonoTy.mkArrow' last (hd :: init) := by
  induction init generalizing hd with
  | nil =>
    show LMonoTy.mkArrow hd [last] = LMonoTy.mkArrow' last [hd]
    rw [show LMonoTy.mkArrow hd [last] = LMonoTy.arrow hd (LMonoTy.mkArrow last []) from rfl,
      show LMonoTy.mkArrow last [] = last from rfl, LMonoTy.mkArrow'_cons, LMonoTy.mkArrow'_nil]
  | cons a as ih =>
    show LMonoTy.mkArrow hd (a :: (as ++ [last])) = _
    rw [show LMonoTy.mkArrow hd (a :: (as ++ [last]))
        = LMonoTy.arrow hd (LMonoTy.mkArrow a (as ++ [last])) from rfl, ih a]
    simp only [LMonoTy.mkArrow'_cons]

/-- Forward construction: resolving `mkArrow' ret args` succeeds with `mkArrow'` of the resolved
components, given the components resolve (env unchanged) and `"arrow"` is not aliased. -/
private theorem resolveAliases_mkArrow'_ok (ret : LMonoTy) (args : LMonoTys) (Env : TEnv Unit)
    (rret : LMonoTy) (rargs : LMonoTys)
    (h_na : ∀ a ∈ Env.context.aliases, a.name ≠ "arrow")
    (h_ret : LMonoTy.resolveAliases ret Env = .ok (rret, Env))
    (h_args : LMonoTys.resolveAliases args Env = .ok (rargs, Env)) :
    LMonoTy.resolveAliases (LMonoTy.mkArrow' ret args) Env
      = .ok (LMonoTy.mkArrow' rret rargs, Env) := by
  induction args generalizing rargs with
  | nil =>
    simp only [LMonoTys.resolveAliases, pure, Except.pure] at h_args
    rw [Except.ok.injEq, Prod.mk.injEq] at h_args
    rw [LMonoTy.mkArrow'_nil, ← h_args.1, LMonoTy.mkArrow'_nil]
    exact h_ret
  | cons a as ih =>
    -- Peel resolve of (a :: as): resolve a = ra, resolve as = ras, rargs = ra :: ras.
    simp only [LMonoTys.resolveAliases, Bind.bind, Except.bind] at h_args
    elim_err h_args
    rename_i v1 h_a; obtain ⟨ra, E1⟩ := v1; simp only at h_args h_a
    elim_err h_args
    rename_i v2 h_as; obtain ⟨ras, E2⟩ := v2; simp only at h_args h_as
    simp only [pure, Except.pure] at h_args
    rw [Except.ok.injEq, Prod.mk.injEq] at h_args
    obtain ⟨h_rargs, h_env⟩ := h_args
    have hE1 : E1 = Env := LMonoTy.resolveAliases_env a Env ra E1 h_a
    rw [hE1] at h_a h_as
    rw [h_env] at h_as
    -- ih on the tail: resolve (mkArrow' ret as) Env = ok (mkArrow' rret ras, Env).
    have h_M := ih ras h_as
    -- mkArrow' ret (a :: as) = arrow a (mkArrow' ret as) = tcons "arrow" [a, mkArrow' ret as].
    rw [LMonoTy.mkArrow'_cons,
      show LMonoTy.arrow a (LMonoTy.mkArrow' ret as) = LMonoTy.tcons "arrow" [a, LMonoTy.mkArrow' ret as] from rfl]
    -- Resolve the tcons: resolve-list [a, mkArrow' ret as] then tconsAliasSimple.
    simp only [LMonoTy.resolveAliases, LMonoTys.resolveAliases, Bind.bind, Except.bind,
      h_a, h_M, pure, Except.pure]
    rw [tconsAliasSimple_arrow_not_alias _ _ h_na,
      show LMonoTy.tcons "arrow" [ra, LMonoTy.mkArrow' rret ras]
        = LMonoTy.arrow ra (LMonoTy.mkArrow' rret ras) from rfl,
      ← LMonoTy.mkArrow'_cons, ← h_rargs]

theorem Function.typeCheck_inverse_components (C : LContext CoreLParams) (Env : TEnv Unit)
    (func : Function) (type : LTy) (v_inst : LMonoTy × TEnv Unit) (ρ : Subst) (Env_r : TEnv Unit)
    (h_type : LFunc.type func = .ok type)
    (h_ra : LMonoTy.resolveAliases (LTy.toMonoTypeUnsafe type) Env
      = .ok (LMonoTy.subst ρ v_inst.fst, Env_r))
    (h_aw : TContext.AliasesWF Env.context)
    (h_aliases_not_known : ∀ a ∈ Env.context.aliases, a.name ≠ "arrow")
    -- `ρ` is a variable renaming (every range value is a `.ftvar`), so `subst ρ` preserves
    -- `destructArrow` shape.
    (h_ρ_ftvar : ∀ mty ∈ Maps.values ρ, ∃ w, mty = LMonoTy.ftvar w)
    -- `"arrow"` is a known type at arity 2 (context well-formedness; true of `KnownTypes.default`
    -- and any extending context), so every arrow node is binary.
    (h_arrow_wf : ArrowKnownBinary C)
    -- `v_inst.fst` is an instance of a known type (recursive arity check).
    (h_known : LMonoTy.knownInstance v_inst.fst C.knownTypes = true) :
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
  -- Derive the `∀ k` arity form from the named well-formedness hypothesis.
  have h_arrow2 := h_arrow_wf.arrow_arity_eq_two
  -- SIG = toMonoTypeUnsafe type.  From h_type, `type = .forAll typeArgs sigBody` where
  -- sigBody is either func.output (no inputs) or mkArrow ity (irest ++ destructArrow output).
  simp only [LFunc.type, bind, Except.bind] at h_type
  split at h_type
  · contradiction
  split at h_type
  · contradiction
  -- New arrowsBinary guard: in the success branch, the guard condition holds.
  split at h_type
  · contradiction
  rename_i h_iv_dup h_ta_dup h_arrows
  -- h_arrows : ¬ (!(func.output.arrowsBinary && LMonoTys.arrowsBinary func.inputs.values)) = true
  have h_out_binary : func.output.arrowsBinary = true := by
    simp only [Bool.not_eq_true', Bool.not_eq_false, Bool.and_eq_true] at h_arrows
    exact h_arrows.1
  simp only [pure, Except.pure] at h_type
  -- Now split on inputs.values shape
  -- First: inputs.keys.length = inputs.values.length
  have h_len : func.inputs.keys.length = func.inputs.values.length := by
    rw [ListMap.keys_eq_map_fst, ListMap.values_eq_map_snd, List.length_map, List.length_map]
  split at h_type
  · -- inputs.values = []: n = 0, take 0 = [], AliasEquivList over [] is trivial
    rename_i h_iv_nil
    rw [Except.ok.injEq] at h_type
    subst h_type
    -- SIG = toMonoTypeUnsafe (forAll typeArgs func.output) = func.output
    have h_sig : LTy.toMonoTypeUnsafe (LTy.forAll func.typeArgs func.output) = func.output := rfl
    rw [h_sig] at h_ra
    -- n = 0
    have h_n0 : func.inputs.keys.length = 0 := by rw [h_len, h_iv_nil]; rfl
    rw [h_n0]
    simp only [List.take_zero, List.drop_zero]
    refine ⟨?_, ?_⟩
    · -- output: subst ρ (mkArrow' (getLast da / getD) (dropLast da)) ≈ func.output.
      -- `v_inst.fst` roundtrips through its destructArrow spine (binary via `h_known`), so the
      -- reconstruction is `subst ρ v_inst.fst`; `resolveAliases_aliasEquiv` + `h_ra` + symm close it.
      have h_rt : LMonoTy.mkArrow'
          (v_inst.fst.destructArrow.getLast?.getD
            (List.getLast v_inst.fst.destructArrow (LMonoTy.destructArrow_non_empty v_inst.fst)))
          v_inst.fst.destructArrow.dropLast = v_inst.fst :=
        mkArrow'_destructArrow_roundtrip C.knownTypes h_arrow2 _ (icSize v_inst.fst) v_inst.fst
          (Nat.le_refl _) h_known
      rw [h_rt]
      -- resolveAliases gives AliasEquiv func.output (subst ρ v_inst.fst).
      have h_ae : AliasEquiv Env.context.aliases func.output (LMonoTy.subst ρ v_inst.fst) :=
        resolveAliases_aliasEquiv (T := CoreLParams) (Γ := Env.context) func.output Env
          (LMonoTy.subst ρ v_inst.fst) Env_r h_ra rfl h_aw
      exact AliasEquiv.symm h_ae
    · -- inputs: AliasEquivList aliases [] func.inputs.values, and inputs.values = []
      rw [h_iv_nil]; exact .nil
  · -- inputs.values = ity :: irest
    rename_i ity irest h_iv
    rw [Except.ok.injEq] at h_type
    subst h_type
    -- SIG = mkArrow ity (irest ++ func.output.destructArrow).
    have h_sig : LTy.toMonoTypeUnsafe
        (LTy.forAll func.typeArgs (ity.mkArrow (irest ++ func.output.destructArrow)))
        = ity.mkArrow (irest ++ func.output.destructArrow) := rfl
    rw [h_sig] at h_ra
    -- Distribute resolveAliases over the arrow spine (arrow is not aliased).
    obtain ⟨rhd, rtl, h_rhd, h_rtl, h_split⟩ :=
      resolveAliases_mkArrow ity (irest ++ func.output.destructArrow) Env
        (LMonoTy.subst ρ v_inst.fst) Env_r h_aliases_not_known h_ra
    -- Split the resolved tail-list along the append: rtl = r_irest ++ r_outspine.
    obtain ⟨r_irest, r_outspine, h_r_irest, h_r_outspine, h_rtl_split⟩ :=
      resolveAliasesList_append irest func.output.destructArrow Env rtl Env h_rtl
    -- `subst ρ v_inst.fst = mkArrow rhd (r_irest ++ r_outspine)`.
    have h_svfst : LMonoTy.subst ρ v_inst.fst = LMonoTy.mkArrow rhd (r_irest ++ r_outspine) := by
      rw [h_split, h_rtl_split]
    -- The destructArrow spine of `subst ρ v_inst.fst` = map (subst ρ) da.
    have h_da_map : LMonoTy.destructArrow (LMonoTy.subst ρ v_inst.fst)
        = v_inst.fst.destructArrow.map (LMonoTy.subst ρ) :=
      destructArrow_subst ρ h_ρ_ftvar v_inst.fst
    -- Also, knownInstance of `subst ρ v_inst.fst` (ρ is a renaming).
    have h_known_subst : LMonoTy.knownInstance (LMonoTy.subst ρ v_inst.fst) C.knownTypes = true :=
      (knownInstance_subst_renaming ρ C.knownTypes h_ρ_ftvar (icSize v_inst.fst)).1
        v_inst.fst (Nat.le_refl _) h_known
    -- `r_outspine` is nonempty (resolve preserves length; `output.destructArrow` nonempty).
    have h_ros_ne : r_outspine ≠ [] := by
      intro h_eq
      have h_len_os := resolveAliasesList_length func.output.destructArrow Env r_outspine Env h_r_outspine
      rw [h_eq, List.length_nil] at h_len_os
      exact absurd (List.eq_nil_of_length_eq_zero h_len_os.symm) (LMonoTy.destructArrow_non_empty func.output)
    -- Length facts: n = (ity::irest).length = 1 + irest.length = 1 + r_irest.length.
    have h_rirest_len : r_irest.length = irest.length :=
      resolveAliasesList_length irest Env r_irest Env h_r_irest
    have h_n : func.inputs.keys.length = 1 + irest.length := by
      rw [h_len, h_iv]; simp only [List.length_cons]; omega
    have h_tail_ne : r_irest ++ r_outspine ≠ [] :=
      fun h => absurd (List.append_eq_nil_iff.mp h).2 h_ros_ne
    have h_dropLast : (r_irest ++ r_outspine).dropLast = r_irest ++ r_outspine.dropLast :=
      List.dropLast_append_of_ne_nil h_ros_ne
    -- Split `r_outspine = r_od ++ [r_ol]` to peel the spine without a dependent `getLast`.
    obtain ⟨r_od, r_ol, h_ros_split⟩ : ∃ r_od r_ol, r_outspine = r_od ++ [r_ol] :=
      ⟨r_outspine.dropLast, r_outspine.getLast h_ros_ne, (List.dropLast_concat_getLast h_ros_ne).symm⟩
    -- spine = destructArrow (mkArrow rhd (r_irest ++ r_od ++ [r_ol]))
    --       = rhd :: (r_irest ++ r_od) ++ destructArrow r_ol   (via destructArrow_mkArrow' style)
    have h_spine : v_inst.fst.destructArrow.map (LMonoTy.subst ρ)
        = (rhd :: (r_irest ++ r_od)) ++ r_ol.destructArrow := by
      rw [← h_da_map, h_svfst, h_ros_split]
      -- mkArrow rhd (r_irest ++ (r_od ++ [r_ol])) = mkArrow' r_ol (rhd :: (r_irest ++ r_od))?  No.
      -- Use destructArrow_mkArrow_cons-based full peel: prove by the mkArrow'/destructArrow bridge.
      rw [show r_irest ++ (r_od ++ [r_ol]) = (r_irest ++ r_od) ++ [r_ol] from by
        rw [List.append_assoc]]
      -- mkArrow rhd ((r_irest++r_od) ++ [r_ol]) : destructArrow = rhd :: (r_irest++r_od) ++ destructArrow r_ol
      rw [destructArrow_mkArrow_snoc]
    -- ============ INPUTS conjunct ============
    have h_inputs : Lambda.AliasEquivList Env.context.aliases
        (LMonoTy.subst ρ <$> List.take func.inputs.keys.length v_inst.fst.destructArrow)
        func.inputs.values := by
      have h_take : LMonoTy.subst ρ <$> List.take func.inputs.keys.length v_inst.fst.destructArrow
          = rhd :: r_irest := by
        show List.map (LMonoTy.subst ρ) (List.take func.inputs.keys.length v_inst.fst.destructArrow)
          = rhd :: r_irest
        rw [List.map_take, h_spine]
        -- take (1 + irest.length) ((rhd :: (r_irest ++ r_od)) ++ r_ol.destructArrow)
        rw [h_n, List.take_append_of_le_length (by
          simp only [List.length_cons, List.length_append]; omega)]
        rw [List.take_cons (by omega)]
        congr 1
        rw [List.take_append_of_le_length (by omega), List.take_of_length_le (by omega)]
      rw [h_take, h_iv]
      have h_ael : Lambda.AliasEquivList Env.context.aliases (ity :: irest) (rhd :: r_irest) :=
        .cons (resolveAliases_aliasEquiv (T := CoreLParams) (Γ := Env.context) ity Env rhd Env h_rhd rfl h_aw)
          (resolveAliasList_aliasEquiv (T := CoreLParams) (Γ := Env.context) irest Env r_irest Env h_r_irest rfl h_aw)
      exact AliasEquivList.symm h_ael
    -- ============ OUTPUT conjunct ============
    refine ⟨?_, h_inputs⟩
    -- func.output ROUNDTRIPS (arrowsBinary from the LFunc.type guard): mkArrow' (getLast? od) (dropLast od) = output.
    have h_out_rt : LMonoTy.mkArrow'
        (func.output.destructArrow.getLast?.getD
          (func.output.destructArrow.getLast (LMonoTy.destructArrow_non_empty func.output)))
        func.output.destructArrow.dropLast = func.output :=
      mkArrow'_destructArrow_roundtrip_binary _ (icSize func.output) func.output (Nat.le_refl _) h_out_binary
    -- destructArrow func.output = r's preimage: split it as `od_init ++ [od_last]`.
    have h_od_ne := LMonoTy.destructArrow_non_empty func.output
    obtain ⟨od_init, od_last, h_od_split⟩ : ∃ od_init od_last, func.output.destructArrow = od_init ++ [od_last] :=
      ⟨func.output.destructArrow.dropLast, func.output.destructArrow.getLast h_od_ne,
        (List.dropLast_concat_getLast h_od_ne).symm⟩
    -- Resolve func.output's spine list: `h_r_outspine : resolve (output.destructArrow) = (r_outspine, Env)`.
    -- Split it along `od_init ++ [od_last]` = `r_od ++ [r_ol]` (both equal r_outspine).
    have h_ros_eq : r_outspine = r_od ++ [r_ol] := h_ros_split
    -- resolve (od_init ++ [od_last]) = r_od ++ [r_ol], so resolve od_init = r_od, resolve [od_last] = [r_ol].
    have h_r_out_spine' : LMonoTys.resolveAliases (od_init ++ [od_last]) Env = .ok (r_od ++ [r_ol], Env) := by
      rw [← h_od_split, ← h_ros_eq]; exact h_r_outspine
    obtain ⟨r_odi, r_oll, h_r_odi, h_r_oll, h_ros_app⟩ :=
      resolveAliasesList_append od_init [od_last] Env (r_od ++ [r_ol]) Env h_r_out_spine'
    -- resolve [od_last] = r_oll (a singleton), so resolve od_last = its head.
    obtain ⟨r_odlast, h_r_odlast, h_oll_eq⟩ : ∃ r_odlast, LMonoTy.resolveAliases od_last Env = .ok (r_odlast, Env)
        ∧ r_oll = [r_odlast] := by
      simp only [LMonoTys.resolveAliases, Bind.bind, Except.bind] at h_r_oll
      elim_err h_r_oll
      rename_i w1 h_w1; obtain ⟨rl, El⟩ := w1; simp only at h_r_oll h_w1
      simp only [pure, Except.pure] at h_r_oll
      rw [Except.ok.injEq, Prod.mk.injEq] at h_r_oll
      have hEl : El = Env := LMonoTy.resolveAliases_env od_last Env rl El h_w1
      subst hEl
      exact ⟨rl, h_w1, h_r_oll.1.symm⟩
    -- Resolve func.output as a whole: rewrite via roundtrip to mkArrow' od_last od_init, then
    -- resolveAliases_mkArrow'_ok gives resolve = mkArrow' r_odlast r_odi.
    have h_out_split_rt : func.output = LMonoTy.mkArrow' od_last od_init := by
      -- getLast? (destructArrow func.output) = some od_last (non-dependent, via the split).
      have h_gl? : func.output.destructArrow.getLast? = some od_last := by
        rw [h_od_split, List.getLast?_append]
        simp only [List.getLast?_singleton, Option.some_or]
      have h_gl : func.output.destructArrow.getLast?.getD
          (func.output.destructArrow.getLast h_od_ne) = od_last := by
        rw [h_gl?, Option.getD_some]
      have h_dl : func.output.destructArrow.dropLast = od_init := by
        rw [h_od_split, List.dropLast_concat]
      -- h_out_rt with the two rewrites gives mkArrow' od_last od_init = func.output.
      rw [h_gl, h_dl] at h_out_rt
      exact h_out_rt.symm
    have h_r_out : LMonoTy.resolveAliases func.output Env = .ok (LMonoTy.mkArrow' r_odlast r_odi, Env) := by
      rw [h_out_split_rt]
      exact resolveAliases_mkArrow'_ok od_last od_init Env r_odlast r_odi h_aliases_not_known h_r_odlast h_r_odi
    have h_ae_out : AliasEquiv Env.context.aliases func.output (LMonoTy.mkArrow' r_odlast r_odi) :=
      resolveAliases_aliasEquiv (T := CoreLParams) (Γ := Env.context) func.output Env
        (LMonoTy.mkArrow' r_odlast r_odi) Env h_r_out rfl h_aw
    -- GOAL: AliasEquiv aliases (subst ρ (mkArrow' R DL)) func.output. Show LHS = mkArrow' r_odlast r_odi.
    -- First: r_od = r_odi and [r_ol] = [r_odlast] from the append split (lengths match).
    have h_r_odi_len : r_odi.length = od_init.length := resolveAliasesList_length od_init Env r_odi Env h_r_odi
    have h_r_od_len : r_od.length = od_init.length := by
      have := resolveAliasesList_length od_init Env r_od Env
      -- from h_ros_app : r_od ++ [r_ol] = r_odi ++ r_oll, and h_oll_eq : r_oll = [r_odlast]
      rw [h_oll_eq] at h_ros_app
      have h_len_eq : (r_od ++ [r_ol]).length = (r_odi ++ [r_odlast]).length := by rw [h_ros_app]
      simp only [List.length_append, List.length_cons, List.length_nil] at h_len_eq
      omega
    have h_od_eq : r_od = r_odi ∧ r_ol = r_odlast := by
      rw [h_oll_eq] at h_ros_app
      have h := List.append_inj h_ros_app (by rw [h_r_od_len, h_r_odi_len])
      exact ⟨h.1, by have := h.2; simpa using this⟩
    -- `drop n` of the spine peels `rhd :: r_irest` (n = 1 + r_irest.length), leaving the output spine.
    have h_drop : LMonoTy.subst ρ <$> (List.drop func.inputs.keys.length v_inst.fst.destructArrow)
        = r_od ++ r_ol.destructArrow := by
      show List.map (LMonoTy.subst ρ) (List.drop func.inputs.keys.length v_inst.fst.destructArrow) = _
      rw [List.map_drop, h_spine, h_n]
      -- drop (1 + irest.length) ((rhd :: (r_irest ++ r_od)) ++ r_ol.destructArrow)
      rw [List.drop_append_of_le_length (by simp only [List.length_cons, List.length_append]; omega)]
      -- drop (1 + irest.length) (rhd :: (r_irest ++ r_od)): peel rhd, then drop irest.length from r_irest.
      rw [show (1 + irest.length) = (irest.length + 1) from by omega]
      rw [List.drop_succ_cons]
      rw [List.drop_append_of_le_length (by omega), List.drop_of_length_le (by omega), List.nil_append]
    -- push subst inside mkArrow' via subst_mkArrow', and move map through getLast?/dropLast.
    have h_recon : LMonoTy.subst ρ
        (((List.drop func.inputs.keys.length v_inst.fst.destructArrow).getLast?.getD
            (List.getLast v_inst.fst.destructArrow (LMonoTy.destructArrow_non_empty v_inst.fst))).mkArrow'
          (List.drop func.inputs.keys.length v_inst.fst.destructArrow).dropLast)
        = LMonoTy.mkArrow' r_odlast r_odi := by
      rw [subst_mkArrow']
      -- `arrowsBinary r_ol`: `r_ol ∈ r_outspine ⊆ (r_irest ++ r_outspine)`, and
      -- `subst ρ v_inst.fst = mkArrow rhd (r_irest ++ r_outspine)` is a known instance.
      have h_ab_svfst : LMonoTy.arrowsBinary (LMonoTy.subst ρ v_inst.fst) = true :=
        (arrowsBinary_of_knownInstance C.knownTypes h_arrow2 (icSize (LMonoTy.subst ρ v_inst.fst))).1
          (LMonoTy.subst ρ v_inst.fst) (Nat.le_refl _) h_known_subst
      have h_ab_tail : ∀ x ∈ (r_irest ++ r_outspine), LMonoTy.arrowsBinary x = true := by
        have h_ab_mk := arrowsBinary_mkArrow_mem rhd (r_irest ++ r_outspine) (h_svfst ▸ h_ab_svfst)
        exact h_ab_mk.2
      have h_ab_rol : LMonoTy.arrowsBinary r_ol = true := by
        apply h_ab_tail
        rw [h_ros_split]
        exact List.mem_append_right _ (by rw [List.mem_append]; right; exact List.mem_singleton_self _)
      -- Move `map subst` through getLast?/dropLast, then use h_drop.
      -- First arg: subst ρ (getLast?.getD (drop) default) = (map subst (drop)).getLast?.getD (subst default).
      have h_arg1 : LMonoTy.subst ρ
          ((List.drop func.inputs.keys.length v_inst.fst.destructArrow).getLast?.getD
            (List.getLast v_inst.fst.destructArrow (LMonoTy.destructArrow_non_empty v_inst.fst)))
          = (List.map (LMonoTy.subst ρ)
              (List.drop func.inputs.keys.length v_inst.fst.destructArrow)).getLast?.getD
            (LMonoTy.subst ρ (List.getLast v_inst.fst.destructArrow (LMonoTy.destructArrow_non_empty v_inst.fst))) := by
        rw [List.getLast?_map]
        cases h_g : (List.drop func.inputs.keys.length v_inst.fst.destructArrow).getLast? with
        | none => simp only [Option.getD_none, Option.map_none]
        | some w => simp only [Option.getD_some, Option.map_some]
      have h_drop' : List.map (LMonoTy.subst ρ) (List.drop func.inputs.keys.length v_inst.fst.destructArrow)
          = r_od ++ r_ol.destructArrow := h_drop
      rw [h_arg1, List.map_dropLast, h_drop']
      -- Now goal over `r_od ++ r_ol.destructArrow`. getLast?/dropLast of the append (r_ol.da nonempty).
      have h_rol_ne := LMonoTy.destructArrow_non_empty r_ol
      rw [List.getLast?_append, List.dropLast_append_of_ne_nil h_rol_ne]
      -- getLast? (r_od ++ r_ol.da) = r_ol.da.getLast?.or r_od.getLast? = r_ol.da.getLast? (nonempty)
      obtain ⟨u, h_u⟩ : ∃ u, r_ol.destructArrow.getLast? = some u := by
        cases h_g : r_ol.destructArrow.getLast? with
        | none => exact absurd (List.getLast?_eq_none_iff.mp h_g) h_rol_ne
        | some u => exact ⟨u, rfl⟩
      rw [h_u, Option.some_or, Option.getD_some]
      -- LHS = mkArrow' u (r_od ++ r_ol.da.dropLast) = mkArrow' (mkArrow' u r_ol.da.dropLast) r_od.
      rw [mkArrow'_append]
      -- inner mkArrow' u r_ol.da.dropLast = r_ol by roundtrip (arrowsBinary r_ol); u = getLast? r_ol.da.
      have h_rt_rol : LMonoTy.mkArrow' (r_ol.destructArrow.getLast?.getD u) r_ol.destructArrow.dropLast = r_ol :=
        mkArrow'_destructArrow_roundtrip_binary u (icSize r_ol) r_ol (Nat.le_refl _) h_ab_rol
      rw [h_u, Option.getD_some] at h_rt_rol
      rw [h_rt_rol, h_od_eq.1, h_od_eq.2]
    rw [h_recon]
    exact AliasEquiv.symm h_ae_out


end TypeSpec
end Core
