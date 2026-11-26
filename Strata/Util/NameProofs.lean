/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import Strata.Util.Name
public import Std.Data.HashSet.Basic
import all Strata.Util.Name
import Std.Data.HashSet.Lemmas
import Std.Data.String.ToNat
import Strata.Util.StringProps
import Strata.Util.ListUtilsProps

/-!
# Proofs about `Strata.Name.findUnique` and `Strata.Name.freshName`

`findUniqueFast_not_mem` and `findUniqueSlow_not_mem` prove that both the
fast and slow paths return a name not in `usedNames`.  `findUnique_not_mem`
combines them into a single correctness theorem for `findUnique`.

`freshNameBy_not_taken` proves that `freshNameBy` returns a name `taken` rejects when at most
`fuel` names are taken, and `freshName_not_mem` that `freshName` returns a name not in `taken`.
`freshNamesBy_fresh` and `freshNames_fresh` prove the same for several names at once, and that
the names are pairwise distinct.
`freshNames_not_mem`, `freshNames_nodup`, `freshNames_length` and `freshNames_prefix` state
that `freshNames` picks one distinct name per base, outside `taken`, starting with its base.
`startsWith_internalPrefixOf` proves that an internal name starts with the prefix recorded for it.
-/

public section

namespace Strata.Name

/-- `disambiguate` is injective in its suffix when the base name is fixed.
    This follows from `Nat.repr` injectivity, which is not yet available in our
    Lean toolchain. -/
def DisambiguateInjective : Prop :=
  ∀ (baseName : String) (m n : Nat), disambiguate baseName m = disambiguate baseName n → m = n

/-- When `findUniqueFast` returns `some result`, the result is not in `usedNames`. -/
theorem findUniqueFast_not_mem (baseName candidate : String) (suffix : Nat)
    (usedNames : Std.HashSet String) (fuel : Nat) (result : String)
    (h : findUniqueFast baseName candidate suffix usedNames fuel = some result) :
    result ∉ usedNames := by
  induction fuel generalizing candidate suffix with
  | zero =>
    unfold findUniqueFast at h
    split at h
    · simp only [Option.some.injEq] at h; subst h
      rename_i hc; simp only [Bool.not_eq_eq_eq_not, Bool.not_true, Std.HashSet.contains_eq_false_iff_not_mem] at hc
      exact hc
    · simp at h
  | succ n ih =>
    unfold findUniqueFast at h
    split at h
    · simp only [Option.some.injEq] at h; subst h
      rename_i hc; simp only [Bool.not_eq_eq_eq_not, Bool.not_true, Std.HashSet.contains_eq_false_iff_not_mem] at hc
      exact hc
    · exact ih _ _ h

/-- When `findUniqueSlow` returns `some result`, the result is not in `usedSet`. -/
theorem findUniqueSlow_not_mem (baseName candidate : String) (suffix : Nat)
    (usedSet : Std.HashSet String) (remaining : List String) (result : String)
    (h : findUniqueSlow baseName candidate suffix usedSet remaining = some result) :
    result ∉ usedSet := by
  generalize hlen : remaining.length = n at *
  induction n using Nat.strongRecOn generalizing candidate suffix remaining with
  | _ n ih =>
    unfold findUniqueSlow at h
    split at h
    · simp only [Option.some.injEq] at h; subst h
      rename_i hc; simp only [Bool.not_eq_eq_eq_not, Bool.not_true, Std.HashSet.contains_eq_false_iff_not_mem] at hc
      exact hc
    · split at h
      · have : (remaining.erase candidate).length < remaining.length := by grind
        exact ih _ (by omega) _ _ _ h rfl
      · simp at h

/-- The slow path never returns `none` when `remaining` covers `usedSet` and
    `disambiguate` is injective. The invariant tracks that every member of `usedSet`
    is either still in `remaining` or was a previously tried candidate. -/
private theorem findUniqueSlow_ne_none
    (h_inj : DisambiguateInjective)
    (baseName : String) (suffix : Nat)
    (usedSet : Std.HashSet String) (remaining : List String)
    (h_covers : ∀ s, s ∈ usedSet → s ∈ remaining ∨
      ∃ k, k < suffix ∧ s = disambiguate baseName k) :
    findUniqueSlow baseName (disambiguate baseName suffix) (suffix + 1)
      usedSet remaining ≠ none := by
  generalize hlen : remaining.length = n
  induction n using Nat.strongRecOn generalizing suffix remaining with
  | _ n ih =>
    unfold findUniqueSlow
    split
    · simp
    · rename_i h_in_set
      simp only [Bool.not_eq_eq_eq_not, Bool.not_true, Std.HashSet.contains_eq_false_iff_not_mem,
    Decidable.not_not] at h_in_set
      have h_in_rem : disambiguate baseName suffix ∈ remaining := by
        rcases h_covers _ h_in_set with h | ⟨k, hk, heq⟩
        · exact h
        · exact absurd (h_inj _ _ _ heq) (by omega)
      split
      · have h_len : (remaining.erase (disambiguate baseName suffix)).length <
            remaining.length := by grind
        refine ih _ (by omega) (suffix + 1)
          (remaining.erase (disambiguate baseName suffix)) ?_ rfl
        intro s hs
        rcases h_covers s hs with h_in_rem' | ⟨k, hk, heq⟩
        · by_cases heq : s = disambiguate baseName suffix
          · exact Or.inr ⟨suffix, by omega, heq⟩
          · exact Or.inl ((List.mem_erase_of_ne heq).mpr h_in_rem')
        · exact Or.inr ⟨k, by omega, heq⟩
      · exact absurd (List.contains_iff_mem.mpr h_in_rem) ‹_›

/-- `findUnique` returns a name not in `usedNames`, given that `disambiguate` is
    injective in its suffix argument. -/
theorem findUnique_not_mem (h_inj : DisambiguateInjective)
    (baseName : String) (startSuffix : Nat)
    (usedNames : Std.HashSet String) :
    findUnique baseName startSuffix usedNames ∉ usedNames := by
  unfold findUnique
  simp only
  split
  · next hfast => exact findUniqueFast_not_mem _ _ _ _ _ _ hfast
  · next hfast =>
    split
    · next hslow => exact findUniqueSlow_not_mem _ _ _ _ _ _ hslow
    · next hslow =>
      exfalso
      exact findUniqueSlow_ne_none h_inj baseName (startSuffix + 1000000) usedNames
        usedNames.toList (fun s hs => Or.inl (Std.HashSet.mem_toList.mpr hs)) hslow

/-- Suffixing `base` with `_` and a number gives distinct names for distinct numbers. -/
theorem suffix_cand_inj (base : String) :
    ∀ i j : Nat, base ++ "_" ++ toString i = base ++ "_" ++ toString j → i = j := by
  intro i j hij
  rw [String.append_assoc, String.append_assoc, String.append_right_inj,
    String.append_right_inj] at hij
  exact Nat.toString_injective hij

/-- The candidates of `freshNameBy` are distinct. -/
private theorem freshNameBy_cand_inj (base : String) (i j : Nat)
    (h : (if i = 0 then base else base ++ "_" ++ toString i)
      = (if j = 0 then base else base ++ "_" ++ toString j)) : i = j := by
  have hne : ∀ k : Nat, base ≠ base ++ "_" ++ toString k := by
    intro k heq
    have hlen := congrArg String.length heq
    simp only [String.length_append] at hlen
    have hsep : "_".length = 1 := rfl
    omega
  by_cases hi : i = 0 <;> by_cases hj : j = 0 <;> simp only [hi, hj, ite_true, ite_false] at h
  · omega
  · exact absurd h (hne j)
  · exact absurd h.symm (hne i)
  · exact suffix_cand_inj base i j h

/-- `firstUntaken` returns an untaken name, or every candidate it tried is taken. -/
private theorem firstUntaken_cases (taken : String → Bool) (cand : Nat → String) (fuel i : Nat) :
    taken (firstUntaken taken cand fuel i) = false ∨
      ∀ j ≤ fuel, taken (cand (i + j)) = true := by
  induction fuel generalizing i with
  | zero =>
    cases hc : taken (cand i) with
    | false => exact Or.inl (by simp only [firstUntaken]; exact hc)
    | true =>
      refine Or.inr (fun j hj => ?_)
      have hj0 : j = 0 := Nat.le_zero.mp hj
      subst hj0; simpa using hc
  | succ fuel ih =>
    cases hc : taken (cand i) with
    | false => exact Or.inl (by simp only [firstUntaken, hc]; exact hc)
    | true =>
      rcases ih (i + 1) with hl | hr
      · exact Or.inl (by simp only [firstUntaken, hc]; exact hl)
      · refine Or.inr (fun j hj => ?_)
        cases j with
        | zero => simpa using hc
        | succ k =>
          have hk : k ≤ fuel := Nat.le_of_succ_le_succ hj
          have hmem := hr k hk
          rwa [show i + 1 + k = i + (k + 1) by omega] at hmem

/-- With distinct candidates and `fuel` larger than the length of a list `l` that holds every
    taken name, `firstUntaken` returns an untaken name. -/
private theorem firstUntaken_not_taken (taken : String → Bool) (cand : Nat → String)
    (hinj : ∀ i j, cand i = cand j → i = j) (l : List String)
    (hl : ∀ n, taken n = true → n ∈ l) (fuel : Nat) (hfuel : l.length < fuel) (i : Nat) :
    taken (firstUntaken taken cand fuel i) = false := by
  rcases firstUntaken_cases taken cand fuel i with h | h
  · exact h
  · exfalso
    have hnd : ((List.range (fuel + 1)).map (fun j => cand (i + j))).Nodup := by
      refine List.Pairwise.map (R := (· ≠ ·)) _ ?_ List.nodup_range
      intro x y hne heq
      exact hne (by have h_inj := hinj _ _ heq; omega)
    have hsub : ((List.range (fuel + 1)).map (fun j => cand (i + j))) ⊆ l := by
      intro n hn
      simp only [List.mem_map, List.mem_range] at hn
      obtain ⟨j, hj, hjn⟩ := hn
      subst hjn
      exact hl _ (h j (by omega))
    have hle := List.subset_nodup_length hnd hsub
    rw [List.length_map, List.length_range] at hle
    omega

/-- `firstUntaken` returns one of its candidates, from the `i`-th on. -/
private theorem firstUntaken_eq_cand (taken : String → Bool) (cand : Nat → String)
    (fuel i : Nat) : ∃ j, i ≤ j ∧ firstUntaken taken cand fuel i = cand j := by
  induction fuel generalizing i with
  | zero => exact ⟨i, Nat.le_refl i, rfl⟩
  | succ fuel ih =>
    cases hc : taken (cand i) with
    | false =>
      exact ⟨i, Nat.le_refl i, by simp only [firstUntaken, hc, Bool.false_eq_true, ite_false]⟩
    | true =>
      obtain ⟨j, hij, hj⟩ := ih (i + 1)
      exact ⟨j, by omega, by simp only [firstUntaken, hc]; exact hj⟩

/-- When `l` holds every name `taken` accepts and `fuel` is at least its length, `freshNameBy`
    returns a name that is not taken. -/
theorem freshNameBy_not_taken (taken : String → Bool) (fuel : Nat) (base : String)
    (l : List String) (hl : ∀ n, taken n = true → n ∈ l) (hfuel : l.length ≤ fuel) :
    taken (freshNameBy taken fuel base) = false :=
  firstUntaken_not_taken taken _ (freshNameBy_cand_inj base) l hl (fuel + 1)
    (Nat.lt_succ_of_le hfuel) 0

/-- `freshNameBy` extends its base. -/
theorem freshNameBy_prefix (taken : String → Bool) (fuel : Nat) (base : String) :
    ∃ t, freshNameBy taken fuel base = base ++ t := by
  obtain ⟨j, -, hj⟩ := firstUntaken_eq_cand taken
    (fun k => if k = 0 then base else base ++ "_" ++ toString k) (fuel + 1) 0
  unfold freshNameBy
  rw [hj]
  by_cases hz : j = 0
  · have heq : (if j = 0 then base else base ++ "_" ++ toString j) = base ++ "" := by
      simp only [hz, ite_true, String.append_empty]
    exact ⟨"", heq⟩
  · have heq : (if j = 0 then base else base ++ "_" ++ toString j)
        = base ++ ("_" ++ toString j) := by
      simp only [hz, ite_false, String.append_assoc]
    exact ⟨"_" ++ toString j, heq⟩

/-- When `base` is taken, `freshNameBy` returns `base_j` for some `j`. -/
theorem freshNameBy_of_taken (taken : String → Bool) (fuel : Nat) (base : String)
    (htaken : taken base = true) :
    ∃ j : Nat, freshNameBy taken fuel base = base ++ "_" ++ toString j := by
  obtain ⟨j, hij, hj⟩ := firstUntaken_eq_cand taken
    (fun k => if k = 0 then base else base ++ "_" ++ toString k) fuel 1
  refine ⟨j, ?_⟩
  unfold freshNameBy
  simp only [firstUntaken, htaken, ite_true]
  rw [hj]
  have hjne : j ≠ 0 := by omega
  simp only [hjne, ite_false]

/-- When `l` holds every name `taken` accepts and `fuel` is at least its length,
    `freshNamesBy` picks one name per base, distinct, not taken, and each extending a base. -/
theorem freshNamesBy_spec (bases : List String) :
    ∀ (taken : String → Bool) (fuel : Nat) (l : List String),
      (∀ n, taken n = true → n ∈ l) → l.length ≤ fuel →
      (freshNamesBy taken fuel bases).length = bases.length ∧
      (freshNamesBy taken fuel bases).Nodup ∧
      (∀ n ∈ freshNamesBy taken fuel bases, taken n = false) ∧
      (∀ n ∈ freshNamesBy taken fuel bases, ∃ b ∈ bases, ∃ t, n = b ++ t) := by
  induction bases with
  | nil =>
    intro taken fuel l _ _
    simp only [freshNamesBy, List.length_nil, List.nodup_nil, List.not_mem_nil,
      false_imp_iff, implies_true, and_self]
  | cons b rest ih =>
    intro taken fuel l hl hfuel
    simp only [freshNamesBy]
    generalize hn : freshNameBy taken fuel b = n
    have hnt : taken n = false := hn ▸ freshNameBy_not_taken taken fuel b l hl hfuel
    have hl' : ∀ m, (taken m || m == n) = true → m ∈ n :: l := by
      intro m hm
      rcases Bool.or_eq_true_iff.mp hm with hm | hm
      · exact List.mem_cons_of_mem _ (hl m hm)
      · exact (beq_iff_eq.mp hm) ▸ List.mem_cons_self
    have hfuel' : (n :: l).length ≤ fuel + 1 := by
      simp only [List.length_cons]
      omega
    obtain ⟨hlen, hnd, hfresh, hpfx⟩ := ih (fun m => taken m || m == n) (fuel + 1) (n :: l) hl'
      hfuel'
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [List.length_cons, hlen]
    · refine List.nodup_cons.mpr ⟨fun hmem => ?_, hnd⟩
      have hbad := hfresh n hmem
      simp only [beq_self_eq_true, Bool.or_true] at hbad
      cases hbad
    · intro m hm
      rcases List.mem_cons.mp hm with rfl | hm
      · exact hnt
      · have hmt := hfresh m hm
        simp only [Bool.or_eq_false_iff] at hmt
        exact hmt.1
    · intro m hm
      rcases List.mem_cons.mp hm with rfl | hm
      · obtain ⟨t, ht⟩ := freshNameBy_prefix taken fuel b
        exact ⟨b, List.mem_cons_self, t, hn ▸ ht⟩
      · obtain ⟨b', hb', t, ht⟩ := hpfx m hm
        exact ⟨b', List.mem_cons_of_mem _ hb', t, ht⟩

/-- `freshNamesBy` for the membership test of a hash set, with fuel its size. -/
private theorem freshNamesBy_spec_set (taken : Std.HashSet String) (bases : List String) :
    (freshNamesBy taken.contains taken.size bases).length = bases.length ∧
      (freshNamesBy taken.contains taken.size bases).Nodup ∧
      (∀ n ∈ freshNamesBy taken.contains taken.size bases, n ∉ taken) ∧
      (∀ n ∈ freshNamesBy taken.contains taken.size bases, ∃ b ∈ bases, ∃ t, n = b ++ t) := by
  have hl : ∀ n, taken.contains n = true → n ∈ taken.toList := fun n hn =>
    Std.HashSet.mem_toList.mpr (Std.HashSet.contains_iff_mem.mp hn)
  have hfuel : taken.toList.length ≤ taken.size := by
    exact Nat.le_of_eq Std.HashSet.length_toList
  obtain ⟨hlen, hnd, hfresh, hpfx⟩ :=
    freshNamesBy_spec bases taken.contains taken.size taken.toList hl hfuel
  refine ⟨hlen, hnd, fun n hn hmem => ?_, hpfx⟩
  have hbad := hfresh n hn
  rw [Std.HashSet.contains_iff_mem.mpr hmem] at hbad
  cases hbad

/-- `freshName taken base` is not in `taken`. -/
theorem freshName_not_mem (taken : Std.HashSet String) (base : String) :
    freshName taken base ∉ taken := by
  have hl : ∀ n, taken.contains n = true → n ∈ taken.toList := fun n hn =>
    Std.HashSet.mem_toList.mpr (Std.HashSet.contains_iff_mem.mp hn)
  have hfuel : taken.toList.length ≤ taken.size := by
    exact Nat.le_of_eq Std.HashSet.length_toList
  have hfree := freshNameBy_not_taken taken.contains taken.size base taken.toList hl hfuel
  intro hmem
  unfold freshName at hmem
  rw [Std.HashSet.contains_iff_mem.mpr hmem] at hfree
  cases hfree

/-- `freshNames` picks one name per base. -/
theorem freshNames_length (taken : Std.HashSet String) (bases : List String) :
    (freshNames taken bases).1.length = bases.length :=
  (freshNamesBy_spec_set taken bases).1

/-- The names `freshNames` picks are distinct. -/
theorem freshNames_nodup (taken : Std.HashSet String) (bases : List String) :
    (freshNames taken bases).1.Nodup :=
  (freshNamesBy_spec_set taken bases).2.1

/-- No name `freshNames taken bases` picks is in `taken`. -/
theorem freshNames_not_mem (taken : Std.HashSet String) (bases : List String) :
    ∀ n ∈ (freshNames taken bases).1, n ∉ taken :=
  (freshNamesBy_spec_set taken bases).2.2.1

/-- Every name `freshNames taken bases` picks starts with one of `bases`. -/
theorem freshNames_prefix (taken : Std.HashSet String) (bases : List String) :
    ∀ n ∈ (freshNames taken bases).1, ∃ b ∈ bases, b.toList <+: n.toList := by
  intro n hn
  obtain ⟨b, hb, t, ht⟩ := (freshNamesBy_spec_set taken bases).2.2.2 n hn
  refine ⟨b, hb, ?_⟩
  rw [ht, String.toList_append]
  exact List.prefix_append _ _

/-- If every name `taken` accepts is in a list of at most `fuel` names, the names
    `freshNamesBy taken fuel bases` returns are pairwise distinct and `taken` rejects each. -/
theorem freshNamesBy_fresh (bases : List String) :
    ∀ (taken : String → Bool) (fuel : Nat) (L : List String),
      (∀ s, taken s = true → s ∈ L) → L.length ≤ fuel →
      (∀ n ∈ freshNamesBy taken fuel bases, taken n = false) ∧
        (freshNamesBy taken fuel bases).Nodup := by
  induction bases with
  | nil => intro _ _ _ _ _; simp [freshNamesBy]
  | cons b rest ih =>
    intro taken fuel L hL hlen
    have hn := freshNameBy_not_taken taken fuel b L hL hlen
    obtain ⟨hrest, hnd⟩ := ih (fun m => taken m || m == freshNameBy taken fuel b) (fuel + 1)
      (freshNameBy taken fuel b :: L)
      (fun s hs => by
        rcases Bool.or_eq_true _ _ ▸ hs with h | h
        · exact List.mem_cons_of_mem _ (hL s h)
        · exact (beq_iff_eq.1 h) ▸ List.mem_cons_self)
      (by simp; omega)
    simp only [freshNamesBy, List.mem_cons, List.nodup_cons]
    refine ⟨fun m hm => ?_, fun hm => ?_, hnd⟩
    · rcases hm with rfl | hm
      · exact hn
      · have := hrest m hm
        simp only [Bool.or_eq_false_iff] at this
        exact this.1
    · have := hrest _ hm
      simp at this

/-- The names `freshNames taken bases` returns are pairwise distinct and none is in `taken`. -/
theorem freshNames_fresh (taken : Std.HashSet String) (bases : List String) :
    (∀ n ∈ (freshNames taken bases).1, n ∉ taken) ∧ (freshNames taken bases).1.Nodup := by
  obtain ⟨hnt, hnd⟩ := freshNamesBy_fresh bases taken.contains taken.size taken.toList
    (fun s hs => Std.HashSet.mem_toList.2 (Std.HashSet.mem_iff_contains.2 hs))
    (by simp [Std.HashSet.length_toList])
  refine ⟨fun n hn hmem => ?_, hnd⟩
  have := hnt n hn
  rw [Std.HashSet.mem_iff_contains.1 hmem] at this
  cases this

/-- An internal name starts with the prefix `internalPrefixOf` records for it. -/
theorem startsWith_internalPrefixOf {n : String} (h : isInternal n = true) :
    n.startsWith (internalPrefixOf n) = true := by
  unfold isInternal at h
  rw [String.startsWith_string_iff] at h ⊢
  obtain ⟨rest, hrest⟩ := h
  have hdrop : n.toList.drop internalMarker.length = rest := by
    rw [← hrest, String.length, List.drop_left]
  unfold internalPrefixOf
  rw [String.toList_append, String.toList_ofList, hdrop, ← hrest]
  refine (List.prefix_append_right_inj _).mpr ?_
  split
  · exact List.take_prefix _ _
  · exact List.takeWhile_prefix _

end Strata.Name

end -- public section
