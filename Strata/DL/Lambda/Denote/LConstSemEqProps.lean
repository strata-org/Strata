/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Lambda.Denote.LConstSemEq
import all Strata.DL.Lambda.Denote.LConstSemEq
import all Strata.DL.Lambda.Denote.LExprDenote
import Strata.Util.RealProps

/-!
## Soundness of the semantic equality of literals

A decided answer of `LConst.semEq?` (`Strata.DL.Lambda.Denote.LConstSemEq`) is the equality of
the values of the two literals, in every interpretation whose type constructors are inhabited.

Key definitions: `LConst.SemSound`.

Key theorems: `LConst.semEq?_sound`.
-/

namespace Lambda

/-! ### Soundness -/

public section

variable {tcInterp : TyConstrInterp}

/-- The comparison `f` is *sound* in the interpretation `tcInterp`: whenever it decides two
    literals that have values at one sort, its answer is the equality of those values. -/
@[expose] def LConst.SemSound (tcInterp : TyConstrInterp) (f : LConst → LConst → Option Bool) :
    Prop :=
  ∀ {s : LSort} {c d : LConst} {x y : SortDenote tcInterp s} {b : Bool},
    constVal tcInterp s c = some x → constVal tcInterp s d = some y → f c d = some b →
      (x = y ↔ b = true)

/-- The map `mapOf` builds from no entries is its default. -/
private theorem mapOf_nil {k v : LSort} (dv : SortDenote tcInterp v) (x : SortDenote tcInterp k) :
    (SortDenote.mapOf (k := k) dv [] : SortDenote tcInterp k → SortDenote tcInterp v) x = dv := by
  simp [SortDenote.mapOf]

open Classical in
/-- The map `mapOf` builds sends the key of its first entry to that entry's value, and every
    other key to what the remaining entries send it to. -/
private theorem mapOf_cons {k v : LSort} (dv : SortDenote tcInterp v)
    (a : SortDenote tcInterp k) (w : SortDenote tcInterp v)
    (r : List (SortDenote tcInterp k × SortDenote tcInterp v)) (x : SortDenote tcInterp k) :
    (SortDenote.mapOf dv ((a, w) :: r) : SortDenote tcInterp k → SortDenote tcInterp v) x =
      if a = x then w
      else (SortDenote.mapOf dv r : SortDenote tcInterp k → SortDenote tcInterp v) x := by
  by_cases h : a = x <;> simp [SortDenote.mapOf, h]

/-- The elements of a list with values have a value each, the lists have one length, and the
    values of a non-empty list are the value of its head before those of its tail. -/
private theorem constValElems_cons {a : LSort} {e : LConst} {r : List LConst}
    {xs : List (SortDenote tcInterp a)} (h : constValElems tcInterp a (e :: r) = some xs) :
    ∃ x xs', constVal tcInterp a e = some x ∧ constValElems tcInterp a r = some xs' ∧
      xs = x :: xs' := by
  simp only [constValElems] at h
  split at h <;> cases h
  exact ⟨_, _, ‹_›, ‹_›, rfl⟩

/-- The values of the entries of a non-empty map literal are the values of its first entry
    before those of the remaining ones. -/
private theorem constValEntries_cons {k v : LSort} {a w : LConst} {r : List (LConst × LConst)}
    {kvs : List (SortDenote tcInterp k × SortDenote tcInterp v)}
    (h : constValEntries tcInterp k v ((a, w) :: r) = some kvs) :
    ∃ xa yw kvs', constVal tcInterp k a = some xa ∧ constVal tcInterp v w = some yw ∧
      constValEntries tcInterp k v r = some kvs' ∧ kvs = (xa, yw) :: kvs' := by
  simp only [constValEntries] at h
  split at h <;> cases h
  exact ⟨_, _, _, ‹_›, ‹_›, ‹_›, rfl⟩

/-- **Elementwise comparison is sound** for a sound `f`. -/
private theorem LConst.listEqWith_sound {f : LConst → LConst → Option Bool}
    (hf : LConst.SemSound tcInterp f) {a : LSort} :
    ∀ {xs ys : List LConst} {xv yv : List (SortDenote tcInterp a)} {b : Bool},
      constValElems tcInterp a xs = some xv → constValElems tcInterp a ys = some yv →
      LConst.listEqWith f xs ys = some b → (xv = yv ↔ b = true)
  | [], [], _, _, _, rfl, rfl, rfl => iff_of_true rfl rfl
  | [], _ :: _, _, _, _, rfl, hy, rfl => (constValElems_cons hy).elim fun _ ⟨_, _, _, he⟩ => by
    simp [he]
  | _ :: _, [], _, _, _, hx, rfl, rfl => (constValElems_cons hx).elim fun _ ⟨_, _, _, he⟩ => by
    simp [he]
  | x :: xs, y :: ys, _, _, b, hx, hy, h => by
    obtain ⟨x', xv', hx1, hx2, rfl⟩ := constValElems_cons hx
    obtain ⟨y', yv', hy1, hy2, rfl⟩ := constValElems_cons hy
    simp only [LConst.listEqWith] at h
    split at h <;> rename_i hxy
    · simp [(hf hx1 hy1 hxy).2 rfl, LConst.listEqWith_sound hf hx2 hy2 h]
    · cases h
      simp [mt (hf hx1 hy1 hxy).1 Bool.false_ne_true]
    · cases h

/-- **Lookup is sound** for a sound key comparison `f`: the literal `lookupWith` finds for a key
    `u`, or the default `dc` when it finds none, has the value the map `mapOf` builds sends the
    value of `u` to. -/
private theorem LConst.lookupWith_sound {f : LConst → LConst → Option Bool}
    (hf : LConst.SemSound tcInterp f) {k v : LSort} {u dc : LConst}
    {xu : SortDenote tcInterp k} {dv : SortDenote tcInterp v}
    (hu : constVal tcInterp k u = some xu) (hdc : constVal tcInterp v dc = some dv) :
    ∀ {xs : List (LConst × LConst)} {kvs : List (SortDenote tcInterp k × SortDenote tcInterp v)}
      {r : Option LConst},
      constValEntries tcInterp k v xs = some kvs → LConst.lookupWith f u xs = some r →
      constVal tcInterp v (r.getD dc) =
        some ((SortDenote.mapOf dv kvs : SortDenote tcInterp k → SortDenote tcInterp v) xu)
  | [], _, _, rfl, rfl => by simpa [mapOf_nil] using hdc
  | (a, w) :: rest, kvs, r, hx, h => by
    obtain ⟨xa, yw, kvs', ha, hw, hr, rfl⟩ := constValEntries_cons hx
    simp only [LConst.lookupWith] at h
    split at h <;> rename_i hau
    · cases h
      simpa [mapOf_cons, (hf ha hu hau).2 rfl] using hw
    · simpa [mapOf_cons, mt (hf ha hu hau).1 Bool.false_ne_true] using
        LConst.lookupWith_sound hf hu hdc hr h
    · cases h

/-- `allWith` answers `true` only when `g` holds of every element. -/
private theorem LConst.allWith_true {g : LConst → Option Bool} :
    ∀ {us : List LConst}, LConst.allWith g us = some true → ∀ u ∈ us, g u = some true
  | [], _, _, hu => by cases hu
  | u :: r, h, w, hw => by
    simp only [LConst.allWith] at h
    split at h <;> try cases h
    rename_i hg
    exact (List.mem_cons.1 hw).elim (· ▸ hg) (LConst.allWith_true h w)

/-- `allWith` answers `false` only when `g` refutes some element. -/
private theorem LConst.allWith_false {g : LConst → Option Bool} :
    ∀ {us : List LConst}, LConst.allWith g us = some false → ∃ u ∈ us, g u = some false
  | [], h => by cases h
  | u :: r, h => by
    simp only [LConst.allWith] at h
    split at h
    · exact (LConst.allWith_false h).imp fun _ ⟨hw, hg⟩ => ⟨List.mem_cons_of_mem _ hw, hg⟩
    · exact ⟨u, List.mem_cons_self, ‹_›⟩
    · cases h

/-- Every key of a map literal with values has a value. -/
private theorem LConst.constVal_key_of_entries {k v : LSort} :
    ∀ {xs : List (LConst × LConst)} {kvs : List (SortDenote tcInterp k × SortDenote tcInterp v)},
      constValEntries tcInterp k v xs = some kvs →
      ∀ u ∈ xs.map Prod.fst, ∃ xu, constVal tcInterp k u = some xu
  | [], _, _, _, hu => by simp at hu
  | (a, w) :: rest, _, hx, u, hu => by
    obtain ⟨xa, _, _, ha, -, hr, -⟩ := constValEntries_cons hx
    exact (List.mem_cons.1 hu).elim (· ▸ ⟨xa, ha⟩) (LConst.constVal_key_of_entries hr u)

/-- The map `mapOf` builds sends a value that no listed key has to the default. -/
private theorem LConst.mapOf_of_not_key {k v : LSort} {dv : SortDenote tcInterp v}
    {x : SortDenote tcInterp k} :
    ∀ {xs : List (LConst × LConst)} {kvs : List (SortDenote tcInterp k × SortDenote tcInterp v)},
      constValEntries tcInterp k v xs = some kvs →
      (∀ u ∈ xs.map Prod.fst, constVal tcInterp k u ≠ some x) →
      (SortDenote.mapOf dv kvs : SortDenote tcInterp k → SortDenote tcInterp v) x = dv
  | [], _, rfl, _ => mapOf_nil dv x
  | (a, w) :: rest, _, hx, hn => by
    obtain ⟨xa, yw, kvs', ha, -, hr, rfl⟩ := constValEntries_cons hx
    have hne : xa ≠ x := fun he => hn a (List.mem_cons_self) (he ▸ ha)
    simpa [mapOf_cons, hne] using
      LConst.mapOf_of_not_key hr fun u hu => hn u (List.mem_cons_of_mem _ hu)

/-- **Pigeonhole.** A list holding `m` distinct values `g 0`, …, `g (m - 1)` has length at
    least `m`. -/
private theorem LConst.le_length_of_injOn {α : Type} :
    ∀ (m : Nat) (L : List α) (g : Nat → α),
      (∀ i j, i < m → j < m → g i = g j → i = j) → (∀ i, i < m → g i ∈ L) → m ≤ L.length
  | 0, _, _, _, _ => Nat.zero_le _
  | m + 1, L, g, hinj, hmem => by
    classical
    have hm : g m ∈ L := hmem m (Nat.lt_succ_self m)
    have hrest : m ≤ (L.erase (g m)).length := by
      refine LConst.le_length_of_injOn m _ g (fun i j hi hj => hinj i j (by omega) (by omega))
        fun i hi => (List.mem_erase_of_ne fun he => ?_).2 (hmem i (by omega))
      exact absurd (hinj i m (by omega) (by omega) he) (by omega)
    rw [List.length_erase_of_mem hm] at hrest
    have hp : 0 < L.length := List.length_pos_of_mem hm
    omega

/-- Finitely many keys cannot list every value of a sort into which `g` injects the naturals:
    some value is the value of no key. -/
private theorem LConst.exists_not_key_of_inj {s : LSort} (g : Nat → SortDenote tcInterp s)
    (hg : ∀ i j, g i = g j → i = j) (us : List LConst) :
    ∃ x : SortDenote tcInterp s, ∀ u ∈ us, constVal tcInterp s u ≠ some x := by
  let L := us.filterMap (constVal tcInterp s)
  refine Classical.byContradiction fun hn => Nat.not_succ_le_self L.length ?_
  exact LConst.le_length_of_injOn _ L g (fun i j _ _ => hg i j) fun i _ =>
    Classical.byContradiction fun hx =>
      hn ⟨g i, fun u hu he => hx (List.mem_filterMap.2 ⟨u, hu, he⟩)⟩

/-- A literal with a value at `bool` is a Boolean literal with that value. -/
private theorem eq_boolConst_of_constVal {u : LConst} {x : SortDenote tcInterp .bool}
    (h : constVal tcInterp .bool u = some x) : u = .boolConst x := by
  have hs := constVal_sort h
  cases u <;> simp [LConst.sort] at hs
  rw [constVal_boolConst] at h
  exact congrArg _ (Option.some.inj h)

/-- **`keysCover?` is sound when it answers `true`**: every value of the key sort is the value of
    a listed key. -/
private theorem LConst.keysCover?_true {k : LSort} {us : List LConst}
    (h : LConst.keysCover? k us = some true) :
    ∀ x : SortDenote tcInterp k, ∃ u ∈ us, constVal tcInterp k u = some x := by
  unfold LConst.keysCover? at h
  split at h
  · simp only [Option.some.injEq, Bool.and_eq_true, List.any_eq_true] at h
    obtain ⟨⟨ut, hut, het⟩, ⟨uf, huf, hef⟩⟩ := h
    obtain rfl : ut = .boolConst true := by split at het <;> first | rfl | cases het
    obtain rfl : uf = .boolConst false := by split at hef <;> first | rfl | cases hef
    have hy : ∀ y : Bool, ∃ u ∈ us, constVal tcInterp .bool u = some y
      | false => ⟨_, huf, constVal_boolConst false⟩
      | true => ⟨_, hut, constVal_boolConst true⟩
    exact hy
  · rename_i n
    split at h
    · simp only [Option.some.injEq, List.all_eq_true, List.mem_range, List.any_eq_true] at h
      intro x
      obtain ⟨u, hu, hm⟩ := h (BitVec.toNat (w := n) x) (BitVec.isLt x)
      cases u <;> simp only [Bool.and_eq_true, beq_iff_eq, reduceCtorEq] at hm
      · obtain ⟨rfl, hb⟩ := hm
        exact ⟨_, hu, BitVec.eq_of_toNat_eq hb ▸ constVal_bitvecConst _ _⟩
      all_goals simp at hm
    · cases h
  all_goals cases h

/-- **`keysCover?` is sound when it answers `false`**: some value of the key sort is the value of
    no listed key. This is where the inhabitation of the interpreted sorts matters: a sequence
    sort has infinitely many values because its element sort has one. -/
private theorem LConst.keysCover?_false [hI : TyConstrInterp.AllInhabited tcInterp] {k : LSort}
    {us : List LConst} (h : LConst.keysCover? k us = some false) :
    ∃ x : SortDenote tcInterp k, ∀ u ∈ us, constVal tcInterp k u ≠ some x := by
  unfold LConst.keysCover? at h
  split at h
  · simp only [Option.some.injEq, Bool.and_eq_false_iff, List.any_eq_false] at h
    rcases h with h | h
    · exact ⟨(true : Bool), fun u hu he => h _ hu (eq_boolConst_of_constVal he ▸ rfl)⟩
    · exact ⟨(false : Bool), fun u hu he => h _ hu (eq_boolConst_of_constVal he ▸ rfl)⟩
  · rename_i n
    split at h
    · simp only [Option.some.injEq, List.all_eq_false, List.mem_range, List.any_eq_true,
        not_exists, not_and, Bool.not_eq_true] at h
      obtain ⟨i, hi, hn⟩ := h
      exact ⟨BitVec.ofNat n i, fun u hu he => by
        have hs := constVal_sort he
        cases u <;> simp only [LConst.sort, LSort.bitvec.injEq, reduceCtorEq] at hs
        subst hs
        rw [constVal_bitvecConst] at he
        simpa [Option.some.inj he, Nat.mod_eq_of_lt hi] using hn _ hu⟩

    · rename_i hlt
      refine Classical.byContradiction fun hn => hlt (Nat.le_trans (LConst.le_length_of_injOn
        (2 ^ n) (us.filterMap (constVal tcInterp (.bitvec n)))
        (fun i => (BitVec.ofNat n i : SortDenote tcInterp (.bitvec n))) ?_ ?_)
        (List.length_filterMap_le _ us))
      · exact fun i j hi hj he => by
          simpa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] using congrArg BitVec.toNat he
      · exact fun i _ => Classical.byContradiction fun hx =>
          hn ⟨_, fun u hu he => hx (List.mem_filterMap.2 ⟨u, hu, he⟩)⟩
  · exact LConst.exists_not_key_of_inj (s := .int) (fun i => (i : Int))
      (fun i j h => Int.ofNat.inj h) us
  · exact LConst.exists_not_key_of_inj (s := .real)
      (fun i => Strata.Util.Real.ofRat (i : Rat))
      (fun i j h => by simpa using Strata.Util.Real.ofRat_inj.mp h) us
  · exact LConst.exists_not_key_of_inj (s := .string)
      (fun i => String.ofList (List.replicate i 'a'))
      (fun i j h => by simpa [String.length_ofList] using congrArg String.length h) us
  · rename_i a
    have : Inhabited (SortDenote tcInterp a) := SortDenote.inhabited tcInterp hI.inhabited a
    exact LConst.exists_not_key_of_inj (s := .seq a)
      (fun i => (List.replicate i default : List (SortDenote tcInterp a)))
      (fun i j h => by simpa using congrArg List.length h) us
  · cases h

/-- **Comparing two map literals as functions is sound** for a sound comparison `f` of their
    keys and values. -/
private theorem LConst.mapEqWith_sound [TyConstrInterp.AllInhabited tcInterp]
    {f : LConst → LConst → Option Bool} (hf : LConst.SemSound tcInterp f) {k v : LSort}
    {dc dd : LConst} {xs ys : List (LConst × LConst)} {dv dv' : SortDenote tcInterp v}
    {kvs kvs' : List (SortDenote tcInterp k × SortDenote tcInterp v)} {b : Bool}
    (hdc : constVal tcInterp v dc = some dv) (hdd : constVal tcInterp v dd = some dv')
    (hx : constValEntries tcInterp k v xs = some kvs)
    (hy : constValEntries tcInterp k v ys = some kvs')
    (h : LConst.mapEqWith f k dc xs dd ys = some b) :
    ((SortDenote.mapOf dv kvs : SortDenote tcInterp k → SortDenote tcInterp v) =
      SortDenote.mapOf dv' kvs' ↔ b = true) := by
  have hat : ∀ u {b' : Bool}, (match LConst.lookupWith f u xs, LConst.lookupWith f u ys with
        | some a, some b => f (a.getD dc) (b.getD dd)
        | _, _ => none) = some b' → ∀ xu, constVal tcInterp k u = some xu →
      ((SortDenote.mapOf dv kvs : SortDenote tcInterp k → SortDenote tcInterp v) xu =
        SortDenote.mapOf dv' kvs' xu ↔ b' = true) := by
    intro u b' hg xu hu
    split at hg
    · rename_i a c ha hc
      exact hf (LConst.lookupWith_sound hf hu hdc hx ha) (LConst.lookupWith_sound hf hu hdd hy hc)
        hg
    · cases hg
  have hdef : ∀ x, (∀ u ∈ xs.map Prod.fst ++ ys.map Prod.fst, constVal tcInterp k u ≠ some x) →
      (SortDenote.mapOf dv kvs : SortDenote tcInterp k → SortDenote tcInterp v) x = dv ∧
        (SortDenote.mapOf dv' kvs' : SortDenote tcInterp k → SortDenote tcInterp v) x = dv' :=
    fun x hn => ⟨LConst.mapOf_of_not_key hx fun u hu => hn u (List.mem_append_left _ hu),
      LConst.mapOf_of_not_key hy fun u hu => hn u (List.mem_append_right _ hu)⟩
  simp only [LConst.mapEqWith] at h
  split at h <;> rename_i hpw
  · have heq : (∀ x, (∃ u ∈ xs.map Prod.fst ++ ys.map Prod.fst, constVal tcInterp k u = some x) ∨
        dv = dv') →
        (SortDenote.mapOf dv kvs : SortDenote tcInterp k → SortDenote tcInterp v) =
          SortDenote.mapOf dv' kvs' := by
      intro hall
      funext x
      by_cases hk : ∃ u ∈ xs.map Prod.fst ++ ys.map Prod.fst, constVal tcInterp k u = some x
      · obtain ⟨u, hu, hxu⟩ := hk
        exact (hat u (LConst.allWith_true hpw u hu) x hxu).2 rfl
      · obtain ⟨h1, h2⟩ := hdef x fun u hu he => hk ⟨u, hu, he⟩
        rw [h1, h2]
        exact (hall x).resolve_left hk
    split at h <;> rename_i hd
    · cases h
      exact ⟨fun _ => rfl, fun _ => heq fun _ => .inr ((hf hdc hdd hd).2 rfl)⟩
    · cases b
      · obtain ⟨x, hx'⟩ := LConst.keysCover?_false (tcInterp := tcInterp) h
        obtain ⟨h1, h2⟩ := hdef x hx'
        exact ⟨fun he => (hf hdc hdd hd).1 (h1.symm.trans ((congrFun he x).trans h2)), nofun⟩
      · exact ⟨fun _ => rfl, fun _ => heq fun x => .inl (LConst.keysCover?_true h x)⟩
    · cases h
  · cases h
    obtain ⟨u, hu, hg⟩ := LConst.allWith_false hpw
    obtain ⟨xu, hxu⟩ := (List.mem_append.1 hu).elim (LConst.constVal_key_of_entries hx u)
      (LConst.constVal_key_of_entries hy u)
    exact ⟨fun he => (hat u hg xu hxu).1 (congrFun he xu), nofun⟩
  · cases h

/-- Two literals of one sort containing `Map` are two sequence literals or two map literals,
    with the same element sort, or the same key and value sorts. -/
private theorem shape_of_hasMap {c d : LConst} (hs : c.sort = d.sort)
    (hm : c.sort.hasMap = true) :
    (∃ a xs ys, c = .sequenceConst a ⟨xs⟩ ∧ d = .sequenceConst a ⟨ys⟩) ∨
      (∃ k v dc xs dd ys, c = .mapConst k v dc ⟨xs⟩ ∧ d = .mapConst k v dd ⟨ys⟩) := by
  rcases c with _ | _ | _ | _ | _ | ⟨_, _, _, ⟨_⟩⟩ | ⟨_, ⟨_⟩⟩ <;>
    rcases d with _ | _ | _ | _ | _ | ⟨_, _, _, ⟨_⟩⟩ | ⟨_, ⟨_⟩⟩ <;>
    simp_all [LConst.sort, LSort.hasMap, LSort.hasMap.hasMapList]

/-- **Semantic equality is sound.** When `semEq?` decides two literals that have values at one
    sort, in an interpretation whose type constructors are inhabited (as every model's are), its
    answer is the equality of those values. -/
theorem LConst.semEq?_sound [TyConstrInterp.AllInhabited tcInterp] :
    ∀ fuel, LConst.SemSound tcInterp (LConst.semEq? fuel)
  | 0, _, c, d, _, _, _, hc, hd, h => by
    simp only [LConst.semEq?] at h
    split at h <;> cases h
    subst d
    exact ⟨fun _ => rfl, fun _ => Option.some.inj (hc.symm.trans hd)⟩
  | fuel + 1, s, c, d, x, y, b, hc, hd, h => by
    have hsc := constVal_sort hc
    have hsd := constVal_sort hd
    simp only [LConst.semEq?] at h
    split at h
    · cases h
      subst d
      exact ⟨fun _ => rfl, fun _ => Option.some.inj (hc.symm.trans hd)⟩
    split at h
    · rename_i hne hm
      cases h
      exact ⟨fun hxy => absurd (constVal_injective c d (hsc ▸ hm) hc (hxy ▸ hd)) hne, nofun⟩
    · rename_i hne hm
      rcases shape_of_hasMap (hsc.trans hsd.symm) (by simpa using hm) with
        ⟨a, xs, ys, rfl, rfl⟩ | ⟨k, v, dc, xs, dd, ys, rfl, rfl⟩
      · simp only at h
        obtain rfl : s = .seq a := hsc.symm
        rw [constVal_sequenceConst] at hc hd
        obtain ⟨xv, hxv, rfl⟩ := Option.map_eq_some_iff.mp hc
        obtain ⟨yv, hyv, rfl⟩ := Option.map_eq_some_iff.mp hd
        exact LConst.listEqWith_sound (LConst.semEq?_sound fuel) hxv hyv h
      · simp only at h
        obtain rfl : s = .map k v := hsc.symm
        rw [constVal_mapConst] at hc hd
        split at hc <;> split at hd <;> cases hc <;> cases hd
        exact LConst.mapEqWith_sound (LConst.semEq?_sound fuel) ‹_› ‹_› ‹_› ‹_› h


end

end Lambda
