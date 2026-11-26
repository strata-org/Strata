/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Lambda.Denote.LExprDenote
import all Strata.DL.Lambda.Denote.LExprDenote
import Strata.Util.RealProps

/-!
## Denotations of Constants

Typing facts about constants and the equations and laws of their values (`constVal`) and
denotations (`denoteConst`), which `LExprDenote` defines.

- `LConst.ty_ne_arrow`, `LConst.eq_boolConst_of_ty` — the types of constants
- `LConst.wt_of_isPrimitive`, `LConst.eqDecidable_of_isPrimitive`, `LConst.isPrimitive_of_ty` —
  primitive constants
- `constVal_boolConst`, `constVal_intConst`, `constVal_rationalConst`, `constVal_strConst`,
  `constVal_bitvecConst`, `constVal_mapConst`, `constVal_sequenceConst`, `constVal_dataConst`,
  `constVal_sort`, `constVal_dataConst_some` — the equations of `constVal`
- `constVal_denoteConst` — the denotation of a well-typed literal is its value
- `constVal_injective` (with `constValElems_injective`) — at a sort without `Map`, a literal
  holding no datatype value (`LConst.hasData`) is determined by its value
- `constValElems_iff`, `constValEntries_iff`, `constVal_mapSelect`, `constValEntries_mapUpdate`,
  `constValEntries_cons_update`, `constValElems_contains` — the values of the map and sequence
  literals the evaluator builds
-/

namespace Lambda

/-! ### Types of constants -/

/-- A constant does not have an arrow type. -/
public theorem LConst.ty_ne_arrow (c : LConst) (a b : LMonoTy) : c.ty ≠ .arrow a b := by
  intro h
  cases hw : c.wt
  · rw [LConst.ty_of_not_wt hw] at h
    exact absurd (congrArg (fun t : LMonoTy => match t with | .tcons n _ => n | _ => "") h)
      (show ("bool" : String) ≠ "arrow" by decide)
  · rw [LConst.ty_of_wt hw] at h
    cases c with
    | dataConst _ _ s _ =>
      obtain ⟨_, _⟩ | _ := s <;>
        simp_all [LConst.wt, LConst.sort, LSort.toMonoTy, LMonoTy.arrow, LSort.isDataSort]
    | _ => simp [LConst.sort, LSort.toMonoTy, LSort.toMonoTy.map, LMonoTy.arrow] at h

/-- A well-typed constant of type `bool` is a Boolean literal. -/
public theorem LConst.eq_boolConst_of_ty {c : LConst} (hw : c.wt = true) (h : c.ty = .bool) :
    ∃ b, c = .boolConst b := by
  rw [LConst.ty_of_wt hw] at h
  cases c with
  | boolConst => exact ⟨_, rfl⟩
  | dataConst _ _ s _ =>
    obtain ⟨_, _⟩ | _ := s <;>
      simp_all [LConst.wt, LConst.sort, LSort.toMonoTy, LMonoTy.bool, LSort.isDataSort]
  | _ => simp [LConst.sort, LSort.toMonoTy, LSort.toMonoTy.map, LMonoTy.bool] at h

/-- A primitive constant (`LConst.isPrimitive`) is well typed. -/
public theorem LConst.wt_of_isPrimitive {c : LConst} (h : c.isPrimitive = true) :
    c.wt = true := by
  cases c <;> first | rfl | cases h

/-- A primitive constant (`LConst.isPrimitive`) has decidable equality
(`LConst.eqDecidable`). -/
public theorem LConst.eqDecidable_of_isPrimitive {c : LConst} (h : c.isPrimitive = true) :
    c.eqDecidable = true := by
  cases c <;> first | rfl | cases h

/-- A well-typed constant of the type of a primitive constant is primitive. -/
public theorem LConst.isPrimitive_of_ty {c c' : LConst} (hw : c'.wt = true) (h : c'.ty = c.ty)
    (hc : c.isPrimitive = true) : c'.isPrimitive = true := by
  rw [LConst.ty_of_wt hw, LConst.ty_of_wt (LConst.wt_of_isPrimitive hc)] at h
  cases c' with
  | dataConst _ _ s _ =>
    exfalso
    obtain ⟨_, _⟩ | _ := s <;> cases c <;>
      simp_all [LConst.wt, LConst.sort, LSort.toMonoTy, LSort.isDataSort, LConst.isPrimitive]
  | _ => first | rfl |
    (exfalso
     cases c <;> simp_all [LConst.sort, LSort.toMonoTy, LSort.toMonoTy.map, LConst.isPrimitive])

/-! #### Equations and laws of `constVal` -/

/-- The value of a Boolean literal at the Boolean sort is the Boolean itself. -/
public theorem constVal_boolConst (b : Bool) :
    constVal tcInterp opInterp .bool (.boolConst b) = some b := by
  unfold constVal; split
  · rfl
  · exact absurd rfl ‹_›

/-- The value of an integer literal at the integer sort is the integer itself. -/
public theorem constVal_intConst (i : Int) :
    constVal tcInterp opInterp .int (.intConst i) = some i := by
  unfold constVal; split
  · rfl
  · exact absurd rfl ‹_›

/-- The value of a rational literal at the real sort is the real number it names. -/
public theorem constVal_rationalConst (r : Rat) :
    constVal tcInterp opInterp .real (.rationalConst r) = some (Strata.Util.Real.ofRat r) := by
  unfold constVal; split
  · rfl
  · exact absurd rfl ‹_›

/-- The value of a string literal at the string sort is the string itself. -/
public theorem constVal_strConst (x : String) :
    constVal tcInterp opInterp .string (.strConst x) = some x := by
  unfold constVal; split
  · rfl
  · exact absurd rfl ‹_›

/-- The value of a bit-vector literal of width `n` at the sort of width-`n` bit vectors is the
    bit vector itself. -/
public theorem constVal_bitvecConst (n : Nat) (b : BitVec n) :
    constVal tcInterp opInterp (.bitvec n) (.bitvecConst n b) = some b := by
  unfold constVal; split
  · rfl
  · exact absurd rfl ‹_›

/-- The value of a map literal with key sort `k` and value sort `v` at the sort `Map k v`: the
    map sending each key to the value of its first entry and every other key to the value of the
    default, when the default and every entry have values at those sorts. -/
public theorem constVal_mapConst (k v : LSort) (d : LConst) (es : List (LConst × LConst)) :
    constVal tcInterp opInterp (.map k v) (.mapConst k v d ⟨es⟩) =
      match constVal tcInterp opInterp v d, constValEntries tcInterp opInterp k v es with
      | some dv, some kvs => some (SortDenote.mapOf dv kvs)
      | _, _ => none := by
  conv => lhs; unfold constVal
  split
  · rfl
  · exact absurd rfl ‹_›

/-- The value of a sequence literal with element sort `a` at the sort `Sequence a`: the list of
    the values of its elements, when each has a value at `a`. -/
public theorem constVal_sequenceConst (a : LSort) (es : List LConst) :
    constVal tcInterp opInterp (.seq a) (.sequenceConst a ⟨es⟩) =
      (constValElems tcInterp opInterp a es).map SortDenote.seqOf := by
  conv => lhs; unfold constVal
  split
  · rfl
  · exact absurd rfl ‹_›

/-- The value of a datatype value of sort `s` at `s`: the interpretation of its operator applied to
    the values of its arguments, when `s` is a datatype sort and each argument has a value at its
    sort. -/
public theorem constVal_dataConst (n : String) (as : List LSort) (s : LSort) (es : List LConst)
    (hs : s.isDataSort = true) :
    constVal tcInterp opInterp s (.dataConst n as s ⟨es⟩) =
      (constValArgs tcInterp opInterp as es).map
        (SortDenote.applyArgs tcInterp (opInterp n (LSort.mkArrow s as))) := by
  conv => lhs; unfold constVal
  split
  · rfl
  · exact absurd (And.intro rfl hs) ‹_›

/-- `constVal` at sort `s` succeeds only on constants declaring sort `s`. -/
public theorem constVal_sort {s : LSort} {c : LConst} {x : SortDenote tcInterp s}
    (h : constVal tcInterp opInterp s c = some x) : c.sort = s := by
  cases c with
  | mapConst k v d es =>
    obtain ⟨es⟩ := es
    unfold constVal at h; split at h
    · rename_i hc; exact hc
    · cases h
  | sequenceConst a es =>
    obtain ⟨es⟩ := es
    unfold constVal at h; split at h
    · rename_i hc; exact hc
    · cases h
  | dataConst n as srt es =>
    obtain ⟨es⟩ := es
    unfold constVal at h; split at h
    · rename_i hc; exact hc.1
    · cases h
  | _ =>
    unfold constVal at h; split at h
    · rename_i hc; exact hc
    · cases h

/-- A well-typed constant's value at the sort of its type is its denotation. -/
public theorem constVal_denoteConst (vt : TyVarVal) {c : LConst} (h : c.wt = true) :
    constVal tcInterp opInterp (c.ty.substTyVars vt) c = some (denoteConst tcInterp opInterp vt c) := by
  have hgen : ∀ (s : LSort) (hs : s = c.sort)
      (p : SortDenote tcInterp c.sort = SortDenote tcInterp s),
      constVal tcInterp opInterp s c =
        some (cast p ((constVal tcInterp opInterp c.sort c).get (constVal_isSome tcInterp opInterp c h))) := by
    intro s hs p; subst hs; simp
  have hs : c.ty.substTyVars vt = c.sort := by rw [LConst.ty_of_wt h, LSort.toMonoTy_substTyVars]
  cases c with
  | boolConst b => exact constVal_boolConst b
  | intConst i => exact constVal_intConst i
  | rationalConst r => exact constVal_rationalConst r
  | strConst x => exact constVal_strConst x
  | bitvecConst n b => exact constVal_bitvecConst n b
  | mapConst k v d es =>
    simp only [denoteConst, denoteCollection, h, dite_true]
    exact hgen _ hs _
  | sequenceConst a es =>
    simp only [denoteConst, denoteCollection, h, dite_true]
    exact hgen _ hs _
  | dataConst n as srt es =>
    simp only [denoteConst, denoteCollection, h, dite_true]
    exact hgen _ hs _

/-- A datatype value has a value only at its sort, which is a datatype sort. -/
public theorem constVal_dataConst_some {s : LSort} {n : String} {as : List LSort}
    {srt : LSort} {es : Array LConst} {x : SortDenote tcInterp s}
    (h : constVal tcInterp opInterp s (.dataConst n as srt es) = some x) :
    srt = s ∧ s.isDataSort = true := by
  obtain ⟨es⟩ := es
  unfold constVal at h; split at h
  · rename_i hc; exact ⟨hc.1, hc.1 ▸ hc.2⟩
  · cases h

mutual
/-- At a sort without `Map`, a constant holding no datatype value (`LConst.hasData`) is the only
    constant with its value. -/
public theorem constVal_injective : ∀ {s : LSort} (a b : LConst) {x : SortDenote tcInterp s},
    s.hasMap = false → a.hasData = false → constVal tcInterp opInterp s a = some x →
      constVal tcInterp opInterp s b = some x → a = b
  | s, .sequenceConst e ⟨es⟩, b, x, hs, hd, ha, hb => by
    have hsb := constVal_sort hb
    obtain rfl : s = .tcons "Sequence" [e] := (constVal_sort ha).symm
    cases b with
    | sequenceConst e' es' =>
      obtain ⟨es'⟩ := es'
      obtain rfl : e' = e := by
        simpa only [LConst.sort, LSort.tcons.injEq, List.cons.injEq, and_true, true_and] using hsb
      rw [constVal_sequenceConst] at ha hb
      obtain ⟨xs, hxs, rfl⟩ := Option.map_eq_some_iff.mp ha
      obtain ⟨xs', hxs', hx⟩ := Option.map_eq_some_iff.mp hb
      have hx' : xs' = xs := hx
      have he : e'.hasMap = false := by simp_all [LSort.hasMap, LSort.hasMap.hasMapList]
      have hes := constValElems_injective e' es es' he (by simpa [LConst.hasData] using hd) hxs
        (hx' ▸ hxs')
      subst hes; rfl
    | dataConst =>
      have := (constVal_dataConst_some hb).2; simp_all [LSort.isDataSort]
    | _ => simp [LConst.sort] at hsb
  | s, .mapConst k v _ _, _, _, hs, _, ha, _ => by
    obtain rfl : s = .tcons "Map" [k, v] := (constVal_sort ha).symm
    simp [LSort.hasMap] at hs
  | s, .dataConst .., _, _, _, hd, _, _ => by simp [LConst.hasData] at hd
  | s, .boolConst i, b, x, _, _, ha, hb => by
    have hsb := constVal_sort hb
    obtain rfl : s = .bool := (constVal_sort ha).symm
    cases b <;> simp [LConst.sort] at hsb <;>
      try (have := (constVal_dataConst_some hb).2; simp_all [LSort.isDataSort]; done)
    rw [constVal_boolConst] at ha hb
    exact congrArg _ ((Option.some.inj ha).trans (Option.some.inj hb).symm)
  | s, .intConst i, b, x, _, _, ha, hb => by
    have hsb := constVal_sort hb
    obtain rfl : s = .int := (constVal_sort ha).symm
    cases b <;> simp [LConst.sort] at hsb <;>
      try (have := (constVal_dataConst_some hb).2; simp_all [LSort.isDataSort]; done)
    rw [constVal_intConst] at ha hb
    exact congrArg _ ((Option.some.inj ha).trans (Option.some.inj hb).symm)
  | s, .rationalConst i, b, x, _, _, ha, hb => by
    have hsb := constVal_sort hb
    obtain rfl : s = .real := (constVal_sort ha).symm
    cases b <;> simp [LConst.sort] at hsb <;>
      try (have := (constVal_dataConst_some hb).2; simp_all [LSort.isDataSort]; done)
    rw [constVal_rationalConst] at ha hb
    exact congrArg _ (Strata.Util.Real.ofRat_inj.mp
      ((Option.some.inj ha).trans (Option.some.inj hb).symm))
  | s, .strConst i, b, x, _, _, ha, hb => by
    have hsb := constVal_sort hb
    obtain rfl : s = .string := (constVal_sort ha).symm
    cases b <;> simp [LConst.sort] at hsb <;>
      try (have := (constVal_dataConst_some hb).2; simp_all [LSort.isDataSort]; done)
    rw [constVal_strConst] at ha hb
    exact congrArg _ ((Option.some.inj ha).trans (Option.some.inj hb).symm)
  | s, .bitvecConst n i, b, x, _, _, ha, hb => by
    have hsb := constVal_sort hb
    obtain rfl : s = .bitvec n := (constVal_sort ha).symm
    cases b <;> try (simp [LConst.sort] at hsb; done)
    case dataConst => have := (constVal_dataConst_some hb).2; simp_all [LSort.isDataSort]
    simp only [LConst.sort, LSort.bitvec.injEq] at hsb
    subst hsb
    rw [constVal_bitvecConst] at ha hb
    exact congrArg _ ((Option.some.inj ha).trans (Option.some.inj hb).symm)
/-- At a sort without `Map`, a list of constants holding no datatype value is the only list of
    constants with its values. -/
public theorem constValElems_injective : ∀ (s : LSort) (as bs : List LConst)
    {xs : List (SortDenote tcInterp s)}, s.hasMap = false → LConst.hasDataElems as = false →
    constValElems tcInterp opInterp s as = some xs → constValElems tcInterp opInterp s bs = some xs →
      as = bs
  | _, [], [], _, _, _, _, _ => rfl
  | _, [], _ :: _, _, _, _, ha, hb => by
    simp only [constValElems, Option.some.injEq] at ha
    subst ha
    simp only [constValElems] at hb
    split at hb <;> simp_all
  | _, _ :: _, [], _, _, _, ha, hb => by
    simp only [constValElems, Option.some.injEq] at hb
    subst hb
    simp only [constValElems] at ha
    split at ha <;> simp_all
  | s, a :: as, b :: bs, xs, hs, hd, ha, hb => by
    simp only [LConst.hasDataElems, Bool.or_eq_false_iff] at hd
    simp only [constValElems] at ha hb
    split at ha
    · rename_i x r hx hr
      cases ha
      split at hb
      · rename_i y r' hy hr'
        simp only [Option.some.injEq, List.cons.injEq] at hb
        obtain ⟨rfl, rfl⟩ := hb
        rw [constVal_injective a b hs hd.1 hx hy, constValElems_injective s as bs hs hd.2 hr hr']
      · cases hb
    · cases ha
end

/-! ### Values of collection literals

Laws of `constVal` on map and sequence literals: how the values of the literals the evaluator
builds (`LConst.mapSelect`, `LConst.mapUpdate`, and the array operations on sequence elements)
relate to the values of the literals it builds them from. The `Map` and `Sequence` evaluators of
a language's factory are proved consistent with its model from these laws.
-/

public section

variable {tcInterp : TyConstrInterp} {opInterp : OpInterp tcInterp}

/-! ### Sequence elements -/

/-- A list of constants has the list `a` as values at a sort exactly when `a` has the same
    length and each constant has as value the element of `a` at its position. -/
theorem constValElems_iff {s : LSort} :
    ∀ {l : List LConst} {a : List (SortDenote tcInterp s)},
      constValElems tcInterp opInterp s l = some a ↔
        ∃ h : a.length = l.length, ∀ (i : Nat) (hi : i < l.length),
          constVal tcInterp opInterp s l[i] = some (a[i]'(h ▸ hi))
  | [], a => by
    simp only [constValElems, Option.some.injEq, List.length_nil, List.length_eq_zero_iff]
    constructor
    · rintro rfl; exact ⟨rfl, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    · rintro ⟨h, -⟩; exact h.symm
  | c :: l, a => by
    simp only [constValElems]
    constructor
    · intro h
      split at h
      · rename_i x r hx hr
        simp only [Option.some.injEq] at h; subst h
        obtain ⟨hlen, hall⟩ := (constValElems_iff (l := l)).mp hr
        refine ⟨by simp [hlen], fun i hi => ?_⟩
        cases i with
        | zero => exact hx
        | succ i => exact hall i (by simpa using hi)
      · cases h
    · rintro ⟨hlen, hall⟩
      cases a with
      | nil => simp at hlen
      | cons x r =>
        have hx : constVal tcInterp opInterp s c = some x := hall 0 (by simp)
        have hr : constValElems tcInterp opInterp s l = some r :=
          (constValElems_iff (l := l)).mpr
            ⟨by simpa using hlen, fun i hi => hall (i + 1) (by simpa using hi)⟩
        simp [hx, hr]

/-- If two lists of constants have values at a sort, their concatenation has as values the
    concatenation of their values. -/
theorem constValElems_append {s : LSort} {l₁ l₂ : List LConst}
    {a₁ a₂ : List (SortDenote tcInterp s)}
    (h₁ : constValElems tcInterp opInterp s l₁ = some a₁) (h₂ : constValElems tcInterp opInterp s l₂ = some a₂) :
    constValElems tcInterp opInterp s (l₁ ++ l₂) = some (a₁ ++ a₂) := by
  obtain ⟨hl₁, hv₁⟩ := constValElems_iff.mp h₁
  obtain ⟨hl₂, hv₂⟩ := constValElems_iff.mp h₂
  refine constValElems_iff.mpr ⟨by simp [hl₁, hl₂], fun i hi => ?_⟩
  by_cases hlt : i < l₁.length
  · rw [List.getElem_append_left hlt, List.getElem_append_left (by omega)]
    exact hv₁ i hlt
  · rw [List.getElem_append_right (show l₁.length ≤ i by omega),
      List.getElem_append_right (show a₁.length ≤ i by omega)]
    simp only [hl₁]
    exact hv₂ (i - l₁.length) (by simp at hi; omega)

/-- If a list of constants has values at a sort, its first `n` constants have as values the
    first `n` of its values. -/
theorem constValElems_take {s : LSort} {l : List LConst} {a : List (SortDenote tcInterp s)}
    (h : constValElems tcInterp opInterp s l = some a) (n : Nat) :
    constValElems tcInterp opInterp s (l.take n) = some (a.take n) := by
  obtain ⟨hl, hv⟩ := constValElems_iff.mp h
  refine constValElems_iff.mpr ⟨by simp [hl], fun i hi => ?_⟩
  simp only [List.getElem_take]
  exact hv i (by simp at hi; omega)

/-- If a list of constants has values at a sort, the list without its first `n` constants has
    as values its values without their first `n`. -/
theorem constValElems_drop {s : LSort} {l : List LConst} {a : List (SortDenote tcInterp s)}
    (h : constValElems tcInterp opInterp s l = some a) (n : Nat) :
    constValElems tcInterp opInterp s (l.drop n) = some (a.drop n) := by
  obtain ⟨hl, hv⟩ := constValElems_iff.mp h
  refine constValElems_iff.mpr ⟨by simp [hl], fun i hi => ?_⟩
  simp only [List.getElem_drop]
  exact hv (n + i) (by simp at hi; omega)

/-- If a list of constants has values at a sort, replacing its constant at position `j` by a
    constant with value `x` replaces its value at position `j` by `x`. -/
theorem constValElems_set {s : LSort} {l : List LConst} {a : List (SortDenote tcInterp s)}
    (h : constValElems tcInterp opInterp s l = some a) (j : Nat) {c : LConst} {x : SortDenote tcInterp s}
    (hc : constVal tcInterp opInterp s c = some x) :
    constValElems tcInterp opInterp s (l.set j c) = some (a.set j x) := by
  obtain ⟨hl, hv⟩ := constValElems_iff.mp h
  refine constValElems_iff.mpr ⟨by simp [hl], fun i hi => ?_⟩
  simp only [List.getElem_set]
  split
  · exact hc
  · exact hv i (by simpa using hi)

/-- Whether a list of constants at a sort without `Map` contains a constant holding no datatype
    value is whether one of their values is its value. -/
theorem constValElems_contains {s : LSort} (hs : s.hasMap = false) {l : List LConst}
    {a : List (SortDenote tcInterp s)} (h : constValElems tcInterp opInterp s l = some a)
    {c : LConst} (hcd : c.hasData = false) {x : SortDenote tcInterp s}
    (hc : constVal tcInterp opInterp s c = some x) :
    l.contains c = true ↔ ∃ (i : Nat) (hi : i < a.length), a[i] = x := by
  obtain ⟨hl, hv⟩ := constValElems_iff.mp h
  rw [List.contains_iff_mem, List.mem_iff_getElem]
  constructor
  · rintro ⟨i, hi, rfl⟩
    have hvi := hv i hi
    exact ⟨i, by omega, Option.some.inj (hvi.symm.trans hc)⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨i, by omega, (constVal_injective _ _ hs hcd hc (hv i (by omega))).symm⟩

/-! ### Map entries -/

/-- A list of map entries has the list `kvs` as values at key and value sorts exactly when
    `kvs` has the same length and each entry's key and value have as values the key and value
    of the element of `kvs` at its position. -/
theorem constValEntries_iff {k v : LSort} :
    ∀ {ents : List (LConst × LConst)} {kvs : List (SortDenote tcInterp k × SortDenote tcInterp v)},
      constValEntries tcInterp opInterp k v ents = some kvs ↔
        ∃ h : kvs.length = ents.length, ∀ (i : Nat) (hi : i < ents.length),
          constVal tcInterp opInterp k ents[i].1 = some (kvs[i]'(h ▸ hi)).1 ∧
          constVal tcInterp opInterp v ents[i].2 = some (kvs[i]'(h ▸ hi)).2
  | [], kvs => by
    simp only [constValEntries, Option.some.injEq, List.length_nil, List.length_eq_zero_iff]
    constructor
    · rintro rfl; exact ⟨rfl, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
    · rintro ⟨h, -⟩; exact h.symm
  | (a, b) :: ents, kvs => by
    simp only [constValEntries]
    constructor
    · intro h
      split at h
      · rename_i x y r hx hy hr
        simp only [Option.some.injEq] at h; subst h
        obtain ⟨hlen, hall⟩ := (constValEntries_iff (ents := ents)).mp hr
        refine ⟨by simp [hlen], fun i hi => ?_⟩
        cases i with
        | zero => exact ⟨hx, hy⟩
        | succ i => exact hall i (by simpa using hi)
      · cases h
    · rintro ⟨hlen, hall⟩
      cases kvs with
      | nil => simp at hlen
      | cons p r =>
        obtain ⟨hx, hy⟩ : constVal tcInterp opInterp k a = some p.1 ∧ constVal tcInterp opInterp v b = some p.2 :=
          hall 0 (by simp)
        have hr : constValEntries tcInterp opInterp k v ents = some r :=
          (constValEntries_iff (ents := ents)).mpr
            ⟨by simpa using hlen, fun i hi => hall (i + 1) (by simpa using hi)⟩
        simp [hx, hy, hr]

open Classical in
/-- The map with default `dv` and entries `p :: kvs` gives `x` the value `p.2` if `p`'s key is
    `x`, and otherwise the value the map with entries `kvs` gives it. -/
theorem SortDenote.mapOf_cons {k v : LSort} (dv : SortDenote tcInterp v)
    (p : SortDenote tcInterp k × SortDenote tcInterp v) (kvs : List _) (x : SortDenote tcInterp k) :
    SortDenote.mapOf dv (p :: kvs) x = if p.1 = x then p.2 else SortDenote.mapOf dv kvs x := by
  unfold SortDenote.mapOf
  rw [List.find?_cons]
  by_cases h : p.1 = x <;> simp [h]

/-- The map with default `dv` and no entries gives every key the value `dv`. -/
private theorem SortDenote.mapOf_nil {k v : LSort} (dv : SortDenote tcInterp v)
    (x : SortDenote tcInterp k) :
    SortDenote.mapOf (k := k) dv [] x = dv := rfl

open Classical in
/-- Appending an entry to the entries of a map changes its value only at the entry's key, and
    there only if no earlier entry has that key: it acts as the default value there. -/
private theorem SortDenote.mapOf_append_single {k v : LSort} (dv : SortDenote tcInterp v)
    (l : List (SortDenote tcInterp k × SortDenote tcInterp v)) (a : SortDenote tcInterp k)
    (b : SortDenote tcInterp v) (z : SortDenote tcInterp k) :
    SortDenote.mapOf dv (l ++ [(a, b)]) z =
      SortDenote.mapOf (if a = z then b else dv) l z := by
  induction l with
  | nil => rw [List.nil_append, SortDenote.mapOf_cons]; rfl
  | cons p l ih => rw [List.cons_append, SortDenote.mapOf_cons, SortDenote.mapOf_cons, ih]

/-- The value a map literal gives a key holding no datatype value is the value of the map at the
    key's value, at a key sort without `Map`. -/
theorem constVal_mapSelect {k v : LSort} (hk : k.hasMap = false) {d : LConst}
    {dv : SortDenote tcInterp v} (hd : constVal tcInterp opInterp v d = some dv) :
    ∀ {ents : List (LConst × LConst)} {kvs : List (SortDenote tcInterp k × SortDenote tcInterp v)},
      constValEntries tcInterp opInterp k v ents = some kvs →
      ∀ {key : LConst} {x : SortDenote tcInterp k}, key.hasData = false →
      constVal tcInterp opInterp k key = some x →
      constVal tcInterp opInterp v (LConst.mapSelect d ⟨ents⟩ key) = some (SortDenote.mapOf dv kvs x)
  | [], kvs, h, key, x, _, _ => by
    simp only [constValEntries, Option.some.injEq] at h; subst h
    simp only [LConst.mapSelect, ← Array.find?_toList, List.find?_nil]
    exact hd
  | (a, b) :: ents, kvs, h, key, x, hkd, hx => by
    simp only [constValEntries] at h
    split at h
    · rename_i xa xb r ha hb hr
      simp only [Option.some.injEq] at h; subst h
      have ih := constVal_mapSelect hk hd hr hkd hx
      rw [SortDenote.mapOf_cons]
      simp only [LConst.mapSelect, ← Array.find?_toList] at ih ⊢
      rw [List.find?_cons]
      by_cases hab : a = key
      · subst hab
        have hxa : xa = x := Option.some.inj (ha.symm.trans hx)
        rw [show (a == a) = true from beq_self_eq_true a]
        simp only [hxa, ↓reduceIte]
        exact hb
      · have hxa : xa ≠ x := fun he => hab (constVal_injective _ _ hk hkd hx (he ▸ ha)).symm
        rw [show (a == key) = false from beq_eq_false_iff_ne.mpr hab]
        simp only [hxa, ↓reduceIte]
        exact ih
    · cases h

/-- If two lists of map entries have values at key and value sorts, their concatenation has as
    values the concatenation of their values. -/
private theorem constValEntries_append {k v : LSort} {l₁ l₂ : List (LConst × LConst)}
    {a₁ a₂ : List (SortDenote tcInterp k × SortDenote tcInterp v)}
    (h₁ : constValEntries tcInterp opInterp k v l₁ = some a₁)
    (h₂ : constValEntries tcInterp opInterp k v l₂ = some a₂) :
    constValEntries tcInterp opInterp k v (l₁ ++ l₂) = some (a₁ ++ a₂) := by
  obtain ⟨hl₁, hv₁⟩ := constValEntries_iff.mp h₁
  obtain ⟨hl₂, hv₂⟩ := constValEntries_iff.mp h₂
  refine constValEntries_iff.mpr ⟨by simp [hl₁, hl₂], fun i hi => ?_⟩
  by_cases hlt : i < l₁.length
  · rw [List.getElem_append_left hlt, List.getElem_append_left (by omega)]
    exact hv₁ i hlt
  · rw [List.getElem_append_right (show l₁.length ≤ i by omega),
      List.getElem_append_right (show a₁.length ≤ i by omega)]
    simp only [hl₁]
    exact hv₂ (i - l₁.length) (by simp at hi; omega)

open Classical in
/-- The entries of a map literal without the entries of key `key` have as values the entries
    without the key's value, at a key sort without `Map` and a key holding no datatype value. -/
private theorem constValEntries_filter {k v : LSort} (hk : k.hasMap = false) {key : LConst}
    (hkd : key.hasData = false) {xk : SortDenote tcInterp k}
    (hkey : constVal tcInterp opInterp k key = some xk) :
    ∀ {ents : List (LConst × LConst)} {kvs : List (SortDenote tcInterp k × SortDenote tcInterp v)},
      constValEntries tcInterp opInterp k v ents = some kvs →
      constValEntries tcInterp opInterp k v (ents.filter (fun e => e.1 != key)) =
        some (kvs.filter (fun p => !decide (p.1 = xk)))
  | [], kvs, h => by
    simp only [constValEntries, Option.some.injEq] at h; subst h; rfl
  | (a, b) :: ents, kvs, h => by
    simp only [constValEntries] at h
    split at h
    · rename_i xa xb r ha hb hr
      simp only [Option.some.injEq] at h; subst h
      have ih := constValEntries_filter hk hkd hkey hr
      by_cases hab : a = key
      · subst hab
        have hxa : xa = xk := Option.some.inj (ha.symm.trans hkey)
        subst hxa
        simp only [List.filter_cons, bne_self_eq_false, decide_true, Bool.not_true,
          Bool.false_eq_true, ↓reduceIte]
        exact ih
      · have hxa : xa ≠ xk := fun he => hab (constVal_injective _ _ hk hkd hkey (he ▸ ha)).symm
        simp only [List.filter_cons, bne_iff_ne, ne_eq, hab, not_false_eq_true,
          ↓reduceIte, hxa, decide_false, Bool.not_false]
        simp [constValEntries, ha, hb, ih]
    · cases h

open Classical in
/-- Dropping the entries of a key leaves a map's other values unchanged. -/
private theorem SortDenote.mapOf_filter_ne {k v : LSort} (dv : SortDenote tcInterp v)
    (kvs : List (SortDenote tcInterp k × SortDenote tcInterp v)) {xk z : SortDenote tcInterp k}
    (hz : z ≠ xk) :
    SortDenote.mapOf dv (kvs.filter (fun p => !decide (p.1 = xk))) z =
      SortDenote.mapOf dv kvs z := by
  induction kvs with
  | nil => rfl
  | cons p kvs ih =>
    rw [List.filter_cons, SortDenote.mapOf_cons]
    by_cases hp : p.1 = xk
    · subst hp
      have hpz : p.1 ≠ z := fun h => hz h.symm
      simp [hpz, ih]
    · simp only [hp, decide_false, Bool.not_false, ↓reduceIte, SortDenote.mapOf_cons, ih]

open Classical in
/-- A map without the entries of a key takes its default value at the key. -/
private theorem SortDenote.mapOf_filter_eq {k v : LSort} (dv : SortDenote tcInterp v)
    (kvs : List (SortDenote tcInterp k × SortDenote tcInterp v)) (xk : SortDenote tcInterp k) :
    SortDenote.mapOf dv (kvs.filter (fun p => !decide (p.1 = xk))) xk = dv := by
  induction kvs with
  | nil => rfl
  | cons p kvs ih =>
    rw [List.filter_cons]
    by_cases hp : p.1 = xk
    · simp [hp, ih]
    · simp only [hp, decide_false, Bool.not_false, ↓reduceIte, SortDenote.mapOf_cons, ih]

open Classical in
/-- The entries of a map literal after `LConst.mapUpdate` give the map updated at the key, at a
    key sort without `Map` and a key holding no datatype value. -/
theorem constValEntries_mapUpdate {k v : LSort} (hk : k.hasMap = false) {d : LConst}
    {dv : SortDenote tcInterp v} (hd : constVal tcInterp opInterp v d = some dv)
    {ents : List (LConst × LConst)} {kvs : List (SortDenote tcInterp k × SortDenote tcInterp v)}
    (hes : constValEntries tcInterp opInterp k v ents = some kvs)
    {key x : LConst} (hkd : key.hasData = false) {xk : SortDenote tcInterp k}
    {xv : SortDenote tcInterp v} (hkey : constVal tcInterp opInterp k key = some xk)
    (hx : constVal tcInterp opInterp v x = some xv) :
    ∃ kvs', constValEntries tcInterp opInterp k v (LConst.mapUpdate d ⟨ents⟩ key x).toList = some kvs' ∧
      ∀ z, SortDenote.mapOf dv kvs' z =
        if z = xk then xv else SortDenote.mapOf dv kvs z := by
  have hf := constValEntries_filter (v := v) hk hkd hkey hes
  unfold LConst.mapUpdate
  dsimp only
  split
  · rename_i hxd
    obtain ⟨hxd, -⟩ := hxd
    subst hxd
    have hxv : xv = dv := Option.some.inj (hx.symm.trans hd)
    subst hxv
    refine ⟨_, by rw [Array.toList_filter]; exact hf, fun z => ?_⟩
    by_cases hz : z = xk
    · subst hz; simp [SortDenote.mapOf_filter_eq]
    · simp [hz, SortDenote.mapOf_filter_ne _ _ hz]
  · refine ⟨kvs.filter (fun p => !decide (p.1 = xk)) ++ [(xk, xv)], ?_, fun z => ?_⟩
    · rw [Array.toList_push, Array.toList_filter]
      have hpair : constValEntries tcInterp opInterp k v [(key, x)] = some [(xk, xv)] := by
        simp [constValEntries, hkey, hx]
      exact constValEntries_append hf hpair
    · rw [SortDenote.mapOf_append_single]
      by_cases hz : z = xk
      · subst hz; simp [SortDenote.mapOf_filter_eq]
      · have hxz : xk ≠ z := fun h => hz h.symm
        simp [hz, hxz, SortDenote.mapOf_filter_ne _ _ hz]

open Classical in
/-- Dropping entries whose key is `key` leaves a map's values at every other key unchanged. -/
private theorem constValEntries_filter_ne {k v : LSort} {dv : SortDenote tcInterp v} {key : LConst}
    {xk : SortDenote tcInterp k} (hkey : constVal tcInterp opInterp k key = some xk) :
    ∀ {ents : List (LConst × LConst)} {kvs : List (SortDenote tcInterp k × SortDenote tcInterp v)},
      constValEntries tcInterp opInterp k v ents = some kvs →
      ∃ kvs', constValEntries tcInterp opInterp k v (ents.filter (fun e => e.1 != key)) =
        some kvs' ∧ ∀ z, z ≠ xk → SortDenote.mapOf dv kvs' z = SortDenote.mapOf dv kvs z
  | [], kvs, h => by
    simp only [constValEntries, Option.some.injEq] at h; subst h
    exact ⟨[], rfl, fun _ _ => rfl⟩
  | (a, b) :: ents, kvs, h => by
    simp only [constValEntries] at h
    split at h
    · rename_i xa xb r ha hb hr
      simp only [Option.some.injEq] at h; subst h
      obtain ⟨kvs', hkvs', hz⟩ := constValEntries_filter_ne hkey hr
      by_cases hab : a = key
      · subst hab
        obtain rfl : xa = xk := Option.some.inj (ha.symm.trans hkey)
        refine ⟨kvs', by simpa using hkvs', fun z hne => ?_⟩
        rw [SortDenote.mapOf_cons, ite_eq_right_iff.mpr (fun h => absurd h.symm hne), hz z hne]
      · refine ⟨(xa, xb) :: kvs', by simp [hab, constValEntries, ha, hb, hkvs'],
          fun z hne => ?_⟩
        rw [SortDenote.mapOf_cons, SortDenote.mapOf_cons, hz z hne]
    · cases h

open Classical in
/-- The entry `(key, x)` followed by those entries of a map literal whose key is not `key` give
    the map updated at the key, at every key sort: the first entry counts. -/
theorem constValEntries_cons_update {k v : LSort} {dv : SortDenote tcInterp v}
    {ents : List (LConst × LConst)} {kvs : List (SortDenote tcInterp k × SortDenote tcInterp v)}
    (hes : constValEntries tcInterp opInterp k v ents = some kvs) {key x : LConst}
    {xk : SortDenote tcInterp k} {xv : SortDenote tcInterp v}
    (hkey : constVal tcInterp opInterp k key = some xk)
    (hx : constVal tcInterp opInterp v x = some xv) :
    ∃ kvs', constValEntries tcInterp opInterp k v
        ((key, x) :: ents.filter (fun e => e.1 != key)) = some kvs' ∧
      ∀ z, SortDenote.mapOf dv kvs' z = if z = xk then xv else SortDenote.mapOf dv kvs z := by
  obtain ⟨kvsf, hf, hz⟩ := constValEntries_filter_ne (dv := dv) hkey hes
  refine ⟨(xk, xv) :: kvsf, by simp [constValEntries, hkey, hx, hf], fun z => ?_⟩
  rw [SortDenote.mapOf_cons]
  by_cases hzk : z = xk
  · subst hzk; simp
  · simp [hzk, Ne.symm hzk, hz z hzk]

end -- public section

end Lambda
