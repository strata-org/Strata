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
  `constVal_bitvecConst`, `constVal_mapConst`, `constVal_sequenceConst`, `constVal_sort` — the
  equations of `constVal`
- `constVal_denoteConst` — the denotation of a well-typed literal is its value
- `constVal_injective` (with `constValElems_injective`) — literals with no map in their sort are
  determined by their values
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
    cases c <;> simp [LConst.sort, LSort.toMonoTy, LSort.toMonoTy.map, LMonoTy.arrow] at h

/-- A well-typed constant of type `bool` is a Boolean literal. -/
public theorem LConst.eq_boolConst_of_ty {c : LConst} (hw : c.wt = true) (h : c.ty = .bool) :
    ∃ b, c = .boolConst b := by
  rw [LConst.ty_of_wt hw] at h
  cases c <;> first | exact ⟨_, rfl⟩ |
    simp [LConst.sort, LSort.toMonoTy, LSort.toMonoTy.map, LMonoTy.bool] at h

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
  cases c' <;> first | rfl |
    (exfalso
     cases c <;> simp_all [LConst.sort, LSort.toMonoTy, LSort.toMonoTy.map, LConst.isPrimitive])

/-! #### Equations and laws of `constVal` -/

/-- The value of a Boolean literal at the Boolean sort is the Boolean itself. -/
public theorem constVal_boolConst (b : Bool) :
    constVal tcInterp .bool (.boolConst b) = some b := by
  unfold constVal; split
  · rfl
  · exact absurd rfl ‹_›

/-- The value of an integer literal at the integer sort is the integer itself. -/
public theorem constVal_intConst (i : Int) :
    constVal tcInterp .int (.intConst i) = some i := by
  unfold constVal; split
  · rfl
  · exact absurd rfl ‹_›

/-- The value of a rational literal at the real sort is the real number it names. -/
public theorem constVal_rationalConst (r : Rat) :
    constVal tcInterp .real (.rationalConst r) = some (Strata.Util.Real.ofRat r) := by
  unfold constVal; split
  · rfl
  · exact absurd rfl ‹_›

/-- The value of a string literal at the string sort is the string itself. -/
public theorem constVal_strConst (x : String) :
    constVal tcInterp .string (.strConst x) = some x := by
  unfold constVal; split
  · rfl
  · exact absurd rfl ‹_›

/-- The value of a bit-vector literal of width `n` at the sort of width-`n` bit vectors is the
    bit vector itself. -/
public theorem constVal_bitvecConst (n : Nat) (b : BitVec n) :
    constVal tcInterp (.bitvec n) (.bitvecConst n b) = some b := by
  unfold constVal; split
  · rfl
  · exact absurd rfl ‹_›

/-- The value of a map literal with key sort `k` and value sort `v` at the sort `Map k v`: the
    map sending each key to the value of its first entry and every other key to the value of the
    default, when the default and every entry have values at those sorts. -/
public theorem constVal_mapConst (k v : LSort) (d : LConst) (es : List (LConst × LConst)) :
    constVal tcInterp (.map k v) (.mapConst k v d ⟨es⟩) =
      match constVal tcInterp v d, constValEntries tcInterp k v es with
      | some dv, some kvs => some (SortDenote.mapOf dv kvs)
      | _, _ => none := by
  conv => lhs; unfold constVal
  split
  · rfl
  · exact absurd rfl ‹_›

/-- The value of a sequence literal with element sort `a` at the sort `Sequence a`: the list of
    the values of its elements, when each has a value at `a`. -/
public theorem constVal_sequenceConst (a : LSort) (es : List LConst) :
    constVal tcInterp (.seq a) (.sequenceConst a ⟨es⟩) =
      (constValElems tcInterp a es).map SortDenote.seqOf := by
  conv => lhs; unfold constVal
  split
  · rfl
  · exact absurd rfl ‹_›

/-- `constVal` at sort `s` succeeds only on constants declaring sort `s`. -/
public theorem constVal_sort {s : LSort} {c : LConst} {x : SortDenote tcInterp s}
    (h : constVal tcInterp s c = some x) : c.sort = s := by
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
  | _ =>
    unfold constVal at h; split at h
    · rename_i hc; exact hc
    · cases h

/-- A well-typed constant's value at the sort of its type is its denotation. -/
public theorem constVal_denoteConst (vt : TyVarVal) {c : LConst} (h : c.wt = true) :
    constVal tcInterp (c.ty.substTyVars vt) c = some (denoteConst tcInterp vt c) := by
  have hgen : ∀ (s : LSort) (hs : s = c.sort)
      (p : SortDenote tcInterp c.sort = SortDenote tcInterp s),
      constVal tcInterp s c =
        some (cast p ((constVal tcInterp c.sort c).get (constVal_isSome tcInterp c h))) := by
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

mutual
/-- At a sort without `Map`, two constants with the same value are equal. -/
public theorem constVal_injective : ∀ {s : LSort} (a b : LConst) {x : SortDenote tcInterp s},
    s.hasMap = false → constVal tcInterp s a = some x → constVal tcInterp s b = some x → a = b
  | s, .sequenceConst e ⟨es⟩, b, x, hs, ha, hb => by
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
      have he : e'.hasMap = false := by
        simp_all [LSort.hasMap, LSort.hasMap.hasMapList]
      have hes := constValElems_injective e' es es' he hxs (hx' ▸ hxs')
      subst hes; rfl
    | _ => simp [LConst.sort] at hsb
  | s, .mapConst k v _ _, _, _, hs, ha, _ => by
    obtain rfl : s = .tcons "Map" [k, v] := (constVal_sort ha).symm
    simp [LSort.hasMap] at hs
  | s, .boolConst i, b, x, _, ha, hb => by
    have hsb := constVal_sort hb
    obtain rfl : s = .bool := (constVal_sort ha).symm
    cases b <;> simp [LConst.sort] at hsb
    rw [constVal_boolConst] at ha hb
    exact congrArg _ ((Option.some.inj ha).trans (Option.some.inj hb).symm)
  | s, .intConst i, b, x, _, ha, hb => by
    have hsb := constVal_sort hb
    obtain rfl : s = .int := (constVal_sort ha).symm
    cases b <;> simp [LConst.sort] at hsb
    rw [constVal_intConst] at ha hb
    exact congrArg _ ((Option.some.inj ha).trans (Option.some.inj hb).symm)
  | s, .rationalConst i, b, x, _, ha, hb => by
    have hsb := constVal_sort hb
    obtain rfl : s = .real := (constVal_sort ha).symm
    cases b <;> simp [LConst.sort] at hsb
    rw [constVal_rationalConst] at ha hb
    exact congrArg _ (Strata.Util.Real.ofRat_inj.mp
      ((Option.some.inj ha).trans (Option.some.inj hb).symm))
  | s, .strConst i, b, x, _, ha, hb => by
    have hsb := constVal_sort hb
    obtain rfl : s = .string := (constVal_sort ha).symm
    cases b <;> simp [LConst.sort] at hsb
    rw [constVal_strConst] at ha hb
    exact congrArg _ ((Option.some.inj ha).trans (Option.some.inj hb).symm)
  | s, .bitvecConst n i, b, x, _, ha, hb => by
    have hsb := constVal_sort hb
    obtain rfl : s = .bitvec n := (constVal_sort ha).symm
    cases b <;> try (simp [LConst.sort] at hsb; done)
    simp only [LConst.sort, LSort.bitvec.injEq] at hsb
    subst hsb
    rw [constVal_bitvecConst] at ha hb
    exact congrArg _ ((Option.some.inj ha).trans (Option.some.inj hb).symm)
/-- At a sort without `Map`, two lists of constants with the same values are equal. -/
public theorem constValElems_injective : ∀ (s : LSort) (as bs : List LConst)
    {xs : List (SortDenote tcInterp s)}, s.hasMap = false →
    constValElems tcInterp s as = some xs → constValElems tcInterp s bs = some xs → as = bs
  | _, [], [], _, _, _, _ => rfl
  | _, [], _ :: _, _, _, ha, hb => by
    simp only [constValElems, Option.some.injEq] at ha
    subst ha
    simp only [constValElems] at hb
    split at hb <;> simp_all
  | _, _ :: _, [], _, _, ha, hb => by
    simp only [constValElems, Option.some.injEq] at hb
    subst hb
    simp only [constValElems] at ha
    split at ha <;> simp_all
  | s, a :: as, b :: bs, xs, hs, ha, hb => by
    simp only [constValElems] at ha hb
    split at ha
    · rename_i x r hx hr
      cases ha
      split at hb
      · rename_i y r' hy hr'
        simp only [Option.some.injEq, List.cons.injEq] at hb
        obtain ⟨rfl, rfl⟩ := hb
        rw [constVal_injective a b hs hx hy, constValElems_injective s as bs hs hr hr']
      · cases hb
    · cases ha
end

end Lambda
