/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Lambda.TypeFactoryWF
import all Strata.DL.Lambda.TypeFactoryWF

/-!
## Properties of `Lambda.TypeFactoryWF`

- `TypeFactoryWF.eq_of_name_eq` — in a well-formed `TypeFactory` (i.e. one whose
  datatype names are unique), two datatypes drawn from it with the same name are
  equal.
-/

namespace Lambda

/-- Two datatypes in a well-formed `TypeFactory` with the same name are equal. -/
theorem TypeFactoryWF.eq_of_name_eq {IDMeta : Type} {tf : @TypeFactory IDMeta}
    (hwf : TypeFactoryWF tf)
    {d₁ d₂ : LDatatype IDMeta}
    (hd₁ : d₁ ∈ tf.allDatatypes)
    (hd₂ : d₂ ∈ tf.allDatatypes)
    (hname : d₁.name = d₂.name)
    : d₁ = d₂ := by
  -- Nodup is Pairwise (· ≠ ·), so distinct elements have distinct mapped values
  -- Contrapositive: same mapped value → same element
  suffices h : ∀ (l : List (LDatatype IDMeta)),
      (l.map LDatatype.name).Nodup → ∀ a ∈ l, ∀ b ∈ l, a.name = b.name → a = b from
    h _ hwf.name_nodup d₁ hd₁ d₂ hd₂ hname
  intro l
  induction l with
  | nil => intro _ a ha; contradiction
  | cons x xs ih =>
    intro hnd a ha b hb hab
    simp only [List.map_cons, List.nodup_cons] at hnd
    have ⟨hnotmem, hnd_tl⟩ := hnd
    simp only [List.mem_cons] at ha hb
    cases ha with
    | inl ha_eq => cases hb with
      | inl hb_eq => rw [ha_eq, hb_eq]
      | inr hb_mem =>
        subst ha_eq
        have h_b_mem : b.name ∈ xs.map LDatatype.name := List.mem_map.mpr ⟨b, hb_mem, rfl⟩
        exact absurd (hab ▸ h_b_mem) hnotmem
    | inr ha_mem => cases hb with
      | inl hb_eq =>
        subst hb_eq
        have h_a_mem : a.name ∈ xs.map LDatatype.name := List.mem_map.mpr ⟨a, ha_mem, rfl⟩
        exact absurd (hab.symm ▸ h_a_mem) hnotmem
      | inr hb_mem => exact ih hnd_tl a ha_mem b hb_mem hab

end Lambda
