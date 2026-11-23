/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Lambda.TypeFactoryWF
import all Strata.DL.Lambda.TypeFactoryWF
public import Strata.DL.Lambda.TypeFactory
public import Strata.DL.Lambda.LExprTypeEnv
public import Strata.DL.Lambda.FactoryWF
import Strata.DL.Lambda.TypeFactoryProps
import Strata.DL.Lambda.DatatypeFactoryWFProps
import all Strata.DL.Lambda.TypeFactory
import Strata.DL.Lambda.LExprTypeEnvProps
import Strata.DL.Lambda.FactoryWFProps
import Strata.Util.ListUtilsProps

/-!
## Properties of `Lambda.TypeFactoryWF`

- `TypeFactoryWF.eq_of_name_eq` — in a well-formed `TypeFactory` (i.e. one whose
  datatype names are unique), two datatypes drawn from it with the same name are
  equal.
- `TypeFactoryWF.default` — the empty type factory is well-formed.
- `addMutualBlock_preserves_FactorySigWF` — registering an accepted mutual datatype
  block keeps every function signature of the context well formed.
-/

namespace Lambda

/-- The empty type factory is well-formed. -/
public theorem TypeFactoryWF.default {IDMeta : Type} :
    TypeFactoryWF (TypeFactory.default : @TypeFactory IDMeta) :=
  ⟨by simp [TypeFactory.default, TypeFactory.allDatatypes]⟩

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

/-! ## Well-formedness properties of executable type-factory validation -/

public section

/-- After registering an accepted mutual datatype block, every function of the context is one
    the context held before or is well formed. -/
private theorem mem_addMutualBlock_functions {T : LExprParams}
    [DecidableEq T.IDMeta]
    [Inhabited T.IDMeta] [Inhabited T.Metadata] [Std.ToFormat T.IDMeta]
    (C C' : LContext T) (block : MutualDatatype T.IDMeta)
    (h : C.addMutualBlock block = .ok C') (lf : LFunc T) (hlf : lf ∈ C'.functions.toArray) :
    lf ∈ C.functions.toArray ∨ LFuncWF lf := by
  obtain ⟨fgen, hfgen, hlist⟩ := LContext.addMutualBlock_functions_toList h
  obtain ⟨fac, hfac, hgenwf⟩ := LContext.addMutualBlock_genBlockFactory_wf h
  rw [hfgen, Except.ok.injEq] at hfac
  subst hfac
  rw [Array.mem_def, hlist, List.mem_append] at hlf
  rcases hlf with hold | hnew
  · exact .inl (Array.mem_def.mpr hold)
  · exact .inr (hgenwf lf (Array.mem_def.mpr hnew))

/-- Registering an accepted mutual datatype block preserves `FactorySigWF` of the context's
    functions. -/
theorem addMutualBlock_preserves_FactorySigWF {T : LExprParams}
    [DecidableEq T.IDMeta]
    [Inhabited T.IDMeta] [Inhabited T.Metadata] [Std.ToFormat T.IDMeta]
    (C C' : LContext T) (block : MutualDatatype T.IDMeta)
    (hwf : FactorySigWF C.functions)
    (h : C.addMutualBlock block = .ok C') :
    FactorySigWF C'.functions :=
  ⟨fun lf hlf => (mem_addMutualBlock_functions C C' block h lf hlf).elim (hwf.lfuncs_wf lf)
    LFuncWF.toSig⟩

end
end Lambda
