/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.Grammar.ConcreteToAbstractTreeTranslator
public import Strata.Languages.Laurel.Grammar.AbstractToConcreteTreeTranslator
public import Strata.Languages.Laurel.LaurelASTProps
import all Strata.Languages.Laurel.Grammar.ConcreteToAbstractTreeTranslator
import all Strata.Languages.Laurel.Grammar.AbstractToConcreteTreeTranslator
import all Strata.Languages.Laurel.LaurelAST

/-!
# Round-trip of the Laurel tree translators (type level)

`highTypeValToArg` (abstract → concrete) followed by `translateHighType`
(concrete → abstract) is the identity on the **grammar-representable**
fragment of `HighType`, modulo source metadata (`highEq`).

The fragment excludes exactly the constructors the printer is deliberately
lossy for: `.TVoid` (prints as the identifier `void`), `.TSet` (element type
not representable), `.Applied`/`.Intersection` (printed as their
base/head), `.Unknown`, and `.MultiValuedExpr`. For everything else — the
primitive types, `TBv`, `UserDefined`, and arbitrarily nested `TMap` — the
round-trip is proven for this fragment; golden print→parse example tests on
it are instances of the theorem.

Key definitions and results:

- `HighType.grammarRepresentable` — predicate characterising the fragment the
  grammar represents faithfully.
- `getArgFileRange_ok` — `getArgFileRange` always succeeds and leaves the
  translation state unchanged.
- `translateHighType_highTypeValToArg_roundtrip` — for every
  grammar-representable type and any translation state, printing then parsing
  succeeds and is the identity modulo source metadata (`highEq_source_irrel`
  from `LaurelASTProps` supplies the metadata irrelevance).
-/

namespace Strata.Laurel

public section

/-- The fragment of `HighType` the Laurel grammar can represent faithfully:
    primitives, bitvectors, user-defined names, and maps thereof. On this
    fragment the abstract→concrete printer is injective and the round-trip
    through `translateHighType` is the identity (modulo source locations). -/
def HighType.grammarRepresentable : HighType → Bool
  | .TInt | .TBool | .TFloat64 | .TReal | .TString | .TBv _ => true
  | .UserDefined _ => true
  | .TMap k v => HighType.grammarRepresentable k.val && HighType.grammarRepresentable v.val
  | _ => false
  termination_by t => sizeOf t
  decreasing_by
    all_goals first
      | (cases k; simp; omega)
      | (cases v; simp; omega)

/-! Constructor-level `highEq` reductions. The raw `highEq.eq_def` loops under
`simp` (the recursive arms mention `highEq` again), so these expose only the
concrete-constructor reductions the round-trip proof needs; their left-hand
sides carry concrete constructors, so `simp` terminates. -/

@[local simp] private theorem highEq_TInt (sa sb : Option FileRange) :
    highEq ⟨.TInt, sa⟩ ⟨.TInt, sb⟩ = true := by rw [highEq.eq_def]
@[local simp] private theorem highEq_TBool (sa sb : Option FileRange) :
    highEq ⟨.TBool, sa⟩ ⟨.TBool, sb⟩ = true := by rw [highEq.eq_def]
@[local simp] private theorem highEq_TFloat64 (sa sb : Option FileRange) :
    highEq ⟨.TFloat64, sa⟩ ⟨.TFloat64, sb⟩ = true := by rw [highEq.eq_def]
@[local simp] private theorem highEq_TReal (sa sb : Option FileRange) :
    highEq ⟨.TReal, sa⟩ ⟨.TReal, sb⟩ = true := by rw [highEq.eq_def]
@[local simp] private theorem highEq_TString (sa sb : Option FileRange) :
    highEq ⟨.TString, sa⟩ ⟨.TString, sb⟩ = true := by rw [highEq.eq_def]
@[local simp] private theorem highEq_TBv (w₁ w₂ : Nat) (sa sb : Option FileRange) :
    highEq ⟨.TBv w₁, sa⟩ ⟨.TBv w₂, sb⟩ = (w₁ == w₂) := by rw [highEq.eq_def]
@[local simp] private theorem highEq_UserDefined (r₁ r₂ : Identifier) (sa sb : Option FileRange) :
    highEq ⟨.UserDefined r₁, sa⟩ ⟨.UserDefined r₂, sb⟩ = (r₁.text == r₂.text) := by
  rw [highEq.eq_def]
@[local simp] private theorem highEq_TMap (k₁ v₁ k₂ v₂ : HighTypeMd) (sa sb : Option FileRange) :
    highEq ⟨.TMap k₁ v₁, sa⟩ ⟨.TMap k₂ v₂, sb⟩ = (highEq k₁ k₂ && highEq v₁ v₂) := by
  rw [highEq.eq_def]

/-- `getArgFileRange` always succeeds, returning `s` unchanged: on the printer's
    `SourceRange.none` sentinel it returns `none`, and otherwise a range
    assembled from the state's `uri`. Stated as a plain success/shape fact so
    the round-trip proof can rewrite through the monadic `if` without unfolding
    `isNone` (whose body is not exposed across the module boundary). -/
private theorem getArgFileRange_ok (arg : StrataDDM.Arg) (s : TransState) :
    getArgFileRange arg s =
      .ok (if arg.ann.isNone then none
           else match s.uri with
                | some uri => some ⟨uri, arg.ann⟩
                | none => none, s) := by
  rw [getArgFileRange]
  split <;> cases huri : s.uri <;>
    simp_all [SourceRange.toFileRange, pure, StateT.pure, Except.pure, bind, StateT.bind,
              Except.bind, get, getThe, MonadStateOf.get, StateT.get]

/-- **Round-trip**: printing a grammar-representable `HighType` and parsing it
    back yields the same type modulo source metadata (`highEq`). Every golden
    `print → parse` example test on this fragment is an instance of this
    theorem. -/
theorem translateHighType_highTypeValToArg_roundtrip
    (t : HighType) (h : t.grammarRepresentable = true) (s : TransState) :
    ∃ t' s', translateHighType (highTypeValToArg t) s = .ok (t', s')
      ∧ highEq t' ⟨t, none⟩ = true := by
  suffices h_all : ∀ n (t : HighType), sizeOf t ≤ n →
      t.grammarRepresentable = true → ∀ s,
      ∃ t' s', translateHighType (highTypeValToArg t) s = .ok (t', s')
        ∧ highEq t' ⟨t, none⟩ = true from h_all (sizeOf t) t (Nat.le_refl _) h s
  intro n
  induction n with
  | zero => intro t hsz; cases t <;> simp at hsz
  | succ n ih =>
    intro t hsz hrep s
    match t with
    | .TInt | .TBool | .TFloat64 | .TReal | .TString =>
      simp only [highTypeValToArg]
      rw [translateHighType.eq_def]
      simp [laurelOp, getArgFileRange_ok, bind, StateT.bind, pure, StateT.pure, Except.pure,
            mkHighTypeMd, Except.bind]
    | .TBv w =>
      simp only [highTypeValToArg]
      rw [translateHighType.eq_def]
      simp [laurelOp, getArgFileRange_ok, translateNat, bind, StateT.bind, pure, StateT.pure,
            Except.pure, mkHighTypeMd, Except.bind]
    | .UserDefined name =>
      simp only [highTypeValToArg]
      rw [translateHighType.eq_def]
      simp [laurelOp, ident, getArgFileRange_ok, translateIdent, bind, StateT.bind, pure,
            StateT.pure, Except.pure, mkHighTypeMd, Except.bind]
    | .TMap k v =>
      simp only [HighType.grammarRepresentable, Bool.and_eq_true] at hrep
      have hszk : sizeOf k.val ≤ n := by cases k; simp at hsz ⊢; omega
      have hszv : sizeOf v.val ≤ n := by cases v; simp at hsz ⊢; omega
      obtain ⟨k', s1, hk_eq, hk_hi⟩ := ih k.val hszk hrep.1 s
      obtain ⟨v', _, hv_eq, hv_hi⟩ := ih v.val hszv hrep.2 s1
      have hk' : highEq k' k = true := highEq_source_irrel k' k k'.source none ▸ hk_hi
      have hv' : highEq v' v = true := highEq_source_irrel v' v v'.source none ▸ hv_hi
      simp only [highTypeValToArg, highTypeToArg]
      rw [translateHighType.eq_def]
      simp [laurelOp, getArgFileRange_ok, bind, StateT.bind, pure, StateT.pure, Except.pure,
            mkHighTypeMd, Except.bind, hk_eq, hv_eq, hk', hv']
    | .TVoid | .TSet _ | .Applied _ _ | .Intersection _ | .Unknown
    | .MultiValuedExpr _ =>
      simp [HighType.grammarRepresentable] at hrep

/-! ## Correspondence to the golden round-trip tests

Every type annotation appearing in the golden print→parse programs of
`StrataTest/Languages/Laurel/UnitTests/AbstractToConcreteTreeTranslatorTest.lean`
(`x: int`, `: int` returns, `var p: Point`) satisfies the theorem's
`grammarRepresentable` hypothesis, so each golden round-trip is an instance of
`translateHighType_highTypeValToArg_roundtrip` at the type level. The guards
below pin that correspondence — plus a representative nested-`TMap` case the
theorem covers beyond the goldens, and, as a negative, `TVoid` (which appears
in the goldens only as a procedure's absent return and is deliberately outside
the fragment). -/

#guard HighType.TInt.grammarRepresentable                 -- `x: int`, `: int`
#guard (HighType.UserDefined (mkId "Point")).grammarRepresentable  -- `var p: Point`
#guard (HighType.TMap ⟨.TInt, none⟩ ⟨.TMap ⟨.TBool, none⟩ ⟨.TString, none⟩, none⟩).grammarRepresentable
#guard !HighType.TVoid.grammarRepresentable  -- lossy: prints as the identifier `void`

end -- public section

end Strata.Laurel
