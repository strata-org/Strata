/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.Store
import all Strata.DL.Imperative.Store
import all Strata.Util.ListUtilsProps

---------------------------------------------------------------------

namespace Imperative

/-! # Metatheory of semantic stores

List-level definedness laws, store-substitution symmetry, and generated-name
reservation properties for the definitions in `Store`.

Key results:
- `isDefinedCons` / `isDefinedApp` and the corresponding `isNotDefined*` laws
  compose and decompose list-level definedness.
- `substStoresFlip`, `substDefinedFlip`, `invStoresComm`, and
  `invStoresExceptComm` establish substitution and invariance symmetry.
- `SemanticStore.isReserved.gen_slot_none`,
  `SemanticStore.isReserved.storeWith_gen`, and `SemanticStore.isReserved.mono`
  establish and preserve generated-name reservations.
-/

public section

variable (P : PureExpr)

/-- Definedness of a singleton and a tail implies definedness of their cons. -/
theorem isDefinedCons :
    isDefined σ [v] →
    isDefined σ vs2 →
    isDefined σ (v :: vs2) := by
  intros Hd1 Hd2
  simp [isDefined] at *
  simp [Option.isSome] at *
  split <;> simp_all

/-- Definedness of two lists implies definedness of their concatenation. -/
theorem isDefinedApp :
    isDefined σ vs1 →
    isDefined σ vs2 →
    isDefined σ (vs1 ++ vs2) := by
  intros Hd1 Hd2
  simp [isDefined] at *
  intros ident hmem
  simp [Option.isSome] at *
  cases hmem with
  | inl hmem =>
    split <;> simp
    specialize Hd1 ident hmem
    simp_all
  | inr hmem =>
    split <;> simp
    specialize Hd2 ident hmem
    simp_all

/-- Definedness of a cons list implies definedness of its head and tail. -/
theorem isDefinedCons' :
    isDefined σ (h :: t) →
    isDefined σ [h] ∧ isDefined σ t := by
  simp [isDefined] at *

/-- Definedness of a concatenation implies definedness of both component lists. -/
theorem isDefinedApp' :
    isDefined σ (t1 ++ t2) →
    isDefined σ t1 ∧ isDefined σ t2 := by
  intros hdefined
  simp [isDefined] at *
  apply And.intro
  · intros ident hmem
    apply hdefined
    left
    assumption
  · intros ident hmem
    apply hdefined
    right
    assumption

/-- Undefinedness of a singleton and a tail implies undefinedness of their cons. -/
theorem isNotDefinedCons :
    isNotDefined σ [v] →
    isNotDefined σ vs2 →
    isNotDefined σ (v :: vs2) := by
  intros Hd1 Hd2
  simp [isNotDefined] at *
  simp_all

/-- Undefinedness of two lists implies undefinedness of their concatenation. -/
theorem isNotDefinedApp :
    isNotDefined σ vs1 →
    isNotDefined σ vs2 →
    isNotDefined σ (vs1 ++ vs2) := by
  intros Hd1 Hd2
  simp [isNotDefined] at *
  intros ident hmem
  cases hmem with
  | inl hmem =>
    specialize Hd1 ident hmem
    simp_all
  | inr hmem =>
    specialize Hd2 ident hmem
    simp_all

/-- Undefinedness of a cons list implies undefinedness of its head and tail. -/
theorem isNotDefinedCons' :
    isNotDefined σ (h :: t) →
    isNotDefined σ [h] ∧ isNotDefined σ t := by
  simp [isNotDefined] at *

/-- Undefinedness of a concatenation implies undefinedness of both components. -/
theorem isNotDefinedApp' :
    isNotDefined σ (t1 ++ t2) →
    isNotDefined σ t1 ∧ isNotDefined σ t2 := by
  intros hundefined
  simp [isNotDefined] at *
  apply And.intro
  · intros ident hmem
    apply hundefined
    left
    assumption
  · intros ident hmem
    apply hundefined
    right
    assumption

/-! ## Store substitution -/

/-- Swapping both sides of every substitution pair twice is the identity. -/
theorem substSwapId (substs : List (P.Ident × P.Ident)) :
    substSwap (substSwap substs) = substs := by
  simp [substSwap]

/-- Store substitution can be read in the reverse direction after swapping its
identifier pairs. -/
theorem substStoresFlip :
    substStores σ₁ σ₂ substs →
    substStores σ₂ σ₁ (substSwap substs) := by
  intros hsubst
  simp [substStores, substSwap] at *
  intros targetIdent sourceIdent targetValue sourceValue hmem hsource htarget
  simp_all
  apply Eq.symm
  apply hsubst
  exact hmem

/-- Reverse-direction store substitution can be flipped back. -/
theorem substStoresFlip' :
    substStores σ₂ σ₁ (substSwap substs) →
    substStores σ₁ σ₂ substs := by
  intros hsubst
  have hsubst' := substStoresFlip hsubst
  simp [substSwapId] at hsubst'
  exact hsubst'

/-- Pairwise definedness is symmetric after swapping substitution pairs. -/
theorem substDefinedFlip :
    substDefined σ₁ σ₂ substs →
    substDefined σ₂ σ₁ (substSwap substs) := by
  intros hsubst
  simp [substDefined, substSwap] at *
  intros targetIdent sourceIdent targetValue sourceValue hmem hsource htarget
  simp_all
  exact And.comm.mp (hsubst sourceIdent targetIdent hmem)

/-- Swapped pairwise definedness can be flipped back. -/
theorem substDefinedFlip' :
    substDefined σ₂ σ₁ (substSwap substs) →
    substDefined σ₁ σ₂ substs := by
  intros hsubst
  have hsubst' := substDefinedFlip hsubst
  simp [substSwapId] at hsubst'
  exact hsubst'

/-- Store invariance is symmetric. -/
theorem invStoresComm :
    invStores σ₁ σ₂ ks →
    invStores σ₂ σ₁ ks := by
  intros hinvariant
  simp [invStores] at *
  apply substStoresFlip'
  simp [substSwap]
  assumption

/-- Store invariance outside a key set is symmetric. -/
theorem invStoresExceptComm :
    invStoresExcept σ₁ σ₂ ks →
    invStoresExcept σ₂ σ₁ ks := by
  intros hinvariant other hdisjoint
  simp [invStoresExcept] at *
  exact invStoresComm (hinvariant other hdisjoint)

/-! ## Generated-name reservations -/

/-- The freshly generated name's slot is undefined in a reserved store, given a
well-formed generator state and classification of the generated name. -/
theorem SemanticStore.isReserved.gen_slot_none {P : PureExpr} [HasIdent P]
    {Q : String → Prop}
    {state : StringGenState} {store : SemanticStore P}
    (pfx : String) (hreserved : SemanticStore.isReserved Q state store)
    (hwf : StringGenState.WF state)
    (hQ : Q (StringGenState.gen pfx state).1) :
    store (HasIdent.ident (P := P) (StringGenState.gen pfx state).1) = none :=
  hreserved _ hQ (StringGenState.stringGens_gen_not_in pfx state hwf)

/-- Defining the freshly generated name and advancing the generator preserves
reserved-name freshness. -/
theorem SemanticStore.isReserved.storeWith_gen {P : PureExpr} [HasIdent P]
    [DecidableEq P.Ident] [LawfulHasIdent P]
    {Q : String → Prop}
    {state : StringGenState} {store : SemanticStore P}
    (pfx : String) (value : P.Expr)
    (hreserved : SemanticStore.isReserved Q state store) :
    SemanticStore.isReserved Q (StringGenState.gen pfx state).2
      (SemanticStore.update store
        (HasIdent.ident (P := P) (StringGenState.gen pfx state).1) value) := by
  intro name hQ hnotGenerated
  rw [StringGenState.stringGens_gen] at hnotGenerated
  have hne : name ≠ (StringGenState.gen pfx state).1 :=
    fun h => hnotGenerated (h ▸ List.mem_cons_self)
  have hnotGeneratedState : name ∉ state.stringGens :=
    fun h => hnotGenerated (List.mem_cons_of_mem _ h)
  have hidentNe :
      HasIdent.ident (P := P) name ≠
        HasIdent.ident (P := P) (StringGenState.gen pfx state).1 :=
    fun h => hne (LawfulHasIdent.ident_inj h)
  show (if HasIdent.ident (P := P) name = _ then some value else _) = none
  rw [ite_eq_right hidentNe]
  exact hreserved name hQ hnotGeneratedState

/-- Advancing the generator weakens the set of ungenerated names, so reserved
name freshness remains true. -/
theorem SemanticStore.isReserved.mono {P : PureExpr} [HasIdent P]
    {Q : String → Prop}
    {state state' : StringGenState} {store : SemanticStore P}
    (hstep : StringGenState.GenStep state state')
    (hreserved : SemanticStore.isReserved Q state store) :
    SemanticStore.isReserved Q state' store := by
  intro name hQ hnotGenerated
  exact hreserved name hQ (fun h => hnotGenerated (hstep.subset h))

end -- public section

end Imperative
