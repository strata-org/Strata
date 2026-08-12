/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.DL.Lambda.DatatypeWF
import all Strata.DL.Lambda.DatatypeWF
import Strata.DL.Lambda.TypeFactory
import all Strata.DL.Lambda.TypeFactory

/-!
# DatatypeWF Tests

Worked examples of the declarative datatype well-formedness relations from
`Strata.DL.Lambda.DatatypeWF`: constructor-argument types that are well-formed
(`ConstrArgWF`) versus ones rejected for non-uniformity or nesting. Each
`example` proves the relation (or its negation) directly.

Throughout, `Tree` is the datatype under construction, declared `Tree a`
(so its `typeArgs` are `["a"]`); `block = [Tree]`. `List`/`Pair` are other
(non-block) type constructors, and `bool` is `.tcons "bool" []`.
-/

namespace Lambda
namespace DatatypeWFTests

open Lambda

/-- `Tree a`, the datatype whose constructor arguments we check. -/
private def treeTy : LDatatype Unit :=
  { name := "Tree", typeArgs := ["a"],
    constrs := [{ name := "Leaf", args := [] }], constrs_ne := rfl }

/-- The mutual block containing only `Tree`. -/
private def block : MutualDatatype Unit := [treeTy]

/-- `n` is absent from a `.tcons` whose head is not `n` and all of whose
    arguments are themselves `n`-absent. -/
private theorem tyNameAbsent_tcons {n h : String} {args : LMonoTys}
    (hne : h ≠ n) (hargs : ∀ a ∈ args, TyNameAbsent n a) :
    TyNameAbsent n (.tcons h args) := by
  intro happ
  cases happ with
  | head _ => exact hne rfl
  | arg _ _ t hmem ht => exact hargs t hmem ht

/-- A `.tcons` whose head is not `"arrow"` is not a binary arrow. -/
private theorem not_isBinaryArrow_of_ne {n : String} {args : LMonoTys}
    (h : n ≠ "arrow") : ¬ IsBinaryArrow (.tcons n args) := by
  rintro ⟨_, _, heq⟩
  simp only [LMonoTy.arrow, LMonoTy.tcons.injEq] at heq
  exact h heq.1

/-! ## `UniformOccur`: every use of `n` is applied to exactly `args` -/

/-- `a` (a bare type variable) trivially uses `List` uniformly. -/
example : UniformOccur "List" [.ftvar "a"] (.ftvar "a") := .ftvar _

/-- `List a` is a uniform use of `List a`. -/
example : UniformOccur "List" [.ftvar "a"] (.tcons "List" [.ftvar "a"]) := .self

/-- `Pair (List a) bool`: `List` occurs uniformly under the non-`List` head `Pair`
    (`bool = .tcons "bool" []` is itself a uniform, `List`-free, occurrence). -/
example :
    UniformOccur "List" [.ftvar "a"]
      (.tcons "Pair" [.tcons "List" [.ftvar "a"], .bool]) := by
  apply UniformOccur.other _ _ (by decide)
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with h | h <;> subst h
  · exact .self
  · exact .other _ _ (by decide) (by simp)

/-- `List bool` is NOT a uniform use of `List a` (`List` applied to `bool ≠ [a]`). -/
example : ¬ UniformOccur "List" [.ftvar "a"] (.tcons "List" [.bool]) := by
  intro h
  cases h with
  | other _ _ hne _ => exact hne rfl

/-! ## `ConstrArgWF`: not-nested and strictly-positive/uniform -/

/-- `Tree a` is a well-formed constructor-argument type: a direct recursive use. -/
example : ConstrArgWF block (.tcons "Tree" [.ftvar "a"]) := by
  refine ⟨.headBlock _ _ (by decide), ?_⟩
  apply StrictPosUnif.base _ (not_isBinaryArrow_of_ne (by decide))
  intro d hd
  simp only [block, treeTy, List.mem_cons, List.not_mem_nil, or_false] at hd
  subst hd
  exact .self

/-- `bool → Tree a` is well-formed: `Tree` is strictly positive (only in the
    codomain) and not nested. -/
example : ConstrArgWF block (.arrow .bool (.tcons "Tree" [.ftvar "a"])) := by
  refine ⟨.arrow _ _ ?_ (.headBlock _ _ (by decide)), ?_⟩
  · -- domain `bool` is not-nested
    exact .headOther _ _ (not_isBinaryArrow_of_ne (by decide)) (by decide)
      (fun _ _ _ hmem => absurd hmem (by simp)) (fun _ hmem => absurd hmem (by simp))
  apply StrictPosUnif.arrow
  · -- `Tree` is absent from the domain `bool`
    intro d hd
    simp only [block, treeTy, List.mem_cons, List.not_mem_nil, or_false] at hd
    subst hd
    exact tyNameAbsent_tcons (by decide) (by simp)
  · apply StrictPosUnif.base _ (not_isBinaryArrow_of_ne (by decide))
    intro d hd
    simp only [block, treeTy, List.mem_cons, List.not_mem_nil, or_false] at hd
    subst hd
    exact .self

/-- `List (Tree a)` is NOT well-formed: `Tree` is nested inside the non-block
    head `List`, which `NotNested` forbids. -/
example : ¬ ConstrArgWF block (.tcons "List" [.tcons "Tree" [.ftvar "a"]]) := by
  rintro ⟨hnn, _⟩
  generalize ht : (LMonoTy.tcons "List" [LMonoTy.tcons "Tree" [.ftvar "a"]]) = t at hnn
  cases hnn with
  | ftvar _ => simp at ht
  | bitvec _ => simp at ht
  | arrow _ _ _ _ => simp [LMonoTy.arrow] at ht
  | headBlock _ _ hmem =>
      obtain ⟨hn, _⟩ := LMonoTy.tcons.injEq .. |>.mp ht.symm
      subst hn; simp [block, treeTy] at hmem
  | headOther _ _ _ _ habs _ =>
      obtain ⟨hn, hargs⟩ := LMonoTy.tcons.injEq .. |>.mp ht.symm
      subst hn; subst hargs
      have hAbs : TyNameAbsent "Tree" (.tcons "Tree" [.ftvar "a"]) := by
        have := habs treeTy (by simp [block]) (.tcons "Tree" [.ftvar "a"]) (by simp)
        simpa [treeTy] using this
      exact hAbs (.head _)

/-- `(Tree a → bool) → Tree a` is NOT well-formed: `Tree` occurs negatively — to
    the left of an arrow — which strict positivity forbids. -/
example :
    ¬ ConstrArgWF block
        (.arrow (.arrow (.tcons "Tree" [.ftvar "a"]) .bool) (.tcons "Tree" [.ftvar "a"])) := by
  rintro ⟨_, hsp⟩
  -- The outer arrow's domain `Tree a → bool` must be `Tree`-absent, but `Tree`
  -- appears at its head, so the `arrow` case's positivity premise fails.
  cases hsp with
  | arrow _ _ hdomAbs _ =>
      have hAbs : TyNameAbsent "Tree" (.arrow (.tcons "Tree" [.ftvar "a"]) .bool) := by
        simpa [treeTy] using hdomAbs treeTy (by simp [block])
      -- `Tree` appears at the head of the arrow's domain.
      exact hAbs (.arg "arrow" _ (.tcons "Tree" [.ftvar "a"]) (by simp) (.head _))
  | base _ hnb _ => exact hnb ⟨_, _, rfl⟩

/-! ## Inhabitance: `TySymInhab` / `TyInhab` / `ConstrInhab` -/

/-- `MyUnit`, a datatype with a single nullary constructor. -/
private def unitTy : LDatatype Unit :=
  { name := "MyUnit", typeArgs := [], constrs := [{ name := "MkU", args := [] }],
    constrs_ne := rfl }

private def unitAdts : @TypeFactory Unit := #[[unitTy]]

/-- A datatype with a nullary constructor is inhabited (`TySymInhab.datatype`). -/
example : TySymInhab unitAdts "MyUnit" := by
  refine .datatype "MyUnit" unitTy { name := "MkU", args := [] } ?_ (by simp [unitTy]) ?_
  · simp [TypeFactory.getType, TypeFactory.allDatatypes, unitAdts, unitTy]
  · exact .mk _ (by simp)

/-- An unknown (non-datatype) symbol is inhabited (`TySymInhab.external`). -/
example : TySymInhab unitAdts "SomeUnknown" := by
  apply TySymInhab.external
  simp [TypeFactory.getType, TypeFactory.allDatatypes, unitAdts, unitTy]

/-- `Loop`, whose only constructor takes a `Loop` (`type Loop = C (x : Loop)`). -/
private def loopTy : LDatatype Unit :=
  { name := "Loop", typeArgs := [],
    constrs := [{ name := "C", args := [(⟨"x", ()⟩, .tcons "Loop" [])] }],
    constrs_ne := rfl }

private def loopAdts : @TypeFactory Unit := #[[loopTy]]

private theorem loop_getType : loopAdts.getType "Loop" = some loopTy := by
  simp [TypeFactory.getType, TypeFactory.allDatatypes, loopAdts, loopTy]

/-- `Loop` is NOT inhabited: its sole constructor requires a `Loop`, so the only
    way to derive `TySymInhab` cycles back to itself. As a least-fixpoint relation,
    no finite derivation exists — this is the whole point of the inductive
    formulation. Proved via the mutual recursor: any derivation about `Loop` feeds
    back through the induction hypotheses to `False`. -/
example : ¬ TySymInhab loopAdts "Loop" := by
  intro h
  refine TySymInhab.rec
    (motive_1 := fun t _ => t = .tcons "Loop" [] → False)
    (motive_2 := fun s _ => s = "Loop" → False)
    (motive_3 := fun c _ => c ∈ loopTy.constrs → False)
    ?ftvar ?bitvec ?tcons ?external ?datatype ?mk h rfl
  case ftvar => intro v heq; simp at heq
  case bitvec => intro sz heq; simp at heq
  case tcons =>
    intro name args _ _ ih2 _ heq
    obtain ⟨hn, _⟩ := LMonoTy.tcons.injEq .. |>.mp heq
    exact ih2 hn
  case external =>
    intro name hnone heq
    subst heq; rw [loop_getType] at hnone; simp at hnone
  case datatype =>
    intro name d c hget hmem _ ih3 heq
    subst heq
    rw [loop_getType] at hget
    obtain rfl := Option.some.injEq .. |>.mp hget.symm
    exact ih3 hmem
  case mk =>
    intro c _ ih1 hcmem
    simp [loopTy] at hcmem
    subst hcmem
    exact ih1 (⟨"x", ()⟩, .tcons "Loop" []) (by simp) rfl

end DatatypeWFTests
end Lambda
