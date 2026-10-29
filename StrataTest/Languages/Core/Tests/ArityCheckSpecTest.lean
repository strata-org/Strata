/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.Languages.Core.DatatypeTypeSpec
import all Strata.Languages.Core.DatatypeTypeSpec
import Strata.Languages.Core.FunctionTypeSpec
import all Strata.Languages.Core.FunctionTypeSpec
import Strata.Languages.Core.Factory
import all Strata.Languages.Core.Factory
import all Strata.DL.Lambda.LExprTypeEnv
import all Strata.DL.Lambda.TypeFactory

/-! ## Arity-check spec tests

Proof-level counterparts to `ArityCheckTest.lean`: the declarative typing specs
carry a well-kindedness (correct-arity) obligation, so a type that applies a
known constructor at the wrong arity (`Sequence a a`, `Sequence` being arity 1)
is rejected. Correct-arity types (`Sequence a`) remain well-kinded.
-/

namespace Core.ArityCheckSpecTest

open Lambda Core.TypeSpec

/-- Core context: `Sequence` is a known arity-1 type constructor. -/
private def C : LContext CoreLParams :=
  { LContext.default with
      functions := Core.Factory,
      knownTypes := Core.KnownTypes }

/-- The head constructor of `.tcons n args`, with its argument count, is one of
    its arities. -/
private theorem head_mem_getTypeConsArities (n : String) (args : List LMonoTy) :
    (n, args.length) ∈ getTypeConsArities (.tcons n args) := by
  simp [getTypeConsArities]

/-- `Sequence` is registered with arity 1 in Core's known types. -/
private theorem knownSequenceArity : Core.KnownTypes["Sequence"]? = some 1 := by
  have h : Core.KnownTypes = Std.HashMap.ofList
      ((Core.KnownLTys.map (fun ty => ty.toKnownType!)).map (fun x => (x.name, x.arity))) := by
    simp only [Core.KnownTypes, makeKnownTypes]
  rw [h]
  exact Std.HashMap.getElem?_ofList_of_mem (k := "Sequence") (v := 1) (by decide)
    (by decide) (by decide)

/-- `Sequence a a` is NOT well-kinded: `Sequence` has arity 1, not 2. -/
example : ¬ C.WellKindedTy (.tcons "Sequence" [.ftvar "a", .ftvar "a"]) := by
  intro h
  have hlookup := h "Sequence" 2 (head_mem_getTypeConsArities "Sequence" [.ftvar "a", .ftvar "a"])
  simp only [C, knownSequenceArity] at hlookup
  exact absurd hlookup (by decide)

/-- `Sequence a` (correct arity) IS well-kinded. -/
example : C.WellKindedTy (.tcons "Sequence" [.ftvar "a"]) := by
  intro ref n hmem
  simp only [getTypeConsArities, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at hmem
  obtain ⟨rfl, rfl⟩ := hmem
  exact knownSequenceArity

/-- The `FuncHasTypeA` signature obligation rejects `f<a>(x : Sequence a a) : int`:
    no proof exists, since `signatureWellKinded` is unsatisfiable. -/
example (h : FuncHasTypeA C default
    { name := ⟨"f", ()⟩, typeArgs := ["a"],
      inputs := [(⟨"x", ()⟩, .tcons "Sequence" [.ftvar "a", .ftvar "a"])],
      output := .int }) : False := by
  obtain ⟨ty', hEq, hwk⟩ := h.signatureWellKinded (.tcons "Sequence" [.ftvar "a", .ftvar "a"])
    (by simp [ListMap.values])
  -- Annotated `tyCompat` is equality, so `ty'` is the (bad-arity) type itself.
  subst hEq
  have hlookup := hwk "Sequence" 2 (head_mem_getTypeConsArities "Sequence" [.ftvar "a", .ftvar "a"])
  simp only [C, knownSequenceArity] at hlookup
  exact absurd hlookup (by decide)

/-- Alias `MySeq a := Sequence a`. -/
private def mySeqAlias : TypeAlias :=
  { name := "MySeq", typeArgs := ["a"], type := .tcons "Sequence" [.ftvar "a"] }

/-- `MySeq a` expands to `Sequence a` under `[mySeqAlias]`. -/
private theorem mySeq_expandsTo :
    TypeAlias.expandsTo [mySeqAlias] "MySeq" [.ftvar "a"] (.tcons "Sequence" [.ftvar "a"]) :=
  ⟨mySeqAlias, by
    simp [mySeqAlias, TypeAlias.expand, LMonoTy.openVars, LMonoTys.openVars,
      List.zip, List.zipWith]⟩

/-- Polymorphic path: the signature type `MySeq a` is not well-kinded as written
    (`MySeq` is unknown), but `instHasType.tyCompat` (alias-equivalence) matches it
    to the well-kinded `Sequence a`, so the obligation is satisfiable. -/
example :
    ∃ ty', instHasType.tyCompat [mySeqAlias] (.tcons "MySeq" [.ftvar "a"]) ty' ∧
      C.WellKindedTy ty' := by
  refine ⟨.tcons "Sequence" [.ftvar "a"], AliasEquiv.expand mySeq_expandsTo, ?_⟩
  intro ref n hmem
  simp only [getTypeConsArities, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at hmem
  obtain ⟨rfl, rfl⟩ := hmem
  exact knownSequenceArity

end Core.ArityCheckSpecTest
