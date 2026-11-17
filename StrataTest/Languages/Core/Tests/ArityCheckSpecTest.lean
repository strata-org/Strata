/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.Languages.Core.Typing.Spec.TypingSpec
import Strata.Languages.Core.Factory
import all Strata.Languages.Core.Factory
import all Strata.DL.Lambda.LExprTypeEnv
import all Strata.DL.Lambda.TypeFactory
import Strata.DL.Lambda.LTyWFCheckSound

/-! ## Arity-check spec tests

Proof-level counterparts to `ArityCheckTest.lean`: a type that applies a known
constructor at the wrong arity (`Sequence a a`, `Sequence` being arity 1) is
rejected, both by the typing relation (`FuncWellTyped`) and by the typechecker
spec (`ValidWrittenTy`, which `FuncHasType'` requires of written types), with or
without an alias in between. Correct-arity types (`Sequence a`) are accepted.
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

/-- Core's known types are the hash map built from its known type list. -/
private theorem knownTypes_eq : Core.KnownTypes = Std.HashMap.ofList
    ((Core.KnownLTys.map (fun ty => ty.toKnownType!)).map (fun x => (x.name, x.arity))) := by
  simp only [Core.KnownTypes, makeKnownTypes]

/-- `Sequence` is registered with arity 1 in Core's known types. -/
private theorem knownSequenceArity : Core.KnownTypes["Sequence"]? = some 1 := by
  rw [knownTypes_eq]
  exact Std.HashMap.getElem?_ofList_of_mem (k := "Sequence") (v := 1) (by decide)
    (by decide) (by decide)

/-- `MySeq` is not a known type in Core. -/
private theorem knownMySeqNone : Core.KnownTypes["MySeq"]? = none := by
  rw [knownTypes_eq]
  exact Std.HashMap.getElem?_ofList_of_contains_eq_false (by decide)

/-- `Sequence a a` is not well kinded: `Sequence` has arity 1, not 2. -/
private theorem sequence_twice_not_wellKinded :
    ¬ C.WellKindedTy (.tcons "Sequence" [.ftvar "a", .ftvar "a"]) := by
  intro h
  have hlookup := h "Sequence" 2 (head_mem_getTypeConsArities "Sequence" [.ftvar "a", .ftvar "a"])
  simp only [C, knownSequenceArity] at hlookup
  exact absurd hlookup (by decide)

/-- A valid written type that alias resolution leaves unchanged is well kinded. -/
private theorem wellKinded_of_valid_unchanged {aliases : List TypeAlias} {ty : LMonoTy}
    (hres : SourceTyResolves aliases ty ty) (h : ValidWrittenTy C aliases ty) :
    C.WellKindedTy ty := by
  obtain ⟨r, hr, hwf⟩ := h
  have heq := SourceTyResolves.unique hr hres
  subst heq
  exact hwf.wellKinded

/-- With no aliases, the written type `Sequence a a` is not valid: it resolves to
    itself, and `Sequence` has arity 1. -/
example : ¬ ValidWrittenTy C [] (.tcons "Sequence" [.ftvar "a", .ftvar "a"]) := by
  intro h
  have hres : SourceTyResolves [] (.tcons "Sequence" [.ftvar "a", .ftvar "a"])
      (.tcons "Sequence" [.ftvar "a", .ftvar "a"]) :=
    .tcons (.cons .ftvar (.cons .ftvar .nil)) rfl
  exact sequence_twice_not_wellKinded (wellKinded_of_valid_unchanged hres h)

/-- `Sequence a` (correct arity) is well kinded. -/
private theorem sequence_wellKinded : C.WellKindedTy (.tcons "Sequence" [.ftvar "a"]) := by
  intro ref n hmem
  simp only [getTypeConsArities, List.flatMap_cons, List.flatMap_nil,
    List.append_nil, List.mem_cons, List.not_mem_nil, or_false] at hmem
  obtain ⟨rfl, rfl⟩ := hmem
  exact knownSequenceArity

/-- The `FuncWellTyped` signature obligation rejects `f<a>(x : Sequence a a) : int`:
    no proof exists, since `signatureWellKinded` is unsatisfiable. -/
example (h : FuncWellTyped C default
    { name := ⟨"f", ()⟩, typeArgs := ["a"],
      inputs := [(⟨"x", ()⟩, .tcons "Sequence" [.ftvar "a", .ftvar "a"])],
      output := .int }) : False := by
  have hwk := h.signatureWellKinded (.tcons "Sequence" [.ftvar "a", .ftvar "a"])
    (by simp [ListMap.values])
  exact sequence_twice_not_wellKinded hwk

/-- Alias `MySeq a := Sequence a`. -/
private def mySeqAlias : TypeAlias :=
  { name := "MySeq", typeArgs := ["a"], type := .tcons "Sequence" [.ftvar "a"] }

/-- Polymorphic path: the signature type `MySeq a` names an unknown constructor, but it is a
    valid written type, since it resolves through `mySeqAlias` to the well-kinded `Sequence a`. -/
example : ValidWrittenTy C [mySeqAlias] (.tcons "MySeq" [.ftvar "a"]) := by
  have hfind : [mySeqAlias].find? (fun a => a.name == "MySeq" && a.typeArgs.length == 1)
      = some mySeqAlias := by decide
  have hres : SourceTyResolves [mySeqAlias] (.tcons "MySeq" [.ftvar "a"])
      (mySeqAlias.expand [.ftvar "a"]) := .alias (.cons .ftvar .nil) hfind
  have hexp : mySeqAlias.expand [.ftvar "a"] = .tcons "Sequence" [.ftvar "a"] := by
    simp [mySeqAlias, TypeAlias.expand, LMonoTy.openVars, LMonoTys.openVars, List.zip,
      List.zipWith]
  rw [hexp] at hres
  exact ⟨_, hres, ResolvedTyWF.of_wellKinded sequence_wellKinded (fun _ _ => rfl)⟩

/-- An alias applied at the wrong arity is not a valid written type: `MySeq a a`
    matches no alias, since `mySeqAlias` takes one argument, and `MySeq` is not a
    known type. -/
example : ¬ ValidWrittenTy C [mySeqAlias] (.tcons "MySeq" [.ftvar "a", .ftvar "a"]) := by
  intro h
  have hfind : [mySeqAlias].find? (fun a => a.name == "MySeq" && a.typeArgs.length == 2)
      = none := by decide
  have hres : SourceTyResolves [mySeqAlias] (.tcons "MySeq" [.ftvar "a", .ftvar "a"])
      (.tcons "MySeq" [.ftvar "a", .ftvar "a"]) := .tcons (.cons .ftvar (.cons .ftvar .nil)) hfind
  have hlookup := wellKinded_of_valid_unchanged hres h "MySeq" 2
    (head_mem_getTypeConsArities "MySeq" [.ftvar "a", .ftvar "a"])
  simp only [C, knownMySeqNone] at hlookup
  exact absurd hlookup (by decide)

end Core.ArityCheckSpecTest
