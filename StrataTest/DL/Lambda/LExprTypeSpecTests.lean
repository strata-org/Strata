/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.DL.Lambda.LExprTypeSpec
import all Strata.DL.Lambda.LExprTypeEnv
import all Strata.DL.Lambda.LExprWF
import all Strata.DL.Lambda.Identifiers

/-! ## Typing-rule tests for Lambda expressions

For example, with no aliases, a binder annotation that applies a registered
type constructor to the wrong number of arguments is not a valid source type,
so an abstraction written with such an annotation has no typing derivation.
-/

namespace Lambda.LExprTypeSpecTests

open Lambda

private abbrev TP : LExprParams := ⟨Unit, Unit⟩

/-- The default context with `Map` registered as a type constructor with two
    arguments. -/
private def C : LContext TP :=
  { (LContext.default : LContext TP) with
      knownTypes := KnownTypes.default.insert "Map" 2 }

/-- With no aliases, `Map int` (the constructor `Map` applied to one argument)
    is not a valid source type: it resolves to itself, and `Map` is registered
    with two arguments, not one. -/
private theorem mapInt_not_sourceTyWF (r : LMonoTy) :
    ¬ SourceTyWF C TyVarAdmissibility.all [] (.tcons "Map" [.int]) r := by
  intro ⟨hres, hty⟩
  cases hres with
  | alias _ hfind => simp at hfind
  | tcons hargs _ =>
    cases hargs with
    | cons _ htail =>
      cases htail
      cases hty with
      | tcons hknown _ =>
        simp only [C, KnownTypes.contains, Identifiers.contains,
          Std.HashMap.getElem?_insert_self, List.length_cons,
          List.length_nil] at hknown
        exact absurd hknown (by decide)

/-- In a context without aliases, where `Map` is registered with two arguments,
    the abstraction `λ (x : Map int). x` has no type. The abstraction rule asks
    the written binder annotation to be a valid source type, which `Map int` is
    not; the other rules that can type an abstraction only reuse a typing of
    the same expression. -/
example (Γ : TContext TP.IDMeta) (hΓ : Γ.aliases = []) (ty : LTy) :
    ¬ LExpr.HasType C Γ
      (.abs () "x" (some (.tcons "Map" [.int])) (.bvar () 0)) ty := by
  intro h
  generalize he :
    (LExpr.abs () "x" (some (.tcons "Map" [.int])) (.bvar () 0) :
      LExpr TP.mono) = e at h
  induction h
  case tabs h_valid _ =>
    cases he
    obtain ⟨r, hr⟩ := h_valid _ rfl
    rw [hΓ] at hr
    exact mapInt_not_sourceTyWF r hr
  all_goals first
    | (cases he; done)
    | (rename_i ih; exact ih hΓ he)

/-- `Map a b`, the constructor `Map` applied to two type variables. -/
private abbrev mapAB : LMonoTy := .tcons "Map" [.ftvar "a", .ftvar "b"]

/-- In a context without aliases, where `Map` is registered with two arguments,
    the abstraction `λ (x : Map a b). x` has type `Map a b → Map a b`: its
    annotation applies `Map` to the right number of arguments, so it is a valid
    source type. -/
example (Γ : TContext TP.IDMeta) (hΓ : Γ.aliases = []) :
    LExpr.HasType C Γ (.abs () "x" (some mapAB) (.bvar () 0))
      (.forAll [] (.tcons "arrow" [mapAB, mapAB])) := by
  have h_fresh : LExpr.fresh (("x" : Identifier Unit), some mapAB)
      (.bvar () 0 : LExpr TP.mono) := by
    simp [LExpr.fresh, LExpr.freeVars]
  have h_open : LTy.openFull (.forAll [] mapAB) [] = mapAB := by
    simp only [LTy.openFull, LTy.boundVars, LTy.toMonoTypeUnsafe]
    rw [LExpr.subst_ofScopes_zip_eq_openVars _ _ _ rfl (by simp)]
    rfl
  have h_known :
      C.knownTypes.contains { name := "Map", metadata := 2 } = true := by
    simp [C, KnownTypes.contains, Identifiers.contains, KnownType.arity]
  refine LExpr.HasType.tabs Γ () "x" (("x" : Identifier Unit), some mapAB)
    (.forAll [] mapAB) (.bvar () 0) (.forAll [] mapAB) (some mapAB)
    h_fresh rfl rfl ?_ (.inr ⟨mapAB, rfl, LExpr.AnnotCompat.of_eq⟩) ?_
  · simp only [LExpr.varOpen, LExpr.substK, beq_self_eq_true, ite_true]
    exact LExpr.HasType.tvar_annotated (T := TP) _ () _ (.forAll [] mapAB)
      mapAB [] mapAB (Strata.Util.HMaps.find?_insert_self ..) rfl h_open
      LExpr.AnnotCompat.of_eq
  · rintro t ⟨⟩
    rw [hΓ]
    exact ⟨mapAB, .tcons (.cons .ftvar (.cons .ftvar .nil)) rfl,
      .tcons h_known (.cons (.ftvar rfl) (.cons (.ftvar rfl) .nil))⟩

end Lambda.LExprTypeSpecTests
