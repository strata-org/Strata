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
import Strata.Languages.Core.Typing.Spec.DatatypeTypeSpec
import Strata.Languages.Core.Typing.Spec.FunctionTypeSpec
import Strata.Languages.Core.Typing.Spec.NamesWF
import Strata.Languages.Core.Typing.Props.CmdTypeSpecProps
import Strata.Languages.Core.Typing.Props.FunctionTypeProps
import Strata.Languages.Core.Typing.Props.ProcedureTypeProps
import Strata.DL.Lambda.Identifiers
import Strata.DL.Lambda.LExprTypeSpecProps
import all Strata.DL.Lambda.LExprTypeSpec
import all Strata.Languages.Core.Typing.Spec.ProgramTypeSpec
import all Strata.Languages.Core.Typing.Spec.ProcedureTypeSpec
import all Strata.Languages.Core.TypeSkolem
import Strata.Languages.Core.Typing.Spec.TypeSpecShared
import Strata.Languages.Core.IdentifiersProps
import Strata.DL.Lambda.LTyUnifyProps
import StrataTest.Languages.Core.Tests.TestUtil
import Strata.DL.Lambda.NamePrefixesProps
import all Strata.Languages.Core.Typing.Spec.CmdTypeSpec
import all Strata.Languages.Core.Typing.Spec.NamesWF

/-! ## Arity-check spec tests

Proof-level counterparts to `ArityCheckTest.lean`: a type that applies a known
constructor at the wrong arity (`Sequence a a`, `Sequence` being arity 1) is
rejected, both by the typing relation (`FuncWellTyped`) and by the typechecker
spec (`ValidWrittenTy`, which `FuncHasTypeExact` requires of written types), with or
without an alias in between. Correct-arity types (`Sequence a`) are accepted.
Further tests cover type synonyms, binder annotations, reserved names, measures and
recursion marks.
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

/-- `isSingleton<a>() : bool` is rejected: its signature does not mention `a`. -/
example (Γ : TContext Unit) (h : FuncHasTypeExact C Γ
    { name := ⟨"isSingleton", ()⟩, typeArgs := ["a"], inputs := [], output := .bool }) :
    False := by
  have hmem := h.typeArgsInSignature "a" List.mem_cons_self
  simp [ListMap.values, LMonoTy.bool, LMonoTy.freeVars, LMonoTys.freeVars] at hmem

/-- The non-recursive `f(x : int) : int decreases x` is rejected: only a recursive function may
    have a measure. -/
example (Γ : TContext Unit) (h : FuncHasTypeExact C Γ
    { name := ⟨"f", ()⟩, inputs := [(⟨"x", ()⟩, .int)], output := .int,
      measure := some (.fvar Core.coreLoc ⟨"x", ()⟩ (some .int)) }) : False := by
  have hnone := h.measureOnlyRecursive rfl
  simp at hnone

/-- `emptyLen() : int := Sequence.length Sequence.empty`, stored with `Sequence.empty` at
    `Sequence $__ty0`, is not well-typed: `$__ty0` is not a type parameter. -/
example (h : FuncWellTyped C default
    { name := ⟨"emptyLen", ()⟩, inputs := [], output := .int,
      body := some (.app Core.coreLoc
        (.op Core.coreLoc ⟨"Sequence.length", ()⟩
          (some (.arrow (.tcons "Sequence" [.ftvar "$__ty0"]) .int)))
        (.op Core.coreLoc ⟨"Sequence.empty", ()⟩ (some (.tcons "Sequence" [.ftvar "$__ty0"])))) }) :
    False := by
  have hscoped := h.annotsScoped
  simp [Strata.DL.Util.Func.exprs, annotTyVars, exprAnnotTys, LMonoTy.freeVars,
    LMonoTys.freeVars] at hscoped

/-- The recursive `f(b : bool) : int decreases b` is not well-typed: a measure has type `int` or
    a datatype, and `bool` is neither. -/
example (h : FuncWellTyped C default
    { name := ⟨"f", ()⟩, isRecursive := true, inputs := [(⟨"b", ()⟩, .bool)], output := .int,
      measure := some (.fvar Core.coreLoc ⟨"b", ()⟩ (some .bool)) }) : False := by
  obtain ⟨ty, hmem, hint | ⟨n, args, hcompat, hdt, -⟩⟩ := h.measureTyped _ rfl
  · obtain ⟨hA, -⟩ := hint
    generalize hint : LMonoTy.int = t at hA
    cases hA
    simp [LMonoTy.int, LMonoTy.bool] at hint
  · simp only [ListMap.find?, ite_eq_left, Option.some.injEq] at hmem
    subst hmem
    cases hcompat
    simp [C, LContext.default, TypeFactory.getType, TypeFactory.allDatatypes] at hdt

/-- A resolved type is invalid when it applies `Sequence` to two arguments. -/
example : ¬ ResolvedTyWF C TyVarAdmissibility.all
    (.tcons "Sequence" [.ftvar "a", .ftvar "a"]) := by
  intro h
  have hlookup := h.wellKinded "Sequence" 2
    (head_mem_getTypeConsArities "Sequence" [.ftvar "a", .ftvar "a"])
  simp only [C, knownSequenceArity] at hlookup
  exact absurd hlookup (by decide)

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

/-! ### Type synonyms -/

/-- `Map` is registered with arity 2 in Core's known types. -/
private theorem knownMapArity : Core.KnownTypes["Map"]? = some 2 := by
  rw [knownTypes_eq]
  exact Std.HashMap.getElem?_ofList_of_mem (k := "Map") (v := 2) (by decide)
    (by decide) (by decide)

/-- `Foo` is not registered in Core's known types. -/
private theorem knownFooAbsent : Core.KnownTypes["Foo"]? = none := by
  rw [knownTypes_eq]
  exact Std.HashMap.getElem?_ofList_of_contains_eq_false (by decide)

/-- `A` is not registered in Core's known types. -/
private theorem knownAAbsent : Core.KnownTypes["A"]? = none := by
  rw [knownTypes_eq]
  exact Std.HashMap.getElem?_ofList_of_contains_eq_false (by decide)

/-- The type `Foo` is not a valid source type in Core's context without aliases. -/
private theorem foo_not_valid {adm : TyVarAdmissibility} (r : LMonoTy) :
    ¬ SourceTyWF C adm [] (.tcons "Foo" []) r := by
  intro hsrc
  obtain ⟨hresolve, htype⟩ := hsrc
  cases hresolve with
  | tcons hargs hfind =>
    cases hargs
    have hlookup := htype.wellKinded "Foo" 0 (head_mem_getTypeConsArities "Foo" [])
    simp only [C, knownFooAbsent] at hlookup
    exact absurd hlookup (by decide)
  | alias hargs hfind => simp at hfind

/-- The type `Map int` is not a valid source type in Core's context without aliases: `Map` takes
    two arguments. -/
private theorem mapInt_not_valid {adm : TyVarAdmissibility} (r : LMonoTy) :
    ¬ SourceTyWF C adm [] (.tcons "Map" [.int]) r := by
  intro hsrc
  obtain ⟨hresolve, htype⟩ := hsrc
  cases hresolve with
  | tcons hargs hfind =>
    cases hargs with
    | cons hhead htail =>
      cases htail
      rename_i resolvedHead
      have hlookup :=
        htype.wellKinded "Map" 1 (head_mem_getTypeConsArities "Map" [resolvedHead])
      simp only [C, knownMapArity] at hlookup
      exact absurd hlookup (by decide)
  | alias hargs hfind => simp at hfind

/-- The body of a well-typed type synonym is a valid source type through no aliases. -/
private theorem wellTyped_syn_body {P : Program} {ts : TypeScopes} {syn : TypeSynonym}
    {md : Imperative.MetaData Expression} {C' : LContext CoreLParams}
    (h : DeclWellTyped P C ts (.type (.syn syn) md) C') :
    SourceTyWF C TyVarAdmissibility.all [] syn.type syn.type := by
  cases h with
  | type_syn _ _ _ _ _ hbody =>
    exact ⟨SourceTyResolves.self_of_knownInstance (fun _ hal => absurd hal List.not_mem_nil)
      syn.type hbody.knownInstance, hbody⟩

/-- A type synonym declaration satisfying the typechecker spec has a body that resolves, through
    the aliases in scope, to a valid type. -/
private theorem type_syn_inv {P : Program} {Γ Γ' : TContext Unit} {ts : TypeSynonym}
    {md : Imperative.MetaData Expression} {C' : LContext CoreLParams}
    (h : DeclHasType P C Γ (.type (.syn ts) md) C' Γ') :
    ∃ storedTy, SourceTyWF C TyVarAdmissibility.all Γ.aliases ts.type storedTy := by
  cases h with
  | type_syn _ _ _ _ hok =>
    obtain ⟨storedTy, hsyn⟩ := hok
    exact ⟨storedTy, hsyn.bodyTyped⟩

/-- `type A := Foo`. -/
private abbrev fooSyn : TypeSynonym := { name := "A", typeArgs := [], type := .tcons "Foo" [] }

/-- The typechecker spec rejects `type A := Foo`: `Foo` is neither an alias nor a registered
    type. -/
private theorem fooSyn_rejected (P : Program) (md : Imperative.MetaData Expression)
    (C' : LContext CoreLParams) (Γ' : TContext Unit) :
    ¬ DeclHasType P C {} (.type (.syn fooSyn) md) C' Γ' := by
  intro h
  obtain ⟨storedTy, hsrc⟩ := type_syn_inv h
  exact foo_not_valid _ hsrc

/-- The typechecker spec and well-typedness both reject `type A := Foo`. -/
example (P : Program) (md : Imperative.MetaData Expression) (C' : LContext CoreLParams)
    (Γ' : TContext Unit) (ts : TypeScopes) :
    ¬ DeclHasType P C {} (.type (.syn fooSyn) md) C' Γ'
      ∧ ¬ DeclWellTyped P C ts (.type (.syn fooSyn) md) C' :=
  ⟨fooSyn_rejected P md C' Γ',
    fun h => foo_not_valid _ (wellTyped_syn_body h)⟩

/-- `type A := Map int`. -/
private abbrev mapIntSyn : TypeSynonym :=
  { name := "A", typeArgs := [], type := .tcons "Map" [.int] }

/-- The typechecker spec rejects `type A := Map int`: `Map` takes two arguments. -/
private theorem mapIntSyn_rejected (P : Program) (md : Imperative.MetaData Expression)
    (C' : LContext CoreLParams) (Γ' : TContext Unit) :
    ¬ DeclHasType P C {} (.type (.syn mapIntSyn) md) C' Γ' := by
  intro h
  obtain ⟨storedTy, hsrc⟩ := type_syn_inv h
  exact mapInt_not_valid _ hsrc

/-- The typechecker spec and well-typedness both reject `type A := Map int`. -/
example (P : Program) (md : Imperative.MetaData Expression) (C' : LContext CoreLParams)
    (Γ' : TContext Unit) (ts : TypeScopes) :
    ¬ DeclHasType P C {} (.type (.syn mapIntSyn) md) C' Γ'
      ∧ ¬ DeclWellTyped P C ts (.type (.syn mapIntSyn) md) C' :=
  ⟨mapIntSyn_rejected P md C' Γ',
    fun h => mapInt_not_valid _ (wellTyped_syn_body h)⟩

/-- `type A a := Map a int` as stored in the alias scope. -/
private def mapAlias : TypeAlias :=
  { name := "A", typeArgs := ["a"], type := .tcons "Map" [.ftvar "a", .int] }

/-- `type B := A`. -/
private abbrev bareASyn : TypeSynonym := { name := "B", typeArgs := [], type := .tcons "A" [] }

/-- With `type A a := Map a int` in scope, the typechecker spec rejects `type B := A`: `A` takes
    one argument, and no type `A` is registered. -/
private theorem bareASyn_rejected (P : Program) (md : Imperative.MetaData Expression)
    (C' : LContext CoreLParams) (Γ' : TContext Unit) :
    ¬ DeclHasType P C { aliases := [mapAlias] } (.type (.syn bareASyn) md) C' Γ' := by
  intro h
  obtain ⟨storedTy, hresolve, htype⟩ := type_syn_inv h
  cases hresolve with
  | tcons hargs hfind =>
    cases hargs
    have hlookup := htype.wellKinded "A" 0 (head_mem_getTypeConsArities "A" [])
    simp only [C, knownAAbsent] at hlookup
    exact absurd hlookup (by decide)
  | alias hargs hfind =>
    cases hargs
    simp [mapAlias] at hfind

/-- With `type A a := Map a int` in scope, the typechecker spec rejects `type B := A`, and
    well-typedness rejects it in any scope: no type `A` is registered. -/
example (P : Program) (md : Imperative.MetaData Expression) (C' : LContext CoreLParams)
    (Γ' : TContext Unit) (ts : TypeScopes) :
    ¬ DeclHasType P C { aliases := [mapAlias] } (.type (.syn bareASyn) md) C' Γ'
      ∧ ¬ DeclWellTyped P C ts (.type (.syn bareASyn) md) C' := by
  refine ⟨bareASyn_rejected P md C' Γ', fun h => ?_⟩
  cases h with
  | type_syn _ _ _ _ _ hbody =>
    have hlookup := hbody.wellKinded "A" 0 (head_mem_getTypeConsArities "A" [])
    simp only [C, knownAAbsent] at hlookup
    exact absurd hlookup (by decide)

/-- `type $__tyA := int`. -/
private abbrev reservedSyn : TypeSynonym := { name := "$__tyA", typeArgs := [], type := .int }

/-- The name conditions on declarations accept `type $__tyA := int`: a type synonym may be
    named with a reserved prefix. -/
example (P : Program) (md : Imperative.MetaData Expression) (fns : String → Prop) :
    DeclNamesWF P fns (.type (.syn reservedSyn) md) :=
  trivial

/-! ### Binder annotations -/

/-- `forall x : Foo :: e` has no type: `Foo` is not a registered type. -/
example (m : CoreLParams.Metadata) (tr e : LExpr CoreLParams.mono) (ty : LTy) :
    ¬ LExpr.HasType C {} (.quant m .all "x" (some (.tcons "Foo" [])) tr e) ty := by
  intro h
  obtain ⟨r, hr⟩ := (LExpr.HasType.annot_valid_eq_left h).2.1 _ _ _ _ _ _ rfl
  exact foo_not_valid r hr

/-- `forall x : Map int :: e` has no type: `Map` takes two arguments. -/
example (m : CoreLParams.Metadata) (tr e : LExpr CoreLParams.mono) (ty : LTy) :
    ¬ LExpr.HasType C {} (.quant m .all "x" (some (.tcons "Map" [.int])) tr e) ty := by
  intro h
  obtain ⟨r, hsrc⟩ := (LExpr.HasType.annot_valid_eq_left h).2.1 _ _ _ _ _ _ rfl
  exact mapInt_not_valid r hsrc

/-- `(λx:Foo. e1) == (λy:Foo. e2)` has no type: `Foo` is not a registered type. -/
example (m m1 m2 : CoreLParams.Metadata) (e1 e2 : LExpr CoreLParams.mono) (ty : LTy) :
    ¬ LExpr.HasType C {}
      (.eq m (.abs m1 "x" (some (.tcons "Foo" [])) e1) (.abs m2 "y" (some (.tcons "Foo" [])) e2))
      ty := by
  intro h
  obtain ⟨ty1, h1⟩ := (LExpr.HasType.annot_valid_eq_left h).2.2 _ _ _ rfl
  obtain ⟨r, hr⟩ := (LExpr.HasType.annot_valid_eq_left h1).1 _ _ _ _ rfl
  exact foo_not_valid r hr

/-! ### Binder annotations under well-typedness -/

/-- `int` is registered at arity 0 in Core's known types. -/
private theorem knownIntArity : Core.KnownTypes["int"]? = some 0 := by
  rw [knownTypes_eq]
  exact Std.HashMap.getElem?_ofList_of_mem (k := "int") (v := 0) (by decide)
    (by decide) (by decide)

/-- The elaborated `forall x : Foo :: true` is not well-typed in any scope: `Foo` is not a
    registered type. -/
example (ts : TypeScopes) (m : CoreLParams.Metadata) :
    ¬ ExprWellTyped C ts
      (.quant m .all "x" (some (.tcons "Foo" [])) (.const m (.boolConst true))
        (.const m (.boolConst true)))
      .bool := by
  intro h
  have hk := h.2.1 (.tcons "Foo" []) (by simp [LExpr.binderAnnotations])
  simp [LMonoTy.knownInstance, LMonoTys.knownInstances, KnownTypes.contains,
    Identifiers.contains, C, knownFooAbsent] at hk

/-- The elaborated `forall x : int :: true` is well-typed in every scope. -/
example (ts : TypeScopes) (m : CoreLParams.Metadata) :
    ExprWellTyped C ts
      (.quant m .all "x" (some .int) (.const m (.boolConst true))
        (.const m (.boolConst true)))
      .bool := by
  refine ⟨.quant (.const rfl) (.const rfl), ?_, ⟨?_, ?_, ?_⟩⟩
  · intro t ht
    simp only [LExpr.binderAnnotations, Option.toList, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at ht
    subst ht
    simp [LMonoTy.knownInstance, LMonoTys.knownInstances, KnownTypes.contains,
      Identifiers.contains, KnownType.arity, C, knownIntArity]
  · intro x ann hx
    simp [LExpr.freeVars] at hx
  · intro o ty ho
    simp [LExpr.opAnnots] at ho
  · intro o ho
    simp [LExpr.getOps] at ho

/-! ### Variable declarations -/

/-- `var x : ∀a. a := *` is rejected under every environment of written type variables: a
    declared variable type must be a monotype. -/
example (Δ Δ' : WrittenEnv) (Γ Γ' : TContext Unit) (x : Expression.Ident)
    (md : Imperative.MetaData Expression) :
    ¬ CmdHasType C Δ Γ (.init x (.forAll ["a"] (.ftvar "a")) .nondet md) Γ' Δ' := by
  intro h
  cases h with
  | init_nondet _ _ _ _ _ _ _ _ _ hxty => exact absurd hxty (by simp)

/-- A fresh `var x : T := *` satisfies the typechecker spec when `T` is a monotype that is a valid
    source type and the stored type is well-kinded and alias-equivalent to `T`. -/
private theorem init_nondet_derivable (Γ : TContext Unit) (x : Expression.Ident)
    (md : Imperative.MetaData Expression) (t mty : LMonoTy)
    (hfind : Γ.types.find? x = none) (hfun : x.name ∉ C.functions)
    (hae : AliasEquiv Γ.aliases t mty)
    (hvalid : ValidDeclaredTy C Γ.aliases t)
    (hwk : C.WellKindedTy mty) :
    ∃ Γ' Δ', CmdHasType C (fun _ => none) Γ (.init x (.forAll [] t) .nondet md) Γ' Δ' := by
  have hinst : ScopedAnnotInst Γ.aliases C.rigidTypeVars (fun _ => none)
      Strata.Util.HMap.empty t mty := by
    refine ⟨fun _ _ => LMonoTy.subst_single_empty _, fun _ _ _ hbound => ?_, ?_⟩
    · exact absurd hbound (by simp)
    · rw [LMonoTy.subst_single_empty]
      exact hae
  exact ⟨_, _, .init_nondet _ Γ x _ mty t Strata.Util.HMap.empty md _ hfind hfun rfl
    ⟨hinst, hvalid⟩ hwk (TContext.Equiv.refl _)⟩

/-- `int` applies only registered constructors. -/
private theorem int_knownInstance : LMonoTy.knownInstance .int C.knownTypes = true := by
  simp [LMonoTy.knownInstance, LMonoTys.knownInstances, KnownTypes.contains,
    Identifiers.contains, KnownType.arity, C, knownIntArity]

/-- `int` is well-kinded. -/
private theorem int_wellKinded : C.WellKindedTy .int := by
  intro ref n hmem
  simp only [LMonoTy.int, getTypeConsArities, List.flatMap_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hmem
  obtain ⟨rfl, rfl⟩ := hmem
  exact knownIntArity

/-- `int` is a valid declared type. -/
private theorem int_valid : ValidDeclaredTy C [] .int :=
  ⟨.int,
    (SourceTyWF.self_of_knownInstance (fun _ hal => absurd hal (by simp))
      int_knownInstance).hresolve,
    ResolvedTyWF.of_wellKinded int_wellKinded
      (fun v hv => by simp [LMonoTy.freeVars, LMonoTys.freeVars] at hv)⟩

/-- `var x : b := *` satisfies the typechecker spec: a type variable is a valid declared type. -/
example (x : Expression.Ident) (md : Imperative.MetaData Expression)
    (hfun : x.name ∉ C.functions) :
    ∃ Γ' Δ', CmdHasType C (fun _ => none) {} (.init x (.forAll [] (.ftvar "b")) .nondet md)
      Γ' Δ' :=
  init_nondet_derivable {} x md (.ftvar "b") (.ftvar "b") rfl hfun AliasEquiv.refl
    ⟨_, SourceTyResolves.ftvar, ResolvedTyWF.ftvar (by decide)⟩
    (by intro ref n hmem; simp [getTypeConsArities] at hmem)

/-- `var x : int := *` satisfies the typechecker spec. -/
example (x : Expression.Ident) (md : Imperative.MetaData Expression)
    (hfun : x.name ∉ C.functions) :
    ∃ Γ' Δ', CmdHasType C (fun _ => none) {} (.init x (.forAll [] .int) .nondet md) Γ' Δ' :=
  init_nondet_derivable {} x md .int .int rfl hfun AliasEquiv.refl int_valid int_wellKinded

/-- `type A := int` as stored in the alias scope. -/
private def intAlias : TypeAlias := { name := "A", typeArgs := [], type := .int }

/-- With `type A := int` in scope, `var x : A := *` satisfies the typechecker spec. -/
example (x : Expression.Ident) (md : Imperative.MetaData Expression)
    (hfun : x.name ∉ C.functions) :
    ∃ Γ' Δ', CmdHasType C (fun _ => none) { aliases := [intAlias] }
      (.init x (.forAll [] (.tcons "A" [])) .nondet md) Γ' Δ' := by
  have hfind : [intAlias].find? (fun a => a.name == "A" && a.typeArgs.length == 0) =
      some intAlias := by
    simp [intAlias]
  have hint : ResolvedTyWF C TyVarAdmissibility.notGeneratedOrRigid (intAlias.expand []) :=
    (ResolvedTyWF.of_wellKinded (ty := LMonoTy.int) int_wellKinded
      (fun v hv => by simp [LMonoTy.freeVars, LMonoTys.freeVars] at hv) :
        ResolvedTyWF C TyVarAdmissibility.notGeneratedOrRigid .int)
  exact init_nondet_derivable { aliases := [intAlias] } x md (.tcons "A" []) .int rfl hfun
    (.expand ⟨intAlias, List.mem_singleton_self _, rfl, rfl, rfl⟩)
    ⟨_, SourceTyResolves.alias SourceTysResolve.nil hfind, hint⟩
    int_wellKinded

/-! ### Reserved names in written annotations -/

open Core.TestUtil (yId)

/-- The scope binding `y : int`. -/
private def Γy : TContext Unit := { types := [Strata.Util.HMap.ofList [(yId, .forAll [] .int)]] }

/-- `y` is bound to `int` in `Γy`. -/
private theorem yFind : Γy.types.find? yId = some (.forAll [] .int) := by
  simp [Γy, Strata.Util.HMaps.find?, Strata.Util.HMap.find?, Strata.Util.HMap.ofList]

/-- `(y : ann) == 0`. -/
private def yEqZero (m : CoreLParams.Metadata) (ann : LMonoTy) : Expression.Expr :=
  .eq m (.fvar m yId (some ann)) (.intConst m 0)

/-- No expression with a `$__ty0` binder annotation meets an admissibility requirement that
    rejects `$__ty0`. -/
private theorem ty0_binder_rejected {adm : TyVarAdmissibility} {e : Expression.Expr}
    (h : BinderAnnotTyVarsAdmissible adm e)
    (hmem : LMonoTy.ftvar "$__ty0" ∈ LExpr.binderAnnotations e) (hadm : adm "$__ty0" = false) :
    False := by
  have hv := h _ hmem "$__ty0" (by simp [LMonoTy.freeVars])
  rw [hadm] at hv
  exact absurd hv (by decide)

/-- `assert ((y : v) == 0)` is rejected by the typechecker spec when `v` is in the
    generator or rigid namespace. -/
private theorem assert_reserved_fvarAnnot_rejected (v : TyIdentifier)
    (hv : TyVarAdmissibility.notGeneratedOrRigid v = false)
    (Γ Γ' : TContext Unit) (Δ' : WrittenEnv) (m : CoreLParams.Metadata) (l : String)
    (md : Imperative.MetaData Expression) :
    ¬ CmdHasType C (fun _ => none) Γ (.assert l (yEqZero m (.ftvar v)) md) Γ' Δ' := by
  intro h
  cases h with
  | assert _ _ _ _ _ hann _ _ =>
    obtain ⟨r, hr⟩ := hann.1 (.ftvar v) (by simp [yEqZero, LExpr.fvarAnnotations])
    obtain ⟨hres, htype⟩ := hr
    cases hres
    cases htype with
    | ftvar hadm => rw [hv] at hadm; exact absurd hadm (by decide)

/-- `assert ((y : $__ty0) == 0)` is rejected by the typechecker spec: `$__ty0` is a generator
    name. -/
example (Γ Γ' : TContext Unit) (Δ' : WrittenEnv) (m : CoreLParams.Metadata) (l : String)
    (md : Imperative.MetaData Expression) :
    ¬ CmdHasType C (fun _ => none) Γ (.assert l (yEqZero m (.ftvar "$__ty0")) md) Γ' Δ' :=
  assert_reserved_fvarAnnot_rejected "$__ty0" (by decide) Γ Γ' Δ' m l md

/-- `assert ((y : $__rigid_a) == 0)` is rejected by the typechecker spec: `$__rigid_a` is a
    rigid-constant name. -/
example (Γ Γ' : TContext Unit) (Δ' : WrittenEnv) (m : CoreLParams.Metadata) (l : String)
    (md : Imperative.MetaData Expression) :
    ¬ CmdHasType C (fun _ => none) Γ (.assert l (yEqZero m (.ftvar "$__rigid_a")) md) Γ' Δ' :=
  assert_reserved_fvarAnnot_rejected "$__rigid_a" (by decide) Γ Γ' Δ' m l md

/-- `assert ((λ (x : $__ty0). x) 0)` is rejected by the typechecker spec: its binder annotation
    names the generator name `$__ty0`. -/
example (Γ Γ' : TContext Unit) (Δ' : WrittenEnv) (m : CoreLParams.Metadata) (l : String)
    (md : Imperative.MetaData Expression) :
    ¬ CmdHasType C (fun _ => none) Γ
      (.assert l (.app m (.abs m "x" (some (.ftvar "$__ty0")) (.bvar m 0)) (.intConst m 0)) md)
      Γ' Δ' := by
  intro h
  cases h with
  | assert _ _ _ _ _ hann _ _ =>
    exact ty0_binder_rejected hann.2 (by simp [LExpr.binderAnnotations]) (by decide)

/-- `if ((λ (x : $__ty0). x) true) {} else {}` is rejected by the typechecker spec: its
    condition's binder annotation names the generator name `$__ty0`. -/
example (P : Program) (Γ Δ : TContext Unit) (L : List String) (C' : LContext CoreLParams)
    (m : CoreLParams.Metadata) (md : Imperative.MetaData Expression) :
    ¬ StatementHasType P C Γ (fun _ => none) L
      (.ite (.det (.app m (.abs m "x" (some (.ftvar "$__ty0")) (.bvar m 0)) (.boolConst m true)))
        [] [] md) C' Δ (fun _ => none) := by
  intro h
  cases h with
  | ite_det _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hann _ _ _ _ =>
    exact ty0_binder_rejected hann.2 (by simp [LExpr.binderAnnotations]) (by decide)

/-- `int` is a registered type name. -/
private theorem int_containsName : C.knownTypes.containsName "int" := by
  simp only [KnownTypes.containsName, C]
  exact Std.HashMap.mem_iff_isSome_getElem?.mpr (by rw [knownIntArity]; rfl)

/-- `int` is a valid source type under the user-written type-variable policy. -/
private theorem int_valid_notGeneratedOrRigid :
    SourceTyWF C TyVarAdmissibility.notGeneratedOrRigid [] .int .int := by
  obtain ⟨hr, ht⟩ := (SourceTyWF.self_of_knownInstance (aliases := [])
    (fun _ hal => absurd hal (by simp)) int_knownInstance)
  cases ht with
  | tcons hknown _ => exact ⟨hr, .tcons hknown .nil⟩

/-- Reading the type variable `c` through an environment that binds `c` gives that binding. -/
private theorem instAnnotTy_ftvar_bound {Δ : WrittenEnv} {c : TyIdentifier} {t : LMonoTy}
    (hadm : TyVarAdmissibility.notGeneratedOrRigid c = true) (hbound : Δ c = some t) :
    instAnnotTy Δ (.ftvar c) = t := by
  have hfind : Strata.Util.HMaps.find? [restrictTo (readTyVar Δ) (.ftvar c)] c =
      some (readTyVar Δ c) := by
    rw [Strata.Util.HMaps.find?_single_scope]
    exact LExpr.find?_buildSubstFromFunction _ _ c (by simp [LMonoTy.freeVars])
  unfold instAnnotTy
  rw [LMonoTy.subst_ftvar_of_some hfind]
  simp only [readTyVar, hadm, hbound, ite_true, Option.getD_some]

/-- With `y : int` in scope, an assertion `(y : ann) == 0` with any label satisfies the
    typechecker spec when, read through `Δ`, `ann` becomes `ann'`, which instantiates to `int`;
    `ann` is a valid source type with no reserved type-variable name, and each of its type
    variables is rigid or bound in `Δ`. -/
private theorem assert_yEqZero_derivable (Δ : WrittenEnv) (m : CoreLParams.Metadata)
    (l : String) (md : Imperative.MetaData Expression) (ann ann' : LMonoTy)
    (hread : instAnnots Δ (yEqZero m ann) = yEqZero m ann')
    (hcompat : LExpr.AnnotCompat [] ann' .int)
    (hvalid : ∃ r, SourceTyWF C TyVarAdmissibility.notGeneratedOrRigid [] ann r)
    (hscope : ∀ v ∈ LMonoTy.freeVars ann, v ∈ C.rigidTypeVars ∨ (Δ v).isSome) :
    CmdHasType C Δ Γy (.assert l (yEqZero m ann) md) Γy Δ := by
  refine .assert Δ Γy l _ md Γy ?_ ?_ ?_ (TContext.Equiv.refl _)
  · rw [hread]
    exact .teq Γy m _ _ (.forAll [] .int)
      (.tvar_annotated Γy m yId (.forAll [] .int) .int [] ann' yFind rfl
        (openFull_forAll_nil .int []) hcompat)
      (.tint_const Γy m 0 int_containsName)
  · refine ⟨fun t ht => ?_, fun t ht => by simp [yEqZero, LExpr.binderAnnotations] at ht⟩
    simp only [yEqZero, LExpr.fvarAnnotations, Option.toList, List.append_nil,
      List.mem_singleton] at ht
    subst ht
    exact hvalid
  · intro t ht v hv
    simp only [yEqZero, LExpr.fvarAnnotations, LExpr.binderAnnotations, Option.toList,
      List.append_nil, List.mem_singleton] at ht
    subst ht
    exact hscope v hv

/-- The environment binding the written type variable `c` to `int`. -/
private def Δc : WrittenEnv := fun v => if v = "c" then some .int else none

/-- With `y : int` in scope and the written type variable `c` denoting `int`,
    `assert ((y : c) == 0)` with any label satisfies the typechecker spec. -/
example (m : CoreLParams.Metadata) (l : String) (md : Imperative.MetaData Expression) :
    CmdHasType C Δc Γy (.assert l (yEqZero m (.ftvar "c")) md) Γy Δc := by
  have hc : instAnnotTy Δc (.ftvar "c") = .int :=
    instAnnotTy_ftvar_bound (by decide) (by simp [Δc])
  refine assert_yEqZero_derivable Δc m l md _ .int ?_ LExpr.AnnotCompat.of_eq
    ⟨_, SourceTyResolves.ftvar, ResolvedTyWF.ftvar (by decide)⟩ ?_
  · simp only [yEqZero, instAnnots, Option.map_some, hc]
    rfl
  · intro v hv
    simp only [LMonoTy.freeVars, List.mem_singleton] at hv
    subst hv
    exact Or.inr (by simp [Δc])

/-- With `y : int` in scope, `assert ((y : int) == 0)` with any label satisfies the typechecker
    spec. -/
example (m : CoreLParams.Metadata) (l : String) (md : Imperative.MetaData Expression) :
    CmdHasType C (fun _ => none) Γy (.assert l (yEqZero m .int) md) Γy (fun _ => none) :=
  assert_yEqZero_derivable (fun _ => none) m l md .int .int (instAnnots_none _)
    LExpr.AnnotCompat.of_eq ⟨_, int_valid_notGeneratedOrRigid⟩
    (fun v hv => by simp [LMonoTy.freeVars, LMonoTys.freeVars] at hv)

/-! ### Reserved names in procedure conditions and top-level declarations -/

/-- The precondition `(y : ann) == 0`. -/
private def yPre (ann : LMonoTy) : Procedure.Check := { expr := yEqZero Core.coreLoc ann }

/-- A procedure `p(y : int)` with precondition `(y : ann) == 0` and an empty body. -/
private def yProc (ann : LMonoTy) : Procedure :=
  { header := { name := ⟨"p", ()⟩, typeArgs := [], inputs := [(yId, .int)], outputs := [] },
    spec := { preconditions := [("pre", yPre ann)], postconditions := [] },
    body := .structured [] false }

/-- The precondition of `yProc ann` is among its preconditions. -/
private theorem yPre_mem (ann : LMonoTy) : yPre ann ∈ (yProc ann).spec.preconditions.values := by
  simp [yProc, ListMap.values]

/-- A procedure whose precondition is `(y : $__ty0) == 0` is rejected by the typechecker spec:
    `$__ty0` is a generator name. -/
example (P : Program) (Γ : TContext Unit) : ¬ ProcHasType P C Γ (yProc (.ftvar "$__ty0")) := by
  intro h
  obtain ⟨p', hv, h⟩ := h
  obtain rfl := ProcAlphaVariant.eq_self_of_allowed (fun _ h => absurd h List.not_mem_nil) hv
  obtain ⟨r, hr⟩ := (h.preconditionsAnnots _ (yPre_mem _)).1 (.ftvar "$__ty0")
    (by simp [yPre, yEqZero, LExpr.fvarAnnotations])
  obtain ⟨hres, htype⟩ := hr
  cases hres
  cases htype with
  | ftvar hadm => exact absurd hadm (by decide)

/-- The precondition `(y : int) == 0` meets the requirement on written annotations in a scope
    without aliases. -/
example (Γ : TContext Unit) (hal : Γ.aliases = []) :
    ∀ c ∈ (yProc .int).spec.preconditions.values,
      WrittenAnnotsOk C (procInputContext Γ (yProc .int)) c.expr := by
  intro c hc
  simp only [yProc, ListMap.values, List.mem_singleton] at hc
  subst hc
  refine ⟨?_, fun t ht => by simp [yPre, yEqZero, LExpr.binderAnnotations] at ht⟩
  change FVarAnnotsWF C TyVarAdmissibility.notGeneratedOrRigid Γ.aliases _
  rw [hal]
  intro t ht
  simp only [yPre, yEqZero, LExpr.fvarAnnotations, Option.toList, List.append_nil,
    List.mem_singleton] at ht
  subst ht
  exact ⟨_, int_valid_notGeneratedOrRigid⟩

/-- A top-level function `f(u : int) : bool` with body `(u : ann) == u`. -/
private def fFunc (ann : LMonoTy) : Function :=
  { name := ⟨"f", ()⟩, typeArgs := [], inputs := [(⟨"u", ()⟩, .int)], output := .bool,
    body := some (.eq Core.coreLoc (.fvar Core.coreLoc ⟨"u", ()⟩ (some ann))
                  (.fvar Core.coreLoc ⟨"u", ()⟩ none)) }

/-- Declaring `fFunc ($__ty0)` at the top level is rejected by the typechecker spec: its
    body writes the generator name `$__ty0` on a free variable. -/
example (P : Program) (C' : LContext CoreLParams) (Γ Γ' : TContext Unit)
    (md : Imperative.MetaData Expression) :
    ¬ DeclHasType P C Γ (.func (fFunc (.ftvar "$__ty0")) md) C' Γ' := by
  intro h
  cases h with
  | func _ _ _ _ _ _ _ hv hf _ =>
    obtain rfl := FuncAlphaVariant.eq_self_of_allowed (fun _ h => absurd h List.not_mem_nil) hv
    have hbody : ∀ b, (fFunc (.ftvar "$__ty0")).body = some b →
        b ∈ (fFunc (.ftvar "$__ty0")).exprs := by
      intro b hb
      simp [Strata.DL.Util.Func.exprs, hb]
    obtain ⟨r, hr⟩ := (hf.writtenAnnotsOk _ (hbody _ rfl)).1 (.ftvar "$__ty0")
      (by simp [LExpr.fvarAnnotations])
    obtain ⟨hres, htype⟩ := hr
    cases hres
    cases htype with
    | ftvar hadm => exact absurd hadm (by decide)

/-- Declaring `fFunc int` is not well-typed into an output context that stores a different
    function under the name `f`. -/
example (P : Program) (C' : LContext CoreLParams) (ts : TypeScopes)
    (md : Imperative.MetaData Expression) (g : LFunc CoreLParams)
    (hg : C'.functions["f"]? = some g) (hne : g ≠ (fFunc .int).toLFunc) :
    ¬ DeclWellTyped P C ts (.func (fFunc .int) md) C' := by
  intro h
  cases h with
  | func _ _ _ _ _ _ _ hext =>
    obtain ⟨e, he, hagree⟩ := hext.contains_new _ (List.mem_singleton_self _)
    have hge : g = e := Option.some.inj (hg.symm.trans he)
    exact hne (hge.trans hagree)

/-- With no aliases in scope, declaring `fFunc int`, whose output type is `bool`, is rejected by
    the typechecker spec for an output context that stores under `f` a function whose output type
    is `int`. -/
example (P : Program) (C' : LContext CoreLParams) (Γ Γ' : TContext Unit)
    (md : Imperative.MetaData Expression) (hal : Γ.aliases = []) (g : LFunc CoreLParams)
    (hg : C'.functions["f"]? = some g) (hout : g.output = .int) :
    ¬ DeclHasType P C Γ (.func (fFunc .int) md) C' Γ' := by
  intro h
  cases h with
  | func _ _ _ _ _ _ _ hv _ hext =>
    obtain rfl := FuncAlphaVariant.eq_self_of_allowed (fun _ h => absurd h List.not_mem_nil) hv
    obtain ⟨e, he, hsig, -⟩ := hext.contains_new _ (List.mem_singleton_self _)
    have hge : g = e := Option.some.inj (hg.symm.trans he)
    have hoe := hsig.output
    rw [← hge, hout, hal] at hoe
    exact absurd (AliasEquiv.eq_of_nil hoe) (by decide)

/-- Every expression of `fFunc c` meets the requirement on written annotations: `c` is an
    ordinary type variable. -/
example (Γ : TContext Unit) :
    ∀ e ∈ (fFunc (.ftvar "c")).exprs,
      WrittenAnnotsOk C (funcContext Γ (fFunc (.ftvar "c"))) e := by
  intro b hb
  simp only [Strata.DL.Util.Func.exprs, fFunc, Option.toList, List.append_nil, List.map_nil,
    List.mem_singleton] at hb
  subst hb
  refine ⟨fun t ht => ?_, fun t ht => by simp [LExpr.binderAnnotations] at ht⟩
  simp only [LExpr.fvarAnnotations, Option.toList, List.append_nil, List.mem_singleton] at ht
  subst ht
  exact ⟨_, SourceTyResolves.ftvar, ResolvedTyWF.ftvar (by decide)⟩

/-- A recursive `f(x : int) : int` whose bare measure `x` is annotated at `ann`. -/
private def gFunc (ann : LMonoTy) : Function :=
  { name := ⟨"f", ()⟩, isRecursive := true, inputs := [(⟨"x", ()⟩, .int)], output := .int,
    measure := some (.fvar Core.coreLoc ⟨"x", ()⟩ (some ann)) }

/-- A recursive block declaring `gFunc ($__ty0)` is rejected by the typechecker spec: its
    bare measure is annotated with the generator name `$__ty0`. -/
example (P : Program) (C' : LContext CoreLParams) (Γ Γ' : TContext Unit)
    (md : Imperative.MetaData Expression) :
    ¬ DeclHasType P C Γ (.recFuncBlock [gFunc (.ftvar "$__ty0")] md) C' Γ' := by
  intro h
  cases h with
  | recFuncBlock _ _ _ _ _ _ _ _ _ _ _ hvars _ _ _ _ hfs _ =>
    obtain ⟨f', hf', hv⟩ := List.Rel₂.exists_of_mem_left hvars (List.mem_singleton_self _)
    obtain rfl := FuncAlphaVariant.eq_self_of_allowed (fun _ h => absurd h List.not_mem_nil) hv
    have hmeasure : ∀ m, (gFunc (.ftvar "$__ty0")).measure = some m →
        m ∈ (gFunc (.ftvar "$__ty0")).exprs := by
      intro m hm
      simp [Strata.DL.Util.Func.exprs, hm]
    obtain ⟨r, hr⟩ := ((hfs _ hf').writtenAnnotsOk _ (hmeasure _ rfl)).1
      (.ftvar "$__ty0") (by simp [LExpr.fvarAnnotations])
    obtain ⟨hres, htype⟩ := hr
    cases hres
    cases htype with
    | ftvar hadm => exact absurd hadm (by decide)

/-- The top-level axiom `(λ (x : $__ty0). x) true` is rejected by the typechecker spec:
    its binder annotation names the generator name `$__ty0`. -/
example (P : Program) (C' : LContext CoreLParams) (Γ Γ' : TContext Unit)
    (m : CoreLParams.Metadata) (md : Imperative.MetaData Expression) :
    ¬ DeclHasType P C Γ
      (.ax { name := "a",
               e := .app m (.abs m "x" (some (.ftvar "$__ty0")) (.bvar m 0)) (.boolConst m true) }
        md) C' Γ' := by
  intro h
  cases h with
  | ax _ _ _ _ hann =>
    exact ty0_binder_rejected hann.2 (by simp [LExpr.binderAnnotations]) (by decide)

/-! ### Names, type parameters, stored annotations and recursion marks of top-level declarations -/

/-- The axiom `(λ x. x) == (λ x. x)`, stored with `x` annotated at the generated type variable
    `$__ty0`, is not well-typed: an axiom has no type parameters. -/
example (P : Program) (C' : LContext CoreLParams) (ts : TypeScopes)
    (m : CoreLParams.Metadata) (md : Imperative.MetaData Expression) :
    ¬ DeclWellTyped P C ts
      (.ax { name := "A", e := .eq m (.abs m "x" (some (.ftvar "$__ty0")) (.bvar m 0))
                                   (.abs m "x" (some (.ftvar "$__ty0")) (.bvar m 0)) }
        md) C' := by
  intro h
  cases h with
  | ax _ _ _ _ hscoped =>
    simp [annotTyVars, exprAnnotTys, LMonoTy.freeVars] at hscoped

/-- The lemma `L<a, a>: true` is rejected: its type parameters repeat. -/
example (P : Program) (C' : LContext CoreLParams)
    (Γ Γ' : TContext Unit) (m : CoreLParams.Metadata) (md : Imperative.MetaData Expression) :
    ¬ DeclHasType P C Γ
      (.lemma { name := "L", typeArgs := ["a", "a"], e := .boolConst m true } md) C' Γ' := by
  intro h
  match h with
  | .lemma _ _ _ _ _ ⟨_, _, hl⟩ _ _ hnodup _ _ =>
    rw [hl] at hnodup
    exact absurd (nodup_of_renameTyArgList hnodup) (by decide : ¬ ["a", "a"].Nodup)

/-- A recursive block whose only member `fFunc int` is not marked recursive is rejected. -/
example (P : Program) (C' : LContext CoreLParams)
    (Γ Γ' : TContext Unit) (md : Imperative.MetaData Expression) :
    ¬ DeclHasType P C Γ (.recFuncBlock [fFunc .int] md) C' Γ' := by
  intro h
  cases h with
  | recFuncBlock _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hrec =>
    exact absurd (hrec _ (List.mem_singleton_self _)) (by simp [fFunc])

end Core.ArityCheckSpecTest
