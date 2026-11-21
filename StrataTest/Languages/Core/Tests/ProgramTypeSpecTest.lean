/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.Languages.Core.Typing.Spec.ProgramTypeSpec
import Strata.DL.Lambda.NamePrefixesProps
import all Strata.Languages.Core.Typing.Spec.DatatypeTypeSpec
import all Strata.Languages.Core.Typing.Spec.FunctionTypeSpec
import all Strata.Languages.Core.Typing.Spec.CmdTypeSpec
import all Strata.Languages.Core.Typing.Spec.TypeSpecShared
import all Strata.Languages.Core.Procedure
import all Strata.Languages.Core.Statement
import all Strata.DL.Lambda.LExprType
import Strata.DL.Lambda.LTyUnifyProps
import Strata.Languages.Core.StatementProps
import all Strata.DL.Lambda.LExprTypeEnv
import all Strata.Util.ListMap
import all Strata.DL.Imperative.Cmd

/-! ## Declaration spec tests

A self-recursive datatype `List a := Nil | Cons(a, List a)`, written without aliases,
satisfies every premise of `DeclHasType.type_data`, and a type constructor named with a
reserved prefix satisfies `DeclHasType.type_con`. Renaming a reserved type
parameter of a procedure reaches its signature, conditions and a structured
body, and a
function with a reserved type parameter satisfies `DeclHasType.func` through
its renaming.
-/

namespace Core.ProgramTypeSpecTest

open Lambda Imperative Core.TypeSpec

/-- The datatype `List a := Nil | Cons(head : a, tail : List a)`. -/
private def listDt : LDatatype Unit :=
  { name := "List", typeArgs := ["a"]
    constrs :=
      [ { name := ⟨"Nil", ()⟩, args := [], testerName := "List..isNil" },
        { name := ⟨"Cons", ()⟩,
          args := [(⟨"head", ()⟩, .ftvar "a"),
                   (⟨"tail", ()⟩, .tcons "List" [.ftvar "a"])],
          testerName := "List..isCons" } ]
    constrs_ne := rfl }

/-- The block `[listDt]` meets every premise of `DeclHasType.type_data`, with the block itself
    as its alias-equivalent copy. -/
example {C C' : LContext CoreLParams} {P : Program} (md : MetaData Expression)
    (hadd : C.addMutualBlock [listDt] = .ok C') :
    DeclHasType P C ({} : TContext Unit) (.type (.data [listDt]) md) C' {} := by
  have hcompat : MutualBlockTyCompat ({} : TContext Unit) [listDt] [listDt] := by
    refine List.Rel₂.cons ?_ List.Rel₂.nil
    refine ⟨rfl, rfl, ?_⟩
    refine List.Rel₂.cons ⟨rfl, rfl, List.Rel₂.nil⟩ (List.Rel₂.cons ?_ List.Rel₂.nil)
    refine ⟨rfl, rfl, ?_⟩
    exact List.Rel₂.cons ⟨rfl, AliasEquiv.refl⟩
      (List.Rel₂.cons ⟨rfl, AliasEquiv.refl⟩ List.Rel₂.nil)
  exact .type_data C C' {} [listDt] md [listDt] hcompat hadd

/-- The type constructor `$__free_nil_refl_0`, named like the opaque type that closes a
    lemma's free type variable. -/
private def freeTc : TypeConstructor := { name := "$__free_nil_refl_0", params := [] }

/-- `$__free_nil_refl_0` starts with a reserved prefix. -/
example : isAllowedName "$__free_nil_refl_0" = false := by
  rw [isAllowedName_eq_toList]
  decide

/-- A type declaration named with a reserved prefix satisfies `DeclHasType.type_con` whenever
    the type can be registered. -/
example {C C' : LContext CoreLParams} {P : Program} {Γ : TContext Unit}
    (md : MetaData Expression)
    (hadd : C.addKnownTypeWithError { name := freeTc.name, metadata := freeTc.numargs } default =
      .ok C') :
    DeclHasType P C Γ (.type (.con freeTc) md) C' Γ :=
  .type_con C C' Γ freeTc md hadd

/-- The type parameter `$__ty0`, with a reserved prefix, renamed to `a`. -/
private def ren0 : List (String × String) := [("$__ty0", "a")]

/-- Renaming `$__ty0` to `a` sends the type variable `$__ty0` to `a`. -/
private theorem subst_ren0 :
    LMonoTy.subst (Subst.ofRenaming [("$__ty0", "a")]) (.ftvar "$__ty0") =
      .ftvar "a" := by
  apply LMonoTy.subst_ftvar_of_some
  rw [Subst.ofRenaming, Strata.Util.HMaps.find?_single_scope,
    Strata.Util.HMap.find?_ofList_map_snd,
    Strata.Util.HMap.find?_ofList_findSome?]
  rfl

/-- `x` annotated with the type variable `t`. -/
private def xAt (t : String) : Expression.Expr :=
  .fvar Core.valueLoc ⟨"x", ()⟩ (some (.ftvar t))

/-- The procedure `p<t>(x : t) returns (r : t)` with precondition and
    postcondition `(x : t) == (x : t)` and body `var y : t := *`. -/
private def procAt (t : String) : Procedure :=
  { header := { name := ⟨"p", ()⟩, typeArgs := [t],
                inputs := [(⟨"x", ()⟩, .ftvar t)],
                outputs := [(⟨"r", ()⟩, .ftvar t)] },
    spec := { preconditions := [("pre", { expr := .eq Core.valueLoc (xAt t) (xAt t) })],
              postconditions :=
                [("post", { expr := .eq Core.valueLoc (xAt t) (xAt t) })] },
    body := .structured
      [Statement.init ⟨"y", ()⟩ (.forAll [] (.ftvar t)) .nondet .empty] false }

/-- Renaming `$__ty0` to `a` renames it in the type parameters, the input and
    output types, the annotations of both conditions and the declared type of
    the structured body's variable. -/
example : (procAt "$__ty0").renameTypeArgs ren0 = procAt "a" := by
  simp [Procedure.renameTypeArgs, Procedure.mapTys, procAt, xAt, ren0, renameTyArgList,
    mapExprTys, mapStmtsTys_cons, mapStmtsTys_nil, mapStmtTys_cmd, mapCmdTys, mapCmdWith,
    mapLTyTys, ExprOrNondet.map, LExpr.replaceUserProvidedType, subst_ren0]

/-- The function `f<t>(x : t) : t := x`. -/
private def idAt (t : String) : Function :=
  { name := ⟨"f", ()⟩, typeArgs := [t], inputs := [(⟨"x", ()⟩, .ftvar t)],
    output := .ftvar t, body := some (.fvar Core.valueLoc ⟨"x", ()⟩ none) }

/-- Renaming `$__ty0` to `a` turns `f<$__ty0>` into `f<a>`. -/
private theorem idAt_rename :
    (idAt "$__ty0").renameTypeArgs ren0 = idAt "a" := by
  unfold LFuncDefined.renameTypeArgs LFuncDefined.applyTypeSubst
    LExpr.applyTypeSubst
  simp only [idAt, Option.map_some]
  split
  · simp [ren0, renameTyArgList, subst_ren0]
  · simp [ren0, renameTyArgList, subst_ren0, LExpr.replaceUserProvidedType]

/-- `f<a>(x : a) : a := x` satisfies the typechecker spec for functions in the
    empty type scope, when `x` is not a function of `C`. -/
private theorem idAt_a_hasType {C : LContext CoreLParams}
    (hx : "x" ∉ C.functions) : FuncHasTypeExact C {} (idAt "a") := by
  have hfv : LMonoTy.freeVars
      (LMonoTy.mkArrow' (idAt "a").output (idAt "a").inputs.values) =
        ["a", "a"] := by rfl
  have hvalid : ValidWrittenTy C [] (.ftvar "a") :=
    ⟨.ftvar "a", ⟨.ftvar, .ftvar rfl⟩⟩
  have hexprs : (idAt "a").exprs = [.fvar Core.valueLoc ⟨"x", ()⟩ none] := by rfl
  have hkeys : (idAt "a").inputs.keys = [⟨"x", ()⟩] := rfl
  have hnodup : (idAt "a").inputs.keys.Nodup := by
    rw [hkeys]
    decide
  have hfind : (funcContext {} (idAt "a")).types.find? ⟨"x", ()⟩ =
      some (.forAll [] (.ftvar "a")) := by
    show Strata.Util.HMaps.find? [formalsScope (idAt "a").inputs] ⟨"x", ()⟩ = _
    rw [Strata.Util.HMaps.find?_single_scope, formalsScope]
    simp [Strata.Util.HMap.find?_ofList_findSome?, idAt]
  have hnoAnnots : ∀ e ∈ (idAt "a").exprs,
      LExpr.fvarAnnotations e = [] ∧ LExpr.binderAnnotations e = [] := by
    intro e he
    rw [hexprs, List.mem_singleton] at he
    subst he
    exact ⟨rfl, rfl⟩
  refine
    { inputsNodup := hnodup
      typeArgsNodup := by decide
      typeArgsNotReserved := ?_
      noUndeclaredVars := ?_
      typeArgsInSignature := ?_
      signatureWellKinded := ?_
      bodyTyped := ?_
      measureOnlyRecursive := fun _ => rfl
      measureTyped := fun _ h => nomatch h
      preconditionsTyped := fun _ h => nomatch h
      axiomsTyped := fun _ h => nomatch h
      annotsScoped := ?_
      writtenAnnotsOk := ?_
      formalsNotFunctions := ?_
      constrNoBody := fun h => nomatch h }
  · intro ta hta
    rw [List.mem_singleton.mp hta, isAllowedName_eq_toList]
    decide
  · intro v hv
    rw [hfv] at hv
    rcases List.mem_cons.mp hv with rfl | hv'
    · exact List.mem_singleton_self _
    · rw [List.mem_singleton.mp hv']
      exact List.mem_singleton_self _
  · intro ta hta
    rw [List.mem_singleton.mp hta, hfv]
    exact List.mem_cons_self
  · intro ty hty
    rcases List.mem_cons.mp hty with rfl | hty'
    · exact hvalid
    · rw [List.mem_singleton.mp hty']
      exact hvalid
  · intro body hbody
    cases hbody
    exact .tvar _ _ _ _ hfind
  · intro e he t ht
    obtain ⟨hf, hb⟩ := hnoAnnots e he
    rw [hf, hb] at ht
    nomatch ht
  · intro e he
    obtain ⟨hf, hb⟩ := hnoAnnots e he
    refine ⟨fun t ht => ?_, fun t ht => ?_⟩
    · rw [hf] at ht
      nomatch ht
    · rw [hb] at ht
      nomatch ht
  · intro id hid
    rw [hkeys, List.mem_singleton] at hid
    rw [hid]
    exact hx

/-- The function `f<$__ty0>(x : $__ty0) : $__ty0 := x`, whose type parameter
    has a reserved prefix, satisfies `DeclHasType.func` through its renaming to
    `f<a>`, whenever `f<a>` can be registered, neither `f` nor `x` is a function
    of `C`, and `a` is not a rigid type variable of `C`. -/
example {C C' : LContext CoreLParams} {P : Program} (md : MetaData Expression)
    (hf : "f" ∉ C.functions) (hx : "x" ∉ C.functions)
    (hrigid : "a" ∉ C.rigidTypeVars)
    (hext : FactoryExtendedBy (FuncEntryOk {}) C C' [(idAt "a").toLFunc]) :
    DeclHasType P C {} (.func (idAt "$__ty0") md) C' {} := by
  have hfresh : TContext.isFresh (T := CoreLParams) "a" ({} : TContext Unit) :=
    fun _ _ h => nomatch h
  have hmentioned :
      (idAt "$__ty0").mentionedTyVars = ["$__ty0", "$__ty0", "$__ty0"] := by
    rfl
  have hreserved : isAllowedName "$__ty0" = false := by
    rw [isAllowedName_eq_toList]
    decide
  have hren : TyArgRenaming C {} (idAt "$__ty0").typeArgs
      (idAt "$__ty0").mentionedTyVars ren0 := by
    rw [hmentioned]
    refine ⟨⟨by decide, by decide, ?_⟩, ?_⟩
    · intro p hp
      rw [List.mem_singleton.mp hp]
      decide
    · intro p hp
      rw [List.mem_singleton.mp hp]
      exact ⟨hreserved, hrigid, hfresh⟩
  have hv : FuncAlphaVariant C {} (idAt "$__ty0") (idAt "a") :=
    ⟨ren0, hren, idAt_rename.symm⟩
  exact .func C C' {} (idAt "$__ty0") (idAt "a") md (fun h => nomatch h) hf hv
    (idAt_a_hasType hx) hext

end Core.ProgramTypeSpecTest
