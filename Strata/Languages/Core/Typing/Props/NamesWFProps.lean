/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Typing.Spec.NamesWF
public import Strata.Languages.Core.Typing.Spec.ProgramTypeSpec
import Strata.DL.Lambda.LExprTypeEnvProps
import Strata.DL.Lambda.LTyWFCheckSound
import all Strata.DL.Lambda.LExprTypeEnv
import Strata.DL.Lambda.TypeFactoryProps
import Strata.Languages.Core.Typing.Props.FactoryRegistrationProps
import Strata.DL.Lambda.DatatypeFactoryWFProps
import all Strata.DL.Lambda.FactoryProps
import all Strata.DL.Lambda.Factory
import all Strata.DL.Lambda.TypeFactory
import all Strata.Languages.Core.Typing.Spec.ProgramTypeSpec
import all Strata.Languages.Core.Typing.Spec.DatatypeTypeSpec
import Strata.Languages.Core.Typing.Props.DatatypeTypeProps
import all Strata.Languages.Core.Typing.Spec.FunctionTypeSpec
import all Strata.Languages.Core.Typing.Spec.ProcedureTypeSpec
import Strata.Languages.Core.StatementProps
import all Strata.Languages.Core.Statement
import all Strata.Languages.Core.Typing.Spec.NamesWF
import all Strata.Languages.Core.Procedure
import Strata.Languages.Core.ProcedureProps

/-! ## Typing implies the name conditions

A program typed by the typechecker spec has valid names, and so does each declaration,
procedure and statement in it. Key theorems: `ProgramNamesWF.of_programHasType`,
`DeclsNamesWF.of_declsHasType`, `DeclNamesWF.of_declHasType`,
`ProcNamesWF.of_procHasTypeExact`, `StatementsNamesWF.of_statementsHasType` and
`StatementNamesWF.of_statementHasType`. -/

namespace Core

open Lambda Imperative

namespace TypeSpec

public section

/-- Registering a mutual datatype block keeps every function of the context and adds each
    function generated for the block. -/
theorem addMutualBlock_mem_functions {C C' : LContext CoreLParams}
    {block : List (LDatatype Unit)} (h : C.addMutualBlock block = .ok C') (n : String)
    (hn : n ∈ C.functions ∨ n ∈ MutualDatatype.generatedFuncNames block) :
    n ∈ C'.functions := by
  obtain ⟨fgen, hfgen, hlist⟩ := LContext.addMutualBlock_functions_toList h
  rw [Factory.mem_iff_mem_names]
  rcases hn with hold | hnew
  · rw [Factory.mem_iff_mem_names] at hold
    obtain ⟨g, hg, hgn⟩ := Array.mem_map.mp hold
    refine Array.mem_map.mpr ⟨g, ?_, hgn⟩
    rw [Array.mem_def, hlist]
    exact List.mem_append_left _ (Array.mem_def.mp hg)
  · have hnames := genBlockFactory_names hfgen
    rw [← hnames] at hnew
    obtain ⟨g, hg, hgn⟩ := List.mem_map.mp hnew
    refine Array.mem_map.mpr ⟨g, ?_, hgn⟩
    rw [Array.mem_def, hlist]
    exact List.mem_append_right _ hg

/-! ### Names in statements -/

mutual

/-- A statement typed by the typechecker spec with written type variables in scope has valid
    names. -/
theorem StatementNamesWF.of_statementHasType {P : Program}
    {C C' : LContext CoreLParams} {Γ Γ' : TContext Unit} {Δ Δ' : WrittenEnv}
    {L : List String} {s : Statement}
    (h : StatementHasType P C Γ Δ L s C' Γ' Δ') : StatementNamesWF P s :=
  match h with
  | .cmd .. => trivial
  | .block _ _ _ _ _ _ _ _ _ _ _ _ hb _ => StatementsNamesWF.of_statementsHasType hb
  | .ite_det _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ht he _ =>
    ⟨StatementsNamesWF.of_statementsHasType ht, StatementsNamesWF.of_statementsHasType he⟩
  | .ite_nondet _ _ _ _ _ _ _ _ _ _ _ _ _ _ ht he _ =>
    ⟨StatementsNamesWF.of_statementsHasType ht, StatementsNamesWF.of_statementsHasType he⟩
  | .loop _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hb _ =>
    StatementsNamesWF.of_statementsHasType hb
  | .exit .. => trivial
  | .typeDecl _ _ _ _ _ _ _ _ hprog _ _ _ => hprog

/-- A statement list typed by the typechecker spec with written type variables in scope has
    valid names. -/
theorem StatementsNamesWF.of_statementsHasType {P : Program}
    {C C' : LContext CoreLParams} {Γ Γ' : TContext Unit} {Δ Δ' : WrittenEnv}
    {L : List String} {ss : List Statement}
    (h : StatementsHasType P C Γ Δ L ss C' Γ' Δ') : StatementsNamesWF P ss :=
  match h with
  | .nil .. => trivial
  | .cons _ _ _ _ _ _ _ _ _ _ _ _ hs ht =>
    ⟨StatementNamesWF.of_statementHasType hs, StatementsNamesWF.of_statementsHasType ht⟩

end

/-! ### Names in procedures and declarations -/

/-- Statements have valid names when they do with their type annotations rewritten. -/
private theorem StatementsNamesWF.of_mapStmtsTys {P : Program}
    (f : LMonoTy → LMonoTy) (ss : List Statement) :
    StatementsNamesWF P (mapStmtsTys f ss) → StatementsNamesWF P ss := by
  induction ss using Block.mapExpr.induct (motive1 := fun s =>
      StatementNamesWF P (mapStmtTys f s) → StatementNamesWF P s) with
  | case1 c => simp [StatementNamesWF]
  | _ =>
    simp_all [mapStmtTys_block, mapStmtTys_ite, mapStmtTys_loop, mapStmtTys_exit,
      mapStmtTys_typeDecl, mapStmtsTys_nil, mapStmtsTys_cons, StatementNamesWF,
      StatementsNamesWF]

/-- A procedure has valid names when a renaming of its type parameters does. -/
private theorem ProcNamesWF.of_alphaVariant {P : Program}
    {C : LContext CoreLParams} {Γ : TContext Unit} {proc proc' : Procedure}
    (hv : ProcAlphaVariant C Γ proc proc') (h : ProcNamesWF P proc') :
    ProcNamesWF P proc := by
  obtain ⟨ren, -, rfl⟩ := hv
  unfold ProcNamesWF at h ⊢
  cases hb : proc.body with
  | cfg _ | abstract => trivial
  | structured ss =>
    simp only [Procedure.renameTypeArgs, Procedure.mapTys, hb] at h
    exact StatementsNamesWF.of_mapStmtsTys _ ss h

/-- A procedure typed by the typechecker spec has valid names. -/
theorem ProcNamesWF.of_procHasTypeExact {P : Program}
    {C : LContext CoreLParams} {Γ : TContext Unit} {proc : Procedure}
    (h : ProcHasTypeExact P C Γ proc) : ProcNamesWF P proc := by
  have hbody := h.bodyTyped
  unfold ProcNamesWF
  cases hshape : proc.body with
  | cfg _ | abstract => trivial
  | structured _ =>
    rw [hshape] at hbody
    match hbody with
    | .structured _ _ _ _ _ hss =>
      exact StatementsNamesWF.of_statementsHasType
        (C := { C with rigidTypeVars := C.rigidTypeVars ++ proc.header.typeArgs }) hss

/-- A declaration typed by the typechecker spec has valid names. -/
theorem DeclNamesWF.of_declHasType {P : Program} {C C' : LContext CoreLParams}
    {Γ Γ' : TContext Unit} {d : Decl}
    (h : DeclHasType P C Γ d C' Γ') : DeclNamesWF P d :=
  match h with
  | .proc _ _ _ _ ⟨_, hv, hp⟩ =>
    ProcNamesWF.of_alphaVariant hv (ProcNamesWF.of_procHasTypeExact hp)
  | .type_con .. | .type_syn .. | .type_data .. | .ax .. | .lemma .. | .distinct ..
  | .func .. | .recFuncBlock .. => trivial

/-- A declaration list typed by the typechecker spec has valid names. -/
theorem DeclsNamesWF.of_declsHasType {P : Program} {C C' : LContext CoreLParams}
    {Γ Γ' : TContext Unit} {ds : List Decl}
    (h : DeclsHasType P C Γ ds C' Γ') : DeclsNamesWF P ds := by
  induction h with
  | nil => trivial
  | cons =>
    rename_i hd _ ih
    exact ⟨DeclNamesWF.of_declHasType hd, ih⟩

/-- A program typed by the typechecker spec has valid names. -/
theorem ProgramNamesWF.of_programHasType {C : LContext CoreLParams} {Γ : TContext Unit}
    {P : Program} (h : ProgramHasType C Γ P) : ProgramNamesWF C P := by
  obtain ⟨hnodup, hidents, C', Γ', hds⟩ := h
  exact ⟨hnodup, hidents, DeclsNamesWF.of_declsHasType hds⟩

/-! ### Names under smaller programs -/

mutual

/-- Statement names stay valid under a program declaring only names the original declares. -/
private theorem StatementNamesWF.mono {P P' : Program}
    (hP : ∀ n ∈ P'.getNames, n ∈ P.getNames) :
    (s : Statement) → StatementNamesWF P s → StatementNamesWF P' s
  | .cmd _, h => h
  | .block _ b _, h => StatementsNamesWF.mono hP b h
  | .ite _ t e _, h => ⟨StatementsNamesWF.mono hP t h.1, StatementsNamesWF.mono hP e h.2⟩
  | .loop _ _ _ b _, h => StatementsNamesWF.mono hP b h
  | .exit _ _, h => h
  | .typeDecl _ _, h => fun n hn => h n (hP n hn)

/-- Statement-list names stay valid under a program declaring only names the original
    declares. -/
private theorem StatementsNamesWF.mono {P P' : Program}
    (hP : ∀ n ∈ P'.getNames, n ∈ P.getNames) :
    (ss : List Statement) → StatementsNamesWF P ss → StatementsNamesWF P' ss
  | [], h => h
  | s :: ss, h => ⟨StatementNamesWF.mono hP s h.1, StatementsNamesWF.mono hP ss h.2⟩

end

/-- Procedure names stay valid under a program declaring only names the original declares. -/
theorem ProcNamesWF.mono {P P' : Program} (hP : ∀ n ∈ P'.getNames, n ∈ P.getNames)
    {p : Procedure} (h : ProcNamesWF P p) : ProcNamesWF P' p := by
  unfold ProcNamesWF at h ⊢
  cases hb : p.body with
  | structured ss =>
    rw [hb] at h
    exact StatementsNamesWF.mono hP ss h
  | cfg _ | abstract => trivial

/-! ### Names under type-annotation maps -/

mutual

/-- Mapping the type annotations of a statement keeps its names valid. -/
theorem StatementNamesWF.mapStmtTys {P : Program} (f : LMonoTy → LMonoTy) :
    (s : Statement) → StatementNamesWF P s → StatementNamesWF P (mapStmtTys f s)
  | .cmd _, _ => by
    rw [mapStmtTys_cmd]
    trivial
  | .block _ b _, h => by
    rw [mapStmtTys_block]
    exact StatementsNamesWF.mapStmtsTys f b h
  | .ite _ t e _, h => by
    rw [mapStmtTys_ite]
    exact ⟨StatementsNamesWF.mapStmtsTys f t h.1, StatementsNamesWF.mapStmtsTys f e h.2⟩
  | .loop _ _ _ b _, h => by
    rw [mapStmtTys_loop]
    exact StatementsNamesWF.mapStmtsTys f b h
  | .exit _ _, h => by
    rw [mapStmtTys_exit]
    exact h
  | .typeDecl _ _, h => by
    rw [mapStmtTys_typeDecl]
    exact h

/-- Mapping the type annotations of a statement list keeps its names valid. -/
theorem StatementsNamesWF.mapStmtsTys {P : Program} (f : LMonoTy → LMonoTy) :
    (ss : List Statement) → StatementsNamesWF P ss → StatementsNamesWF P (mapStmtsTys f ss)
  | [], h => by
    rw [mapStmtsTys_nil]
    exact h
  | s :: ss, h => by
    rw [mapStmtsTys_cons]
    exact ⟨StatementNamesWF.mapStmtTys f s h.1, StatementsNamesWF.mapStmtsTys f ss h.2⟩

end

end -- public section

end TypeSpec
end Core
