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

A program typed by the typechecker spec has valid names, and so does each
declaration, function, procedure, statement and command in it. Key theorems:
`ProgramNamesWF.of_programHasType`, `DeclsNamesWF.of_declsHasType`,
`DeclNamesWF.of_declHasType`, `ProcNamesWF.of_procHasTypeExact`,
`FuncNamesWF.of_funcHasTypeExact`, `StatementsNamesWF.of_statementsHasType`,
`StatementNamesWF.of_statementHasType` and `CmdNamesWF.of_cmdExtHasType`.
Typing a statement list leaves the function table unchanged
(`StatementsHasType.functions_eq`), and a typed declaration's context holds the
functions it introduces (`DeclHasType.extendScope_subset`). -/

namespace Core

open Lambda Imperative

namespace TypeSpec

public section

/-! ### Function tables -/

/-- Typing a statement leaves the function table of the context unchanged. -/
private theorem StatementHasType.functions_eq {P : Program}
    {C C' : LContext CoreLParams} {Γ Γ' : TContext Unit} {Δ Δ' : WrittenEnv}
    {L : List String} {s : Statement}
    (h : StatementHasType P C Γ Δ L s C' Γ' Δ') : C'.functions = C.functions := by
  cases h with
  | typeDecl =>
    rename_i hadd _
    exact addKnownTypeWithError_functions_eq _ _ _ _ hadd
  | _ => rfl

/-- Typing a statement list leaves the function table of the context unchanged. -/
theorem StatementsHasType.functions_eq {P : Program}
    {C C' : LContext CoreLParams} {Γ Γ' : TContext Unit} {Δ Δ' : WrittenEnv}
    {L : List String} {ss : List Statement}
    (h : StatementsHasType P C Γ Δ L ss C' Γ' Δ') : C'.functions = C.functions :=
  match h with
  | .nil _ _ _ _ _ _ => rfl
  | .cons _ _ _ _ _ _ _ _ _ _ _ _ hs ht =>
    (StatementsHasType.functions_eq ht).trans hs.functions_eq

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

/-- A renaming of a function's type parameters keeps its name. -/
private theorem FuncAlphaVariant.name_eq {C : LContext CoreLParams} {Γ : TContext Unit}
    {func f' : Function} (h : FuncAlphaVariant C Γ func f') : f'.name = func.name := by
  obtain ⟨ren, -, rfl⟩ := h
  exact LFuncDefined.renameTypeArgs_name func ren

/-- A renaming of a function's type parameters keeps its formals. -/
private theorem FuncAlphaVariant.inputs_keys {C : LContext CoreLParams} {Γ : TContext Unit}
    {func f' : Function} (h : FuncAlphaVariant C Γ func f') :
    f'.inputs.keys = func.inputs.keys := by
  obtain ⟨ren, -, rfl⟩ := h
  exact LFuncDefined.renameTypeArgs_inputs_keys func ren

/-- The functions in scope after a declaration are functions of the output table, when the scope
    before it consisted of functions of the input table, the output table keeps every input
    function, and it holds each function the declaration introduces. -/
theorem Decl.extendScope_subset {C C' : LContext CoreLParams} {d : Decl} {fns : String → Prop}
    (hfns : ∀ n, fns n → n ∈ C.functions)
    (hkeep : ∀ n, n ∈ C.functions → n ∈ C'.functions)
    (hadded : ∀ n ∈ d.funcNames.map (·.name), n ∈ C'.functions) :
    ∀ n, d.extendScope fns n → n ∈ C'.functions
  | n, .inl hold => hkeep n (hfns n hold)
  | n, .inr hnew => hadded n hnew

/-- The functions in scope after a typed declaration are functions of its output context, when
    the scope before it consisted of functions of its input context. -/
theorem DeclHasType.extendScope_subset {P : Program}
    {C C' : LContext CoreLParams} {Γ Γ' : TContext Unit} {d : Decl}
    {fns : String → Prop} (hfns : ∀ n, fns n → n ∈ C.functions)
    (h : DeclHasType P C Γ d C' Γ') :
    ∀ n, d.extendScope fns n → n ∈ C'.functions := by
  refine And.elim (Decl.extendScope_subset hfns) ?_
  match h with
  | .type_con _ _ _ _ _ hadd =>
    exact ⟨fun _ hn => (addKnownTypeWithError_functions_eq _ _ _ _ hadd) ▸ hn, nofun⟩
  | .type_syn .. => exact ⟨fun _ hn => hn, nofun⟩
  | .type_data _ _ _ _ _ _ hcompat hadd =>
    refine ⟨fun n hn => addMutualBlock_mem_functions hadd n (.inl hn), fun n hn => ?_⟩
    simp only [Decl.funcNames, List.map_map] at hn
    obtain ⟨m, hm, rfl⟩ := List.mem_map.mp hn
    have hmr : m ∈ MutualDatatype.generatedFuncNames _ :=
      (MutualBlockTyCompat.generatedFuncNames_eq hcompat) ▸ hm
    exact addMutualBlock_mem_functions hadd _ (.inr hmr)
  | .ax .. => exact ⟨fun _ hn => hn, nofun⟩
  | .lemma .. => exact ⟨fun _ hn => hn, nofun⟩
  | .distinct .. => exact ⟨fun _ hn => hn, nofun⟩
  | .proc .. => exact ⟨fun _ hn => hn, nofun⟩
  | .func _ _ _ _ _ _ _ _ hv _ hext =>
    refine ⟨fun _ hn => hext.mem_old hn, fun n hn => ?_⟩
    simp only [Decl.funcNames, List.map_cons, List.map_nil, List.mem_singleton] at hn
    subst hn
    have hmem := hext.mem_new (List.mem_singleton_self _)
    rw [show (LFuncDefined.toLFunc _).name = _ from hv.name_eq] at hmem
    exact hmem
  | .recFuncBlock _ _ _ _ _ _ _ _ _ _ _ _ hvars _ hfull _ hext _ _ =>
    refine ⟨fun _ hn => hext.mem_old hn, fun n hn => ?_⟩
    simp only [Decl.funcNames, List.map_map] at hn
    obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hn
    obtain ⟨f', hf', hv⟩ := List.Rel₂.exists_of_mem_left hvars hf
    subst hfull
    have hmem := hext.mem_new (List.mem_map_of_mem (f := fun g : Function => g.toLFunc) hf')
    rw [show (LFuncDefined.toLFunc f').name = f.name from hv.name_eq] at hmem
    exact hmem

/-! ### Names in commands and statements -/

/-- An imperative command typed as an extended command with written type variables in scope
    has valid names for any function scope made of functions of `C`. -/
theorem CmdNamesWF.of_cmdExtHasType
    {C : LContext CoreLParams} {P : Program} {Δ Δ' : WrittenEnv} {Γ Γ' : TContext Unit}
    {c : Cmd Expression} {fns : String → Prop} (hfns : ∀ n, fns n → n ∈ C.functions)
    (h : CmdExtHasType C P Δ Γ (.cmd c) Γ' Δ') : CmdNamesWF fns c :=
  match h with
  | .cmd _ _ _ _ _ hc =>
    match hc with
    | .init_det _ _ _ _ _ _ _ _ _ _ _ hfun _ _ _ _ _ _ _ _ =>
      fun hf => hfun (hfns _ hf)
    | .init_nondet _ _ _ _ _ _ _ _ _ _ hfun _ _ _ _ => fun hf => hfun (hfns _ hf)
    | .set_det .. => trivial
    | .set_nondet .. => trivial
    | .assert .. => trivial
    | .assume .. => trivial
    | .cover .. => trivial

/-- An extended command typed with written type variables in scope, as a statement, has valid
    names for any function scope made of functions of `C`. -/
private theorem StatementNamesWF.of_cmdExtHasType
    {C : LContext CoreLParams} {P : Program} {Δ Δ' : WrittenEnv} {Γ Γ' : TContext Unit}
    {c : Command} {fns : String → Prop} (hfns : ∀ n, fns n → n ∈ C.functions)
    (h : CmdExtHasType C P Δ Γ c Γ' Δ') : StatementNamesWF P fns (.cmd c) := by
  cases c with
  | cmd c' => exact CmdNamesWF.of_cmdExtHasType hfns h
  | call => trivial

mutual

/-- A statement typed by the typechecker spec with written type variables in scope has valid
    names for any function scope made of functions of `C`. -/
theorem StatementNamesWF.of_statementHasType {P : Program}
    {C C' : LContext CoreLParams} {Γ Γ' : TContext Unit} {Δ Δ' : WrittenEnv}
    {L : List String} {s : Statement} {fns : String → Prop}
    (hfns : ∀ n, fns n → n ∈ C.functions)
    (h : StatementHasType P C Γ Δ L s C' Γ' Δ') : StatementNamesWF P fns s :=
  match h with
  | .cmd _ _ _ _ _ _ _ _ hc _ => StatementNamesWF.of_cmdExtHasType hfns hc
  | .block _ _ _ _ _ _ _ _ _ _ _ _ hb _ =>
    StatementsNamesWF.of_statementsHasType hfns hb
  | .ite_det _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ht he _ =>
    ⟨StatementsNamesWF.of_statementsHasType hfns ht,
      StatementsNamesWF.of_statementsHasType hfns he⟩
  | .ite_nondet _ _ _ _ _ _ _ _ _ _ _ _ _ _ ht he _ =>
    ⟨StatementsNamesWF.of_statementsHasType hfns ht,
      StatementsNamesWF.of_statementsHasType hfns he⟩
  | .loop _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hb _ =>
    StatementsNamesWF.of_statementsHasType hfns hb
  | .exit .. => trivial
  | .typeDecl _ _ _ _ _ _ _ _ hprog _ _ _ => hprog

/-- A statement list typed by the typechecker spec with written type variables in scope has
    valid names for any function scope made of functions of `C`. -/
theorem StatementsNamesWF.of_statementsHasType {P : Program}
    {C C' : LContext CoreLParams} {Γ Γ' : TContext Unit} {Δ Δ' : WrittenEnv}
    {L : List String} {ss : List Statement} {fns : String → Prop}
    (hfns : ∀ n, fns n → n ∈ C.functions)
    (h : StatementsHasType P C Γ Δ L ss C' Γ' Δ') : StatementsNamesWF P fns ss :=
  match h with
  | .nil .. => trivial
  | .cons _ _ _ _ _ _ _ _ _ _ _ _ hs ht =>
    ⟨StatementNamesWF.of_statementHasType hfns hs,
      StatementsNamesWF.of_statementsHasType (fun n hn => hs.functions_eq ▸ hfns n hn) ht⟩

end

/-! ### Names in functions, procedures and declarations -/

/-- A function typed by the typechecker spec has valid names for any function scope made of
    functions of `C`. -/
theorem FuncNamesWF.of_funcHasTypeExact {C : LContext CoreLParams}
    {Γ : TContext Unit} {f : Function} {fns : String → Prop}
    (hfns : ∀ n, fns n → n ∈ C.functions) (h : FuncHasTypeExact C Γ f) : FuncNamesWF fns f :=
  fun x hx hf => h.formalsNotFunctions x hx (hfns _ hf)

/-- A function has valid names when a renaming of its type parameters does. -/
private theorem FuncNamesWF.of_alphaVariant {C : LContext CoreLParams} {Γ : TContext Unit}
    {fns : String → Prop} {func f' : Function}
    (hv : FuncAlphaVariant C Γ func f') (h : FuncNamesWF fns f') : FuncNamesWF fns func := by
  intro x hx
  rw [← hv.inputs_keys] at hx
  exact h x hx

/-- Statements have valid names when they do with their type annotations rewritten. -/
private theorem StatementsNamesWF.of_mapStmtsTys {P : Program} {fns : String → Prop}
    (f : LMonoTy → LMonoTy) (ss : List Statement) :
    StatementsNamesWF P fns (mapStmtsTys f ss) → StatementsNamesWF P fns ss := by
  induction ss using Block.mapExpr.induct (motive1 := fun s =>
      StatementNamesWF P fns (mapStmtTys f s) → StatementNamesWF P fns s) with
  | case1 c =>
    rename_i h
    rw [mapStmtTys_cmd] at h
    cases c with
    | cmd cc => cases cc <;> simp_all [mapCmdTys, mapCmdWith, StatementNamesWF, CmdNamesWF]
    | call => trivial
  | _ =>
    simp_all [mapStmtTys_block, mapStmtTys_ite, mapStmtTys_loop, mapStmtTys_exit,
      mapStmtTys_typeDecl, mapStmtsTys_nil, mapStmtsTys_cons, StatementNamesWF,
      StatementsNamesWF]

/-- A procedure has valid names when a renaming of its type parameters does. -/
private theorem ProcNamesWF.of_alphaVariant {P : Program} {fns : String → Prop}
    {C : LContext CoreLParams} {Γ : TContext Unit} {proc proc' : Procedure}
    (hv : ProcAlphaVariant C Γ proc proc') (h : ProcNamesWF P fns proc') :
    ProcNamesWF P fns proc := by
  obtain ⟨ren, -, rfl⟩ := hv
  obtain ⟨-, hin, hout⟩ := Procedure.renameTypeArgs_names proc ren
  obtain ⟨hkeys, hbody⟩ := h
  have hformals : ∀ x ∈ proc.header.inputs.keys ++ proc.header.outputs.keys,
      VarNotFunc fns x := by
    rw [← hin, ← hout]
    exact hkeys
  refine ⟨hformals, ?_⟩
  cases hb : proc.body with
  | cfg _ | abstract => trivial
  | structured ss =>
    simp only [Procedure.renameTypeArgs, Procedure.mapTys, hb] at hbody
    exact StatementsNamesWF.of_mapStmtsTys _ ss hbody

/-- A procedure typed by the typechecker spec has valid names for any function scope made of
    functions of `C`. -/
theorem ProcNamesWF.of_procHasTypeExact {P : Program}
    {C : LContext CoreLParams} {Γ : TContext Unit} {proc : Procedure} {fns : String → Prop}
    (hfns : ∀ n, fns n → n ∈ C.functions) (h : ProcHasTypeExact P C Γ proc) :
    ProcNamesWF P fns proc := by
  refine ⟨?_, ?_⟩
  · exact fun x hx hf => h.formalsNotFunctions x hx (hfns _ hf)
  · have hbody := h.bodyTyped
    cases hshape : proc.body with
    | cfg _ | abstract => trivial
    | structured _ =>
      rw [hshape] at hbody
      match hbody with
      | .structured _ _ _ _ _ hss =>
        exact StatementsNamesWF.of_statementsHasType
          (C := { C with rigidTypeVars := C.rigidTypeVars ++ proc.header.typeArgs }) hfns hss

/-- A declaration typed by the typechecker spec has valid names for any function scope made of
    functions of `C`. -/
theorem DeclNamesWF.of_declHasType {P : Program} {C C' : LContext CoreLParams}
    {Γ Γ' : TContext Unit} {d : Decl} {fns : String → Prop}
    (hfns : ∀ n, fns n → n ∈ C.functions)
    (h : DeclHasType P C Γ d C' Γ') : DeclNamesWF P fns d :=
  match h with
  | .type_con .. => trivial
  | .type_syn .. => trivial
  | .type_data .. => trivial
  | .ax .. => trivial
  | .lemma .. => trivial
  | .distinct .. => trivial
  | .proc _ _ _ _ ⟨_, hv, hp⟩ =>
    ProcNamesWF.of_alphaVariant hv (ProcNamesWF.of_procHasTypeExact hfns hp)
  | .func _ _ _ _ _ _ _ _ hv hf _ =>
    FuncNamesWF.of_alphaVariant hv (FuncNamesWF.of_funcHasTypeExact hfns hf)
  | .recFuncBlock _ _ _ _ _ _ _ _ _ _ _ _ hvars hstubs hfull hextS _ hfs _ => by
    intro f hf
    obtain ⟨f', hf', hv⟩ := List.Rel₂.exists_of_mem_left hvars hf
    refine FuncNamesWF.of_alphaVariant hv (FuncNamesWF.of_funcHasTypeExact ?_ (hfs f' hf'))
    intro n hn
    rcases hn with hold | hnew
    · exact hextS.mem_old (hfns n hold)
    · obtain ⟨id, hid, rfl⟩ := List.mem_map.mp hnew
      simp only [Decl.funcNames] at hid
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hid
      obtain ⟨g', hg', hgv⟩ := List.Rel₂.exists_of_mem_left hvars hg
      subst hstubs
      have hstub := List.mem_map_of_mem hg' (f := fun f : Function =>
        ({ name := f.name, typeArgs := f.typeArgs, inputs := f.inputs,
           output := f.output } : LFunc CoreLParams))
      have hmem := hextS.mem_new hstub
      rw [hgv.name_eq] at hmem
      exact hmem

/-- A declaration list typed by the typechecker spec has valid names for any function scope made
    of functions of `C`. -/
theorem DeclsNamesWF.of_declsHasType {P : Program} {C C' : LContext CoreLParams}
    {Γ Γ' : TContext Unit} {ds : List Decl} {fns : String → Prop}
    (hfns : ∀ n, fns n → n ∈ C.functions)
    (h : DeclsHasType P C Γ ds C' Γ') : DeclsNamesWF P fns ds := by
  induction h generalizing fns with
  | nil => trivial
  | cons =>
    rename_i hd _ ih
    exact ⟨DeclNamesWF.of_declHasType hfns hd, ih (DeclHasType.extendScope_subset hfns hd)⟩

/-- A program typed by the typechecker spec has valid names. -/
theorem ProgramNamesWF.of_programHasType {C : LContext CoreLParams} {Γ : TContext Unit}
    {P : Program} (h : ProgramHasType C Γ P) : ProgramNamesWF C P := by
  obtain ⟨hnodup, hidents, C', Γ', hds⟩ := h
  exact ⟨hnodup, hidents, DeclsNamesWF.of_declsHasType (fun _ hn => hn) hds⟩

/-! ### Names under smaller function scopes and programs -/

/-- Function names stay valid under a smaller function scope. -/
theorem FuncNamesWF.mono {fns fns' : String → Prop} (hsub : ∀ n, fns n → fns' n)
    {f : Function} (h : FuncNamesWF fns' f) : FuncNamesWF fns f :=
  fun x hx hn => h x hx (hsub _ hn)

mutual

/-- Statement names stay valid under a smaller function scope and a program declaring only
    names the original declares. -/
private theorem StatementNamesWF.mono {P P' : Program} {fns fns' : String → Prop}
    (hP : ∀ n ∈ P'.getNames, n ∈ P.getNames) (hsub : ∀ n, fns n → fns' n) :
    (s : Statement) → StatementNamesWF P fns' s → StatementNamesWF P' fns s
  | .cmd (.cmd c), h => by
    cases c with
    | init _ _ _ _ => exact fun hn => h (hsub _ hn)
    | set _ _ _ => exact h
    | assert _ _ _ => exact h
    | assume _ _ _ => exact h
    | cover _ _ _ => exact h
  | .cmd (.call _ _ _ _), h => h
  | .block _ b _, h => StatementsNamesWF.mono hP hsub b h
  | .ite _ t e _, h => ⟨StatementsNamesWF.mono hP hsub t h.1, StatementsNamesWF.mono hP hsub e h.2⟩
  | .loop _ _ _ b _, h => StatementsNamesWF.mono hP hsub b h
  | .exit _ _, h => h
  | .typeDecl _ _, h => fun n hn => h n (hP n hn)

/-- Statement-list names stay valid under a smaller function scope and a program declaring only
    names the original declares. -/
private theorem StatementsNamesWF.mono {P P' : Program} {fns fns' : String → Prop}
    (hP : ∀ n ∈ P'.getNames, n ∈ P.getNames) (hsub : ∀ n, fns n → fns' n) :
    (ss : List Statement) → StatementsNamesWF P fns' ss → StatementsNamesWF P' fns ss
  | [], h => h
  | s :: ss, h => ⟨StatementNamesWF.mono hP hsub s h.1, StatementsNamesWF.mono hP hsub ss h.2⟩

end

/-- Procedure names stay valid under a smaller function scope and a program declaring only names
    the original declares. -/
theorem ProcNamesWF.mono {P P' : Program} {fns fns' : String → Prop}
    (hP : ∀ n ∈ P'.getNames, n ∈ P.getNames) (hsub : ∀ n, fns n → fns' n) {p : Procedure}
    (h : ProcNamesWF P fns' p) : ProcNamesWF P' fns p := by
  obtain ⟨hformals, hbody⟩ := h
  refine ⟨fun x hx hn => hformals x hx (hsub _ hn), ?_⟩
  cases hb : p.body with
  | structured ss =>
    rw [hb] at hbody
    exact StatementsNamesWF.mono hP hsub ss hbody
  | cfg _ | abstract => trivial

/-! ### Names under type-annotation maps -/

mutual

/-- Mapping the type annotations of a statement keeps its names valid. -/
theorem StatementNamesWF.mapStmtTys {P : Program} {fns : String → Prop}
    (f : LMonoTy → LMonoTy) :
    (s : Statement) → StatementNamesWF P fns s → StatementNamesWF P fns (mapStmtTys f s)
  | .cmd (.cmd c), h => by
    rw [mapStmtTys_cmd]
    cases c <;> exact h
  | .cmd (.call _ _ _ _), _ => by
    rw [mapStmtTys_cmd]
    trivial
  | .block _ b _, h => by
    rw [mapStmtTys_block]
    exact StatementsNamesWF.mapStmtsTys f b h
  | .ite _ t e _, h => by
    rw [mapStmtTys_ite]
    exact ⟨StatementsNamesWF.mapStmtsTys f t h.1,
      StatementsNamesWF.mapStmtsTys f e h.2⟩
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
theorem StatementsNamesWF.mapStmtsTys {P : Program} {fns : String → Prop}
    (f : LMonoTy → LMonoTy) :
    (ss : List Statement) → StatementsNamesWF P fns ss →
      StatementsNamesWF P fns (mapStmtsTys f ss)
  | [], h => by
    rw [mapStmtsTys_nil]
    exact h
  | s :: ss, h => by
    rw [mapStmtsTys_cons]
    exact ⟨StatementNamesWF.mapStmtTys f s h.1,
      StatementsNamesWF.mapStmtsTys f ss h.2⟩

end

end -- public section

end TypeSpec
end Core
