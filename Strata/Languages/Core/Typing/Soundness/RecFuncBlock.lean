/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.RecFuncBlockType
public import Strata.Languages.Core.Typing.Soundness.Function
public import Strata.Languages.Core.Typing.Soundness.RecFuncBlockInversion
public import Strata.Util.ExceptProps
import Strata.Util.Tactics
import all Strata.DL.Lambda.FactoryProps
import all Strata.DL.Lambda.LExprTypeEnv
import Strata.Languages.Core.Typing.Props.FunctionTypeProps
import Strata.Languages.Core.Typing.Props.WrittenTyVarScopeProps
import all Strata.Languages.Core.FunctionType
import all Strata.Languages.Core.RecFuncBlockType
import all Strata.DL.Util.FuncAttr

/-! # Recursive function block checker facts
A successful block check accepts every member with the function checker in the context with
every stub: `RecFuncBlock.typeCheckIn_members`, with the per-block facts alongside it. -/

public section

namespace Core

open Lambda Imperative

/-- An accepted member signature check: the member's name is new to `C`, it is not inline and is
    marked recursive, its written signature names are valid with the functions of `C` and the
    members of `funcs` in scope, and the checked signature is the member's
    `Function.renameAndResolve`. -/
private theorem RecFuncBlock.checkSignature_ok_inv
    {C : Expression.TyContext} {Env : Expression.TyEnv} {funcs : List Function}
    {func : Function} {sig : CheckedSignature}
    (h : RecFuncBlock.checkSignature C Env funcs func = .ok sig) :
    func.name.name ∉ C.functions
      ∧ func.attr.any (· == .inline) = false
      ∧ func.isRecursive = true
      ∧ Function.checkHeaderNames (fun n => n ∈ C.functions ∨ n ∈ funcs.map (·.name.name))
          func = .ok ()
      ∧ Function.renameAndResolve C Env func = .ok sig := by
  unfold RecFuncBlock.checkSignature at h
  simp only [bind, Except.bind] at h
  elim_err h with hfresh
  elim_err h with hinline
  elim_err h with hrec
  elim_err h with u hnames
  obtain ⟨⟩ := u
  exact ⟨Function.checkNameFresh_ok hfresh, by simpa using hinline, by simpa using hrec,
    hnames, h⟩

/-- Resolving a function signature reads only the registered types of the context. -/
private theorem Function.resolveSignature_knownTypes {C C' : Expression.TyContext}
    (hkt : C'.knownTypes = C.knownTypes) (Env : Expression.TyEnv) (func : Function) :
    Function.resolveSignature C' Env func = Function.resolveSignature C Env func := by
  unfold Function.resolveSignature resolveKnownTys isInstanceOfKnownType
  rw [hkt]

/-- A checked definition has the name and type parameters of the checked function, and the
    resolved signature it was checked at. -/
private theorem Function.checkDefinition_signature
    {scope : Thunk (Std.HashSet String)} {C : Expression.TyContext} {Env E : Expression.TyEnv}
    {func func' : Function} {outR : LMonoTy} {insR : LMonoTys} {tyNames : Unit → List String}
    (h : Function.checkDefinition scope C Env func outR insR tyNames = .ok (func', E)) :
    func'.name = func.name ∧ func'.typeArgs = func.typeArgs
      ∧ func'.inputs = func.inputs.keys.zip insR ∧ func'.output = outR := by
  unfold Function.checkDefinition at h
  simp only [bind, Except.bind] at h
  elim_err h
  elim_err h
  cases hscope :
      func.exprs.findSome? (WrittenTyVarScope.unboundAnnotVar? false func.typeArgs []) with
  | some _ => simp [Core.unboundAnnotMsg?_eq, hscope] at h
  | none =>
  simp only [Core.unboundAnnotMsg?_eq, hscope, Option.map_none] at h
  elim_err h
  elim_err h
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, -⟩ := h
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The stub of a checked signature is the signature of the definition checked from it. -/
private theorem RecFuncBlock.checkDefinition_stub
    {scope : Thunk (Std.HashSet String)} {C : Expression.TyContext} {Env E : Expression.TyEnv}
    {sig : CheckedSignature} {func' : Function} {tyNames : Unit → List String}
    (h : Function.checkDefinition scope C Env sig.func sig.output sig.inputs tyNames =
      .ok (func', E)) :
    sig.stub = LFunc.mk func'.name func'.typeArgs (inputs := func'.inputs)
      (output := func'.output) := by
  obtain ⟨hname, hta, hins, hout⟩ := Function.checkDefinition_signature h
  rw [hname, hta, hins, hout]
  rfl

/-- A block member whose signature check and whose definition check against `scope` succeed is
    accepted by `Function.typeCheckIn` against `scope` in any context `Cstub` that has the rigid
    type variables and registered types of `C` and whose functions are those of `C` or members
    of the block. It returns the renaming of the signature check and the checked definition. -/
private theorem RecFuncBlock.member_typeCheckIn {scope : Thunk (Std.HashSet String)}
    {C Cstub : Expression.TyContext} {Env E : Expression.TyEnv} {funcs : List Function}
    {func func' : Function} {sig : CheckedSignature}
    (hsig : RecFuncBlock.checkSignature C Env funcs func = .ok sig)
    (hdef : Function.checkDefinition scope Cstub Env sig.func sig.output sig.inputs
      sig.tyNames = .ok (func', E))
    (hfuncs : ∀ n ∈ Cstub.functions, n ∈ C.functions ∨ n ∈ funcs.map (·.name.name))
    (hrigid : Cstub.rigidTypeVars = C.rigidTypeVars) (hkt : Cstub.knownTypes = C.knownTypes) :
    Function.typeCheckIn scope Cstub Env func = .ok (sig.func, func') := by
  obtain ⟨-, -, -, hnames, hsigC⟩ := RecFuncBlock.checkSignature_ok_inv hsig
  have hsig' : Function.renameAndResolve Cstub Env func = .ok sig := by
    rw [← hsigC]
    unfold Function.renameAndResolve
    simp only [Function.renameReservedTypeArgs_congr func _ hrigid rfl,
      Function.resolveSignature_knownTypes hkt]
  unfold Function.typeCheckIn
  rw [Function.checkHeaderNames_mono hfuncs hnames]
  simp only [bind, Except.bind, hsig', hdef]

/-- Adding signature stubs to a context keeps its rigid type variables. -/
theorem RecFuncBlock.stubContext_rigidTypeVars (C : Expression.TyContext)
    (stubs : List (LFunc CoreLParams)) :
    (RecFuncBlock.stubContext C stubs).rigidTypeVars = C.rigidTypeVars := by
  unfold RecFuncBlock.stubContext
  induction stubs generalizing C with
  | nil => rfl
  | cons stub rest ih =>
    rw [List.foldl_cons, ih]
    unfold LContext.addFactoryFunction
    split <;> rfl

/-- A function name of a context extended with stubs names a function of the context or one of
    the stubs. -/
private theorem RecFuncBlock.mem_stubContext_functions (C : Expression.TyContext)
    (stubs : List (LFunc CoreLParams)) (n : String)
    (h : n ∈ (RecFuncBlock.stubContext C stubs).functions) :
    n ∈ C.functions ∨ n ∈ stubs.map (·.name.name) := by
  unfold RecFuncBlock.stubContext at h
  induction stubs generalizing C with
  | nil => exact Or.inl h
  | cons stub rest ih =>
    rw [List.foldl_cons] at h
    rcases ih _ h with hC | hrest
    · unfold LContext.addFactoryFunction at hC
      split at hC
      · exact Or.inl hC
      · rename_i hnew
        rcases (Lambda.Factory.push_mem_iff _ _ hnew n).mp hC with hstub | hold
        · exact Or.inr (List.mem_cons.mpr (Or.inl hstub))
        · exact Or.inl hold
    · exact Or.inr (List.mem_cons_of_mem _ hrest)

/-- For checked signatures of the members of a block whose definition checks against `scope`
    and the context with every stub all succeed, `Function.typeCheckIn` against `scope` accepts
    each member, in order, in that context, with the corresponding checked function, and each
    stub is the signature of the corresponding checked function. -/
private theorem RecFuncBlock.members_of_sigs {scope : Thunk (Std.HashSet String)}
    {C : Expression.TyContext} {Env : Expression.TyEnv} {funcs funcs' : List Function}
    {sigs : List CheckedSignature}
    (hsigRel : List.Rel₂ (fun f sig => RecFuncBlock.checkSignature C Env funcs f = .ok sig)
      funcs sigs)
    (hdefRel : List.Rel₂ (fun sig f' => ∃ E,
      Function.checkDefinition scope (RecFuncBlock.stubContext C (sigs.map (·.stub))) Env
        sig.func sig.output sig.inputs sig.tyNames = .ok (f', E))
      sigs funcs') :
    sigs.map (·.stub) = funcs'.map (fun f' => LFunc.mk f'.name f'.typeArgs
        (inputs := f'.inputs) (output := f'.output))
      ∧ List.Rel₂ (fun f f' => ∃ renamed, Function.typeCheckIn scope
          (RecFuncBlock.stubContext C (sigs.map (·.stub))) Env f = .ok (renamed, f'))
          funcs funcs' := by
  have hstubNames : (sigs.map (·.stub)).map (·.name.name) = funcs.map (·.name.name) := by
    rw [List.map_map]
    refine (hsigRel.map_eq ?_).symm
    intro f sig hsig
    obtain ⟨-, -, -, -, hsigC⟩ := RecFuncBlock.checkSignature_ok_inv hsig
    obtain ⟨hren, -⟩ := Function.renameAndResolve_ok_inv hsigC
    simp only [Function.comp_apply, CheckedSignature.stub, LFuncDefined.toLFunc,
      hren, (Function.renameReservedTypeArgs_fields C Env f _).1]
  have hfuncs : ∀ n ∈ (RecFuncBlock.stubContext C (sigs.map (·.stub))).functions,
      n ∈ C.functions ∨ n ∈ funcs.map (·.name.name) := by
    intro n hn
    rw [← hstubNames]
    exact RecFuncBlock.mem_stubContext_functions C _ n hn
  have hkt : (RecFuncBlock.stubContext C (sigs.map (·.stub))).knownTypes = C.knownTypes := by
    unfold RecFuncBlock.stubContext
    exact foldl_addFactoryFunction_knownTypes C _ id
  refine ⟨hdefRel.map_eq fun _ _ ⟨_, hdef⟩ => RecFuncBlock.checkDefinition_stub hdef, ?_⟩
  refine (hsigRel.comp hdefRel).imp ?_
  intro f f' ⟨sig, hsig, E, hdef⟩
  exact ⟨sig.func, RecFuncBlock.member_typeCheckIn hsig hdef hfuncs
    (RecFuncBlock.stubContext_rigidTypeVars C _) hkt⟩

/-- The signature stubs of a list of checked functions: each function with its body, contracts
    and attributes dropped. -/
def RecFuncBlock.signatureStubs (funcs' : List Function) : List (LFunc CoreLParams) :=
  funcs'.map fun f' => LFunc.mk f'.name f'.typeArgs (inputs := f'.inputs) (output := f'.output)

/-- A stub is among the signature stubs of a list exactly when it is the signature of one of its
    functions. -/
theorem RecFuncBlock.mem_signatureStubs (funcs' : List Function) (stub : LFunc CoreLParams) :
    stub ∈ RecFuncBlock.signatureStubs funcs' ↔ ∃ f' ∈ funcs',
      LFunc.mk f'.name f'.typeArgs (inputs := f'.inputs) (output := f'.output) = stub := by
  unfold RecFuncBlock.signatureStubs
  exact List.mem_map

/-- A set holding every type name in scope in `C`, extended with the signature type names of
    the stubs that `C` extended with `stubs` registers, holds every type name in scope in that
    extended context. -/
private theorem RecFuncBlock.stubScope_cover {S : Std.HashSet String} {C : Expression.TyContext}
    {Env : Expression.TyEnv} (stubs : List (Lambda.LFunc CoreLParams))
    (hcov : ∀ n ∈ scopeTyNames C Env, n ∈ S) :
    ∀ n ∈ scopeTyNames (RecFuncBlock.stubContext C stubs) Env, n ∈ S.insertMany
      (Factory.tyNamesFrom C.functions.toArray.size
        (RecFuncBlock.stubContext C stubs).functions) := by
  unfold RecFuncBlock.stubContext
  refine Std.HashSet.mem_insertMany_of_cover hcov ?_
  intro n hn
  rw [scopeTyNames_foldl_addFactoryFunction_eq C Env stubs (fun stub => stub)] at hn
  exact List.mem_append.mp hn

/-- A successful block check against a set `S` holding every type name in scope returns the
    incoming environment, the incoming context extended with the checked functions, and a set
    `S'` holding every type name in scope both in the incoming context extended with the stubs
    and in the returned context. `Function.typeCheckIn` against `S'` accepts each member, in
    order, in the context with the signature stubs of the checked functions, with the
    corresponding checked function. -/
theorem RecFuncBlock.typeCheckIn_members (S S' : Std.HashSet String)
    (C C' : Expression.TyContext) (Env Env' : Expression.TyEnv)
    (funcs funcs' : List Function)
    (h : RecFuncBlock.typeCheckIn S C Env funcs = .ok (funcs', C', Env', S'))
    (hcov : ∀ n ∈ scopeTyNames C Env, n ∈ S) :
    Env' = Env
      ∧ C' = RecFuncBlock.fullContext C funcs'
      ∧ (∀ n ∈ scopeTyNames (RecFuncBlock.stubContext C (RecFuncBlock.signatureStubs funcs'))
          Env, n ∈ S')
      ∧ (∀ n ∈ scopeTyNames C' Env, n ∈ S')
      ∧ List.Rel₂ (fun f f' => ∃ renamed, Function.typeCheckIn (Thunk.pure S')
          (RecFuncBlock.stubContext C (RecFuncBlock.signatureStubs funcs')) Env f
            = .ok (renamed, f'))
          funcs funcs' := by
  obtain ⟨sigs, hsigRel, hS', hdefRel, hC', hEnv⟩ :=
    RecFuncBlock.typeCheckIn_decompose S S' C C' Env Env' funcs funcs' h
  obtain ⟨hstubs, hrel⟩ := RecFuncBlock.members_of_sigs hsigRel hdefRel
  have hstubCov :
      ∀ n ∈ scopeTyNames (RecFuncBlock.stubContext C (sigs.map (·.stub))) Env, n ∈ S' := by
    rw [hS']
    exact RecFuncBlock.stubScope_cover _ hcov
  have hfull : scopeTyNames (RecFuncBlock.fullContext C funcs') Env =
      scopeTyNames (RecFuncBlock.stubContext C (sigs.map (·.stub))) Env := by
    unfold RecFuncBlock.fullContext RecFuncBlock.stubContext
    rw [hstubs, List.foldl_map]
    exact scopeTyNames_foldl_addFactoryFunction_congr C Env funcs' (fun f' => f'.toLFunc)
      (fun f' => LFunc.mk f'.name f'.typeArgs (inputs := f'.inputs) (output := f'.output))
      fun _ _ => ⟨rfl, rfl, rfl⟩
  have hstubsEq : sigs.map (·.stub) = RecFuncBlock.signatureStubs funcs' := hstubs
  rw [hstubsEq] at hstubCov hfull hrel
  refine ⟨hEnv, hC', hstubCov, ?_, hrel⟩
  rw [hC', hfull]
  exact hstubCov

/-- Every member of a successfully checked block passes its signature check. -/
private theorem RecFuncBlock.typeCheckIn_member_sig {S S' : Std.HashSet String}
    {C C' : Expression.TyContext} {Env Env' : Expression.TyEnv}
    {funcs funcs' : List Function}
    (h : RecFuncBlock.typeCheckIn S C Env funcs = .ok (funcs', C', Env', S')) :
    ∀ f ∈ funcs, ∃ sig, RecFuncBlock.checkSignature C Env funcs f = .ok sig := by
  intro f hf
  obtain ⟨sigs, hsigRel, -⟩ :=
    RecFuncBlock.typeCheckIn_decompose S S' C C' Env Env' funcs funcs' h
  obtain ⟨sig, -, hsig⟩ := hsigRel.exists_of_mem_left hf
  exact ⟨sig, hsig⟩

/-- The block checker succeeds only on a block with at least one member. -/
theorem RecFuncBlock.typeCheckIn_nonempty
    (S S' : Std.HashSet String) (C C' : Expression.TyContext) (Env Env' : Expression.TyEnv)
    (funcs funcs' : List Function)
    (h : RecFuncBlock.typeCheckIn S C Env funcs = .ok (funcs', C', Env', S')) :
    funcs ≠ [] := by
  intro hnil
  subst hnil
  simp [RecFuncBlock.typeCheckIn, bind, Except.bind] at h

/-- The block checker succeeds only on a block whose members are all marked recursive. -/
theorem RecFuncBlock.typeCheckIn_recursive
    (S S' : Std.HashSet String) (C C' : Expression.TyContext) (Env Env' : Expression.TyEnv)
    (funcs funcs' : List Function)
    (h : RecFuncBlock.typeCheckIn S C Env funcs = .ok (funcs', C', Env', S')) :
    ∀ f ∈ funcs, f.isRecursive = true := by
  intro f hf
  obtain ⟨sig, hsig⟩ := RecFuncBlock.typeCheckIn_member_sig h f hf
  exact (RecFuncBlock.checkSignature_ok_inv hsig).2.2.1

/-- The block checker succeeds only on a block with no member marked inline. -/
theorem RecFuncBlock.typeCheckIn_noInline
    (S S' : Std.HashSet String) (C C' : Expression.TyContext) (Env Env' : Expression.TyEnv)
    (funcs funcs' : List Function)
    (h : RecFuncBlock.typeCheckIn S C Env funcs = .ok (funcs', C', Env', S')) :
    ∀ f ∈ funcs, ∀ a ∈ f.attr, a ≠ Strata.DL.Util.FuncAttr.inline := by
  intro f hf a ha hEq
  subst hEq
  obtain ⟨sig, hsig⟩ := RecFuncBlock.typeCheckIn_member_sig h f hf
  have hfalse := (RecFuncBlock.checkSignature_ok_inv hsig).2.1
  obtain ⟨idx, hidx, hget⟩ := Array.mem_iff_getElem.mp ha
  have hnone := (Array.any_eq_false.mp hfalse) idx hidx
  rw [hget] at hnone
  have hinlinerefl :
      (Strata.DL.Util.FuncAttr.inline == Strata.DL.Util.FuncAttr.inline) = true := by
    unfold Strata.DL.Util.instBEqFuncAttr
    rfl
  exact hnone hinlinerefl

/-- A successful block check returns functions with its members' names, in order. -/
theorem RecFuncBlock.typeCheckIn_names_eq
    (S S' : Std.HashSet String) (C C' : Expression.TyContext) (Env Env' : Expression.TyEnv)
    (funcs funcs' : List Function)
    (h : RecFuncBlock.typeCheckIn S C Env funcs = .ok (funcs', C', Env', S')) :
    funcs'.map (·.name) = funcs.map (·.name) := by
  obtain ⟨sigs, hsigRel, -, hdefRel, -⟩ :=
    RecFuncBlock.typeCheckIn_decompose S S' C C' Env Env' funcs funcs' h
  refine ((RecFuncBlock.members_of_sigs hsigRel hdefRel).2.map_eq ?_).symm
  intro f f' ⟨renamed, hin⟩
  exact (Function.typeCheckIn_copies_untouched_fields _ _ _ f renamed f' hin).1.symm

/-- The stubs of a successfully checked block have its members' names, in order. -/
theorem RecFuncBlock.typeCheckIn_stubs_names
    (S S' : Std.HashSet String) (C C' : Expression.TyContext) (Env Env' : Expression.TyEnv)
    (funcs funcs' : List Function)
    (h : RecFuncBlock.typeCheckIn S C Env funcs = .ok (funcs', C', Env', S')) :
    (RecFuncBlock.signatureStubs funcs').map (·.name) = funcs.map (·.name) := by
  unfold RecFuncBlock.signatureStubs
  rw [List.map_map]
  exact RecFuncBlock.typeCheckIn_names_eq S S' C C' Env Env' funcs funcs' h

/-- A block check succeeds only when no member is named like a function of the incoming
    context. -/
theorem RecFuncBlock.typeCheckIn_names_fresh
    (S S' : Std.HashSet String) (C C' : Expression.TyContext) (Env Env' : Expression.TyEnv)
    (funcs funcs' : List Function)
    (h : RecFuncBlock.typeCheckIn S C Env funcs = .ok (funcs', C', Env', S')) :
    ∀ f ∈ funcs, f.name.name ∉ C.functions := by
  intro f hf
  obtain ⟨sig, hsig⟩ := RecFuncBlock.typeCheckIn_member_sig h f hf
  exact (RecFuncBlock.checkSignature_ok_inv hsig).1

end Core

end -- public section
