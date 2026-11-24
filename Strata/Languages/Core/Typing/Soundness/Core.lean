/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Verifier
public import Strata.Languages.Core.FactoryProps
public import Strata.Languages.Core.Typing.Soundness.Program
public import Strata.Languages.Core.Typing.Props.TypingSpecProps
import Strata.Languages.Core.ProgramType
import Strata.Languages.Core.Factory
import all Strata.Languages.Core.FactoryProps
import all Strata.Transform.CoreTypeCheck
import Strata.Languages.Core.Identifiers
import all Init.Util
import Strata.Languages.Core.IdentifiersProps
import Strata.DL.Lambda.LExprT
import Strata.DL.Lambda.LExprTypeEnv
import Strata.DL.Lambda.TypeFactory
import all Strata.Languages.Core.Typing.Soundness.Program

/-! # Hypothesis-free soundness of the top-level entry point

Key theorems:
* `typeCheck_sound`: an accepted program satisfies the typechecker spec.
* `typeCheck_sound_output`: the output is well typed with valid names.
* `typeCheck_callsWellFormed`: the calls of the output are well formed.

The `_extraFunctions` variants allow extra factory functions. -/

public section

namespace Core

open Lambda Imperative
open TypeSpec

/-! ### The factory check -/

/-- A successful single-function check returns the environment it was given and comes from an
    accepted function check. -/
private theorem checkFunction_ok_inv (scope : Thunk (Std.HashSet String))
    (C : Core.Expression.TyContext) (Env Env' : Core.Expression.TyEnv)
    (func : LFunc CoreLParams) (h : Core.Factory.checkFunction scope C Env func = .ok Env') :
    Env' = Env ∧ ∃ renamed f' : Function,
      Function.typeCheckIn scope C Env func.toFunc = .ok (renamed, f') := by
  unfold Core.Factory.checkFunction at h
  obtain ⟨⟨renamed, f'⟩, hcheck, hpure⟩ := (Except.bind_is_ok _ _ _).mp h
  simp only [Except.ok.injEq] at hpure
  exact ⟨hpure.symm, renamed, f', hcheck⟩

/-- A successful check of a factory function returns the environment it was given, and the
    function has no reserved type parameter and comes from an accepted function check. -/
private theorem checkFactoryFunction_ok_inv (scope : Thunk (Std.HashSet String))
    (C : Core.Expression.TyContext) (Env Env' : Core.Expression.TyEnv) (func : LFunc CoreLParams)
    (h : Core.Factory.checkFactoryFunction scope C Env func = .ok Env') :
    Env' = Env ∧ (∀ a ∈ func.typeArgs, isAllowedName a = true)
      ∧ ∃ renamed f' : Function,
        Function.typeCheckIn scope C Env func.toFunc = .ok (renamed, f') := by
  unfold Core.Factory.checkFactoryFunction at h
  obtain ⟨u, hallowed, hcheck⟩ := (Except.bind_is_ok _ _ _).mp h
  obtain ⟨hEq, hfun⟩ := checkFunction_ok_inv scope C Env Env' func hcheck
  exact ⟨hEq, checkTypeArgsAllowed_ok hallowed, hfun⟩

/-- A successful factory check against the name set `scope` returns the environment it was
    given and accepts every function of the factory in that environment against `scope`; no
    function has a reserved type parameter. -/
private theorem factory_typeCheckIn_ok_inv (scope : Thunk (Std.HashSet String))
    (C : Core.Expression.TyContext) (Env Env' : Core.Expression.TyEnv)
    (h : Core.Factory.typeCheckIn scope C Env = .ok Env') :
    Env' = Env ∧ ∀ f ∈ C.functions.toArray, (∀ a ∈ f.typeArgs, isAllowedName a = true)
      ∧ ∃ renamed f' : Function,
        Function.typeCheckIn scope C Env f.toFunc = .ok (renamed, f') := by
  unfold Core.Factory.typeCheckIn at h
  rw [← Array.foldlM_toList] at h
  simp only [← Array.mem_toList_iff]
  generalize C.functions.toArray.toList = l at h ⊢
  induction l with
  | nil => exact ⟨(Except.ok.inj h).symm, fun f hf => absurd hf List.not_mem_nil⟩
  | cons g rest ih =>
    rw [List.foldlM_cons] at h
    obtain ⟨Env₁, hstep, hrest⟩ := (Except.bind_is_ok _ _ _).mp h
    obtain ⟨rfl, hcheck⟩ := checkFactoryFunction_ok_inv scope C Env Env₁ g hstep
    obtain ⟨hEq, hall⟩ := ih hrest
    refine ⟨hEq, fun f hf => ?_⟩
    rcases List.mem_cons.mp hf with rfl | hmem
    · exact hcheck
    · exact hall f hmem

/-- The renaming of the reserved type parameters of a factory function that the function
    checker returns gives the function a well-formed type signature. -/
private theorem lfuncSigWF_typeCheckIn {scope : Thunk (Std.HashSet String)}
    (C : Expression.TyContext) (Env : Expression.TyEnv) (lf : LFunc CoreLParams)
    (renamed f' : Function) (h : Function.typeCheckIn scope C Env lf.toFunc = .ok (renamed, f')) :
    LFuncSigWF { lf with toFunc := renamed } := by
  have hsig := (LFuncWF_stub C Env h).toSig
  exact ⟨hsig.typeArgs_nodup, hsig.typeArgs_no_gen_prefix, hsig.inputs_typevars_in_typeArgs,
    hsig.output_typevars_in_typeArgs⟩

/-- After a successful factory check against any name set, every function of the factory has
    a well-formed type signature. -/
private theorem factory_typeCheckIn_sigWF (scope : Thunk (Std.HashSet String))
    (C : Core.Expression.TyContext) (Env Env' : Core.Expression.TyEnv)
    (h : Core.Factory.typeCheckIn scope C Env = .ok Env') :
    FactorySigWF C.functions := by
  refine ⟨fun lf hlf => ?_⟩
  obtain ⟨hallowed, renamed, f', hcheck⟩ :=
    (factory_typeCheckIn_ok_inv scope C Env Env' h).2 lf hlf
  have hsig := lfuncSigWF_typeCheckIn C Env lf renamed f' hcheck
  rwa [Function.typeCheckIn_renamed hcheck,
    Function.renameReservedTypeArgs_of_allowed _ _ _ _ hallowed] at hsig

/-! ### The builtin known-type table -/

/-- The initial registered-type table carries the function arrow at arity two and the Boolean
    type at arity zero. -/
private theorem initTyContext_arrow_bool :
    initTyContext.knownTypes["arrow"]? = some 2 ∧
    initTyContext.knownTypes["bool"]? = some 0 := by
  have heq : initTyContext.knownTypes = Core.KnownTypes := rfl
  rw [heq, knownTypes_getElem?, knownTypes_getElem?]
  exact ⟨rfl, rfl⟩

/-- Every primitive literal's type is an instance of a type the initial registered-type table
    registers. -/
private theorem allLiteralTysKnown_init :
    ∀ c : Lambda.LConst, c.isPrimitive = true →
      LMonoTy.knownInstance c.ty initTyContext.knownTypes = true := by
  intro c hp
  have heq : initTyContext.knownTypes = Core.KnownTypes := rfl
  rw [heq]
  refine LMonoTy.wellKinded_knownInstance c.ty Core.KnownTypes
    (wellKinded_of_knownArityOkB 1 c.ty ?_)
  cases c <;> first | rfl | exact absurd hp Bool.false_ne_true

/-! ### Invariants of the initial context and environment -/

/-- A Boolean check that holds on every input and output type of every entry of the built-in
    function array holds on every input and output type of every function of the initial context. -/
private theorem initFunctions_sigs_of_all (p : LMonoTy → Bool)
    (hall : (WFFactoryArray.toList.all fun wf =>
      (wf.func.output :: wf.func.inputs.values).all p) = true) :
    ∀ f ∈ initTyContext.functions.toArray, ∀ ty ∈ f.output :: f.inputs.values, p ty = true := by
  intro f hf ty hty
  exact List.all_eq_true.mp
    (Factory_all_of_WFFactoryArray (fun f => (f.output :: f.inputs.values).all p) hall f hf) ty hty

/-- The initial registered-type table registers `arrow` at arity 2, and every input and output
    type of every built-in function is a registered instance of it. -/
private theorem factorySigsKnown_init :
    FactorySigsKnown initTyContext.knownTypes initTyContext.functions := by
  have hall : (WFFactoryArray.toList.all fun wf =>
      (wf.func.output :: wf.func.inputs.values).all (knownArityOkB 10)) = true := by
    simp only [WFFactoryArray, Array.toList_appendList]
    decide +kernel
  refine ⟨initTyContext_arrow_bool.1, ?_⟩
  intro f hf ty hty
  exact LMonoTy.wellKinded_knownInstance ty Core.KnownTypes
    (wellKinded_of_knownArityOkB 10 ty (initFunctions_sigs_of_all _ hall f hf ty hty))

/-- Every datatype of the initial context, with any function table, is registered. -/
private theorem datatypesKnown_init (functions : Lambda.Factory CoreLParams) :
    ({ initTyContext with functions } : Expression.TyContext).DatatypesKnown := by
  intro d hd
  simp [initTyContext, Lambda.LContext.default, Lambda.TypeFactory.allDatatypes] at hd

/-- The initial environment's alias list is empty. -/
private theorem default_aliases : (Lambda.TEnv.default (IDMeta := Unit)).context.aliases = [] := by
  simp [Lambda.TEnv.default, Lambda.TEnv.context]

/-- No alias belongs to the initial environment. -/
private theorem not_mem_default_aliases (al : TypeAlias) :
    al ∉ (Lambda.TEnv.default (IDMeta := Unit)).context.aliases := by
  simp only [default_aliases, List.not_mem_nil, not_false_eq_true]

/-- The initial environment binds no variable. -/
private theorem default_types_find? (x : Expression.Ident) :
    (Lambda.TEnv.default (IDMeta := Unit)).context.types.find? x = none := by
  simp [Lambda.TEnv.default, Lambda.TEnv.context, Strata.Util.HMaps.find?]

/-- The initial environment has no alias, so every alias body in it is an instance of a
    registered type. -/
private theorem aliasBodiesKnown_init {C : Expression.TyContext} :
    AliasBodiesKnown C (Lambda.TEnv.default (IDMeta := Unit)).context := by
  intro al hal
  exact absurd hal (not_mem_default_aliases _)

/-- The initial environment has no alias, so its aliases agree with any registry. -/
private theorem aliasRegistryCoherent_init {C : Expression.TyContext} {i : Identifiers Unit} :
    AliasRegistryCoherent C Lambda.TEnv.default i where
  declared := fun _ hal =>
    absurd hal (not_mem_default_aliases _)
  freshForKnownTypes := fun _ hal =>
    absurd hal (not_mem_default_aliases _)

/-- The initial type scope binds no variable, so all its schemes are monotypes. -/
private theorem monoScope_init :
    Lambda.MonoScope (Lambda.TEnv.default (IDMeta := Unit)).context := by
  intro z tz hz
  exact absurd hz (by simp only [default_types_find?, reduceCtorEq, not_false_eq_true])

/-- The initial type scope binds no variable, so every ambient variable type is registered. -/
private theorem ambientTypesKnown_init (ks : Lambda.KnownTypes) :
    AmbientTypesKnown ks (Lambda.TEnv.default (IDMeta := Unit)) := by
  intro x vs mty hx
  exact absurd hx (by simp only [default_types_find?, reduceCtorEq, not_false_eq_true])

/-- The initial type scope agrees by lookup with its alias resolution. -/
private theorem default_dealias_FindEq :
    TContext.FindEq (T := CoreLParams) (Lambda.TEnv.default (IDMeta := Unit)).context
      (Lambda.TEnv.default (IDMeta := Unit)).context.dealias := by
  refine ⟨fun x => ?_, ?_⟩
  · rw [TContext.dealias_find? (T := CoreLParams)]
    simp [Lambda.TEnv.default, Lambda.TEnv.context, Strata.Util.HMaps.find?]
  · simp [Lambda.TEnv.default, Lambda.TEnv.context, TContext.dealias]

/-! ### Soundness with extra functions -/

/-- Pushing `f` onto the function table of `C` succeeds only by registering `f`. -/
private theorem addFactoryFunction_of_tryPush {C : Expression.TyContext}
    {f : LFunc CoreLParams} {F : Lambda.Factory CoreLParams}
    (h : C.functions.tryPush f = .ok F) : C.addFactoryFunction f = { C with functions := F } := by
  unfold Lambda.Factory.tryPush at h
  unfold LContext.addFactoryFunction
  split at h
  · nomatch h
  · rename_i hfresh
    simp only [hfresh, ↓reduceDIte]
    rw [Except.ok.inj h]

/-- If `S` holds every type name in scope, then once `f` is pushed onto the function table,
    `S` with the type names of the signature of `f` added holds every type name in scope. -/
private theorem scopeTyNames_cover_tryPush {C : Expression.TyContext} {Env : Expression.TyEnv}
    {S : Std.HashSet String} {f : LFunc CoreLParams} {F : Lambda.Factory CoreLParams}
    (hcov : ∀ n ∈ scopeTyNames C Env, n ∈ S) (h : C.functions.tryPush f = .ok F) :
    ∀ n ∈ scopeTyNames { C with functions := F } Env, n ∈ S.insertMany (funcSigTyNames f) := by
  rw [← addFactoryFunction_of_tryPush h]
  exact scopeTyNames_addFactoryFunction_cover hcov

/-- A successful step that checks a function and adds it to the context comes from an accepted
    function check against `S` and a successful push of the renaming it returns onto the
    context's table; the type names of the signature of that renaming are added to `S`. -/
private theorem checkThenAddOne_ok_inv {Env : Expression.TyEnv} {C C' : Expression.TyContext}
    {S S' : Std.HashSet String} {func : LFunc CoreLParams}
    (h : Factory.checkThenAddOne Env (C, S) func = .ok (C', S')) :
    ∃ (renamed f' : Function) (F : Lambda.Factory CoreLParams),
      Function.typeCheckIn (Thunk.pure S) C Env func.toFunc = .ok (renamed, f')
      ∧ C.functions.tryPush { func with toFunc := renamed } = .ok F
      ∧ C' = { C with functions := F }
      ∧ S' = S.insertMany (funcSigTyNames { func with toFunc := renamed }) := by
  unfold Factory.checkThenAddOne at h
  obtain ⟨⟨renamed, f'⟩, hchk, h⟩ := (Except.bind_is_ok _ _ _).mp h
  obtain ⟨F, hpush, h⟩ := (Except.bind_is_ok _ _ _).mp h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
  exact ⟨renamed, f', F, Except.mapError_ok_h' hchk, hpush, rfl, rfl⟩

/-- The context property `I` survives adding the renaming of each function the checker accepts
    in `Env`. -/
private abbrev CheckThenAddPreserves (I : Expression.TyContext → Prop)
    (Env : Expression.TyEnv) : Prop :=
  ∀ (C : Expression.TyContext) (scope : Thunk (Std.HashSet String))
    (func : LFunc CoreLParams) (F : Lambda.Factory CoreLParams) (renamed f' : Function), I C →
    Function.typeCheckIn scope C Env func.toFunc = .ok (renamed, f') →
    C.functions.tryPush { func with toFunc := renamed } = .ok F →
    I { C with functions := F }

/-- A successful fold that checks and adds a list of functions, from a starting set holding every
    type name in scope, keeps that coverage and any context property `I` surviving each accepted
    addition: both hold at the end and at the context and set reached before each function,
    which is accepted there against that set. -/
private theorem foldlM_checkThenAddOne_ok_inv (I : Expression.TyContext → Prop)
    (Env : Expression.TyEnv) (hstep : CheckThenAddPreserves I Env) :
    ∀ (l : List (LFunc CoreLParams)) (C C' : Expression.TyContext) (S S' : Std.HashSet String),
      I C → (∀ n ∈ scopeTyNames C Env, n ∈ S) →
      l.foldlM (Factory.checkThenAddOne Env) (C, S) = .ok (C', S') →
      I C' ∧ (∀ n ∈ scopeTyNames C' Env, n ∈ S') ∧ ∀ (i : Nat) (hi : i < l.length),
        ∃ (Ci : Expression.TyContext) (Si : Std.HashSet String),
          (l.take i).foldlM (Factory.checkThenAddOne Env) (C, S) = .ok (Ci, Si) ∧ I Ci
          ∧ (∀ n ∈ scopeTyNames Ci Env, n ∈ Si)
          ∧ ∃ renamed f' : Function,
            Function.typeCheckIn (Thunk.pure Si) Ci Env l[i].toFunc = .ok (renamed, f') := by
  intro l
  induction l with
  | nil =>
    intro C C' S S' hI hcov h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj h)
    exact ⟨hI, hcov, fun i hi => absurd hi (Nat.not_lt_zero _)⟩
  | cons g rest ih =>
    intro C C' S S' hI hcov h
    rw [List.foldlM_cons] at h
    obtain ⟨⟨C1, S1⟩, hone, hrest⟩ := (Except.bind_is_ok _ _ _).mp h
    obtain ⟨renamed, f', F, htc, hpush, rfl, rfl⟩ := checkThenAddOne_ok_inv hone
    have hI1 := hstep C _ g F renamed f' hI htc hpush
    obtain ⟨hI', hcov', hall⟩ := ih _ C' _ S' hI1 (scopeTyNames_cover_tryPush hcov hpush) hrest
    refine ⟨hI', hcov', fun i hi => ?_⟩
    cases i with
    | zero => exact ⟨C, S, rfl, hI, hcov, renamed, f', htc⟩
    | succ j =>
      have hj : j < rest.length := Nat.lt_of_succ_lt_succ hi
      obtain ⟨Ci, Si, hCi, hICi, hcovi, hacc⟩ := hall j hj
      refine ⟨Ci, Si, ?_, hICi, hcovi, hacc⟩
      rw [List.take_succ_cons, List.foldlM_cons, hone]
      exact hCi

/-- Checking and adding an array of functions from a set covering the type names in scope keeps
    that coverage and any property `I` each accepted addition preserves, at the end and before
    each function, which is accepted there. -/
private theorem checkThenAddIn_ok_inv (I : Expression.TyContext → Prop) (Env : Expression.TyEnv)
    (hstep : CheckThenAddPreserves I Env)
    (fns : Array (LFunc CoreLParams)) (C C' : Expression.TyContext) (S S' : Std.HashSet String)
    (hI : I C) (hcov : ∀ n ∈ scopeTyNames C Env, n ∈ S)
    (h : Factory.checkThenAddIn S C Env fns = .ok (C', S')) :
    I C' ∧ (∀ n ∈ scopeTyNames C' Env, n ∈ S') ∧ ∀ (i : Nat) (hi : i < fns.size),
      ∃ (Ci : Expression.TyContext) (Si : Std.HashSet String),
        Factory.checkThenAddIn S C Env (fns.take i) = .ok (Ci, Si) ∧ I Ci
        ∧ (∀ n ∈ scopeTyNames Ci Env, n ∈ Si)
        ∧ ∃ renamed f' : Function,
          Function.typeCheckIn (Thunk.pure Si) Ci Env fns[i].toFunc = .ok (renamed, f') := by
  unfold Factory.checkThenAddIn at h ⊢
  rw [← Array.foldlM_toList] at h
  obtain ⟨hI', hcov', hall⟩ :=
    foldlM_checkThenAddOne_ok_inv I Env hstep fns.toList C C' S S' hI hcov h
  refine ⟨hI', hcov', fun i hi => ?_⟩
  have hi' : i < fns.toList.length := by simpa using hi
  obtain ⟨Ci, Si, hCi, hICi, hcovi, renamed, f', htc⟩ := hall i hi'
  have htc' : Function.typeCheckIn (Thunk.pure Si) Ci Env fns[i].toFunc
      = .ok (renamed, f') := by
    simpa using htc
  refine ⟨Ci, Si, ?_, hICi, hcovi, renamed, f', htc'⟩
  rw [← Array.foldlM_toList, Array.take_eq_extract, Array.toList_extract,
    List.extract_eq_take_drop, List.drop_zero, Nat.sub_zero, hCi]

/-- Checking and adding functions to a context returns the context that `checkThenAddIn`
    reaches from the set of the type names in scope. -/
private theorem checkThenAdd_of_checkThenAddIn {C C' : Expression.TyContext}
    {Env : Expression.TyEnv} {fns : Array (LFunc CoreLParams)} {S' : Std.HashSet String}
    (h : Factory.checkThenAddIn (scopeTyNameThunk C Env).get C Env fns = .ok (C', S')) :
    Factory.checkThenAdd C Env fns = .ok C' := by
  unfold Factory.checkThenAdd
  rw [h]
  rfl

/-- A factory the factory check accepts against any name set at the initial context and
    environment satisfies `FactorySigsKnown` for the initial registered-type table. -/
private theorem factory_typeCheckIn_sigsKnown (scope : Thunk (Std.HashSet String))
    (f : Lambda.Factory CoreLParams) (Env' : Expression.TyEnv)
    (h : Factory.typeCheckIn scope { initTyContext with functions := f } Lambda.TEnv.default
      = .ok Env') :
    FactorySigsKnown initTyContext.knownTypes f := by
  refine ⟨initTyContext_arrow_bool.1, ?_⟩
  intro lf hlf ty hty
  obtain ⟨hallowed, renamed, lf', htc⟩ := (factory_typeCheckIn_ok_inv _ _ _ _ h).2 lf hlf
  have hknown := Function.typeCheckIn_declaredSigKnown_of_aliases_nil _ _ _ _ htc rfl
  rw [Function.typeCheckIn_renamed htc,
    Function.renameReservedTypeArgs_of_allowed _ _ _ _ hallowed] at hknown
  exact hknown ty hty

/-- If the factory check accepts a factory at the initial context and environment against a
    name set holding every type name in scope there, every function of the factory satisfies
    the typechecker spec for functions there. -/
private theorem factory_typeCheckIn_funcHasType (scope : Thunk (Std.HashSet String))
    (f : Lambda.Factory CoreLParams) (Env' : Expression.TyEnv)
    (h : Factory.typeCheckIn scope { initTyContext with functions := f } Lambda.TEnv.default
      = .ok Env')
    (hcov : ∀ n ∈ scopeTyNames { initTyContext with functions := f } Lambda.TEnv.default,
      n ∈ scope.get) :
    ∀ lf ∈ f.toArray, FuncHasType { initTyContext with functions := f }
      (Lambda.TEnv.default (IDMeta := Unit)).context lf.toFunc := by
  intro lf hlf
  obtain ⟨-, renamed, lf', htc⟩ := (factory_typeCheckIn_ok_inv _ _ _ _ h).2 lf hlf
  exact Function.typeCheckIn_funcHasType _ _ Lambda.TEnv.default lf.toFunc renamed lf' htc
    hcov (Lambda.LExpr.TEnvWF_default (T := CoreLParams))
    (factory_typeCheckIn_sigWF _ _ _ _ h)
    (Lambda.LExpr.checkContextTypesClosed_default (T := CoreLParams)) monoScope_init

/-- The supplied function table, or the built-in one for `none`, has well-formed and registered
    signatures when a supplied table passes the factory check. -/
private theorem baseFactory_sigs (factory : Option (Lambda.Factory CoreLParams))
    (hsupplied : ∀ f, factory = some f →
      Factory.typeCheck { initTyContext with functions := f } Lambda.TEnv.default
        = .ok Lambda.TEnv.default) :
    FactorySigWF (factory.getD Core.Factory)
      ∧ FactorySigsKnown initTyContext.knownTypes (factory.getD Core.Factory) := by
  cases factory with
  | none =>
    exact ⟨(Lambda.WFLFactory.toFactory_wf Core.WFFactory).toSig, factorySigsKnown_init⟩
  | some f =>
    have hf := hsupplied f rfl
    exact ⟨factory_typeCheckIn_sigWF _ _ _ _ hf, factory_typeCheckIn_sigsKnown _ f _ hf⟩

/-- Check-then-add from the initial context and the set of the type names in scope there keeps
    a well-formed, registered function table and returns a set holding every type name in scope
    at the end; each extra function satisfies the typechecker spec at the context reached before
    it. -/
private theorem checkThenAddIn_init_sound (base : Lambda.Factory CoreLParams)
    (h_fac : FactorySigWF base)
    (h_known : FactorySigsKnown initTyContext.knownTypes base)
    (fns : Array (LFunc CoreLParams)) (C : Expression.TyContext) (S : Std.HashSet String)
    (h : Factory.checkThenAddIn
      (scopeTyNameThunk { initTyContext with functions := base } Lambda.TEnv.default).get
      { initTyContext with functions := base } Lambda.TEnv.default fns = .ok (C, S)) :
    (∃ functions : Lambda.Factory CoreLParams, C = { initTyContext with functions }
      ∧ FactorySigWF functions ∧ FactorySigsKnown initTyContext.knownTypes functions)
    ∧ (∀ n ∈ scopeTyNames C Lambda.TEnv.default, n ∈ S)
    ∧ ∀ (i : Nat) (hi : i < fns.size), ∃ Ci : Expression.TyContext,
      Factory.checkThenAdd { initTyContext with functions := base } Lambda.TEnv.default
        (fns.take i) = .ok Ci
      ∧ FuncHasType Ci (Lambda.TEnv.default (IDMeta := Unit)).context fns[i].toFunc := by
  have hstep : CheckThenAddPreserves (fun C => ∃ functions : Lambda.Factory CoreLParams,
      C = { initTyContext with functions }
        ∧ FactorySigWF functions ∧ FactorySigsKnown initTyContext.knownTypes functions)
      Lambda.TEnv.default := by
    intro C scope func F' renamed f' ⟨F, hC, hWF, hKn⟩ htc hpush
    subst hC
    refine ⟨F', rfl, ⟨fun lf hlf => ?_⟩, hKn.1, fun lf hlf => ?_⟩
    · rcases Lambda.Factory.mem_tryPush hpush lf hlf with hold | rfl
      · exact hWF.lfuncs_wf lf hold
      · exact lfuncSigWF_typeCheckIn _ _ func renamed f' htc
    · rcases Lambda.Factory.mem_tryPush hpush lf hlf with hold | rfl
      · exact hKn.2 lf hold
      · have hknown := Function.typeCheckIn_declaredSigKnown_of_aliases_nil _ _ _ _ htc rfl
        exact hknown
  obtain ⟨hI, hcov, hall⟩ := checkThenAddIn_ok_inv _ Lambda.TEnv.default hstep fns _ C _ S
    ⟨base, rfl, h_fac, h_known⟩ (scopeTyNameThunk_cover _ _) h
  refine ⟨hI, hcov, fun i hi => ?_⟩
  obtain ⟨Ci, Si, hCi, ⟨F, hF, hWF, -⟩, hcovi, renamed, f', htc⟩ := hall i hi
  subst hF
  exact ⟨_, checkThenAdd_of_checkThenAddIn hCi,
    Function.typeCheckIn_funcHasType _ _ Lambda.TEnv.default _ renamed f' htc hcovi
    (Lambda.LExpr.TEnvWF_default (T := CoreLParams)) hWF
    (Lambda.LExpr.checkContextTypesClosed_default (T := CoreLParams)) monoScope_init⟩

/-- A successful `Core.typeCheck` checks and adds the extra functions after the factory's
    (built-in for `none`), from the set of the type names in scope there, and runs
    `Program.typeCheckIn` with the context and set this reaches; a supplied factory passes its
    check. -/
private theorem typeCheck_extraFunctions_reduces
    (options : VerifyOptions) (program program' : Program)
    (factory : Option (Lambda.Factory CoreLParams)) (moreFns : Lambda.Factory CoreLParams)
    (h : Core.typeCheck options program factory moreFns = .ok program') :
    ∃ (C : Expression.TyContext) (S : Std.HashSet String),
      Factory.checkThenAddIn
          (scopeTyNameThunk { initTyContext with functions := factory.getD Core.Factory }
            Lambda.TEnv.default).get
          { initTyContext with functions := factory.getD Core.Factory }
          Lambda.TEnv.default moreFns.toArray = .ok (C, S)
      ∧ (∃ Env' : Expression.TyEnv,
          Program.typeCheckIn S C Lambda.TEnv.default program = .ok (program', Env'))
      ∧ ∀ f, factory = some f →
          Factory.typeCheck { initTyContext with functions := f } Lambda.TEnv.default
            = .ok Lambda.TEnv.default := by
  unfold Core.typeCheck at h
  simp only [bind, Except.bind] at h
  split at h
  · exact absurd h (by simp)
  · rename_i T heqF
    have hcheck : T = Lambda.TEnv.default ∧ ∀ f, factory = some f →
        Factory.typeCheck { initTyContext with functions := f } Lambda.TEnv.default
          = .ok Lambda.TEnv.default := by
      cases factory with
      | none =>
        exact ⟨(Except.ok.inj heqF).symm, fun f hf => absurd hf (by simp)⟩
      | some f =>
        have heqF' : Factory.typeCheck { initTyContext with functions := f } Lambda.TEnv.default
            = Except.ok T := heqF
        obtain rfl := (factory_typeCheckIn_ok_inv _ _ _ _ heqF').1
        exact ⟨rfl, fun g hg => Option.some.inj hg ▸ heqF'⟩
    obtain ⟨rfl, hsupplied⟩ := hcheck
    elim_err h with r hC
    obtain ⟨C, S⟩ := r
    elim_err h with r hprog
    obtain ⟨p, Env'⟩ := r
    have hout : program' = p := by
      split at h <;> simp only [dbgTrace] at h <;> exact (Except.ok.inj h).symm
    subst hout
    exact ⟨C, S, hC, ⟨Env', hprog⟩, hsupplied⟩

/-- If `Core.typeCheck` accepts `program`, checking each extra function and adding it to the
    initial context in turn reaches a context with a well-formed, registered function table. At
    that context `program` is accepted against a set holding every type name in scope there, and
    typed by the typechecker spec; every extra and supplied-factory function satisfies the
    typechecker spec. -/
private theorem typeCheck_extraFunctions_inv
    (options : VerifyOptions) (program program' : Program)
    (factory : Option (Lambda.Factory CoreLParams)) (moreFns : Lambda.Factory CoreLParams)
    (h : Core.typeCheck options program factory moreFns = .ok program') :
    ∃ (functions : Lambda.Factory CoreLParams) (S : Std.HashSet String)
      (Env' : Expression.TyEnv),
      Factory.checkThenAdd { initTyContext with functions := factory.getD Core.Factory }
          Lambda.TEnv.default moreFns.toArray = .ok { initTyContext with functions }
      ∧ FactorySigWF functions ∧ FactorySigsKnown initTyContext.knownTypes functions
      ∧ Program.typeCheckIn S { initTyContext with functions } Lambda.TEnv.default program
          = .ok (program', Env')
      ∧ (∀ n ∈ scopeTyNames { initTyContext with functions } Lambda.TEnv.default, n ∈ S)
      ∧ ProgramHasType { initTyContext with functions }
          (Lambda.TEnv.default (IDMeta := Unit)).context program
      ∧ (∀ (i : Nat) (hi : i < moreFns.toArray.size), ∃ Ci : Expression.TyContext,
          Factory.checkThenAdd { initTyContext with functions := factory.getD Core.Factory }
              Lambda.TEnv.default (moreFns.toArray.take i) = .ok Ci
          ∧ FuncHasType Ci (Lambda.TEnv.default (IDMeta := Unit)).context
              moreFns.toArray[i].toFunc)
      ∧ ∀ f, factory = some f → ∀ lf ∈ f.toArray,
          FuncHasType { initTyContext with functions := f }
            (Lambda.TEnv.default (IDMeta := Unit)).context lf.toFunc := by
  obtain ⟨C, S, hC, ⟨Env', hprog⟩, hsupplied⟩ :=
    typeCheck_extraFunctions_reduces options program program' factory moreFns h
  obtain ⟨hbaseWF, hbaseKnown⟩ := baseFactory_sigs factory hsupplied
  obtain ⟨⟨functions, hCeq, h_fac, h_known⟩, hcov, hextras⟩ :=
    checkThenAddIn_init_sound _ hbaseWF hbaseKnown _ C S hC
  subst hCeq
  refine ⟨functions, S, Env', checkThenAdd_of_checkThenAddIn hC, h_fac, h_known, hprog, hcov,
    ?_, hextras,
    fun f hf => factory_typeCheckIn_funcHasType _ f _ (hsupplied f hf)
      (scopeTyNameThunk_cover _ _)⟩
  exact Program.typeCheckIn_sound S _ Lambda.TEnv.default Env' program program' hprog hcov
    (Lambda.LExpr.TEnvWF_default (T := CoreLParams)) h_fac
    (Lambda.LExpr.checkContextTypesClosed_default (T := CoreLParams))
    aliasRegistryCoherent_init aliasBodiesKnown_init monoScope_init

/-- Input soundness with extra functions: if `Core.typeCheck` accepts `program`, it satisfies
    the typechecker spec at the context reached by checking and adding the extra functions in
    turn, as does each extra function at the context reached before it and every function of a
    supplied factory. -/
theorem typeCheck_sound_extraFunctions
    (options : VerifyOptions) (program program' : Program)
    (factory : Option (Lambda.Factory CoreLParams)) (moreFns : Lambda.Factory CoreLParams)
    (h : Core.typeCheck options program factory moreFns = .ok program') :
    ∃ C : Expression.TyContext,
      Factory.checkThenAdd { initTyContext with functions := factory.getD Core.Factory }
          Lambda.TEnv.default moreFns.toArray = .ok C
      ∧ ProgramHasType C (Lambda.TEnv.default (IDMeta := Unit)).context program
      ∧ (∀ (i : Nat) (hi : i < moreFns.toArray.size), ∃ Ci : Expression.TyContext,
          Factory.checkThenAdd { initTyContext with functions := factory.getD Core.Factory }
              Lambda.TEnv.default (moreFns.toArray.take i) = .ok Ci
          ∧ FuncHasType Ci (Lambda.TEnv.default (IDMeta := Unit)).context
              moreFns.toArray[i].toFunc)
      ∧ ∀ f, factory = some f → ∀ lf ∈ f.toArray,
          FuncHasType { initTyContext with functions := f }
            (Lambda.TEnv.default (IDMeta := Unit)).context lf.toFunc := by
  obtain ⟨_, _, _, hC, -, -, -, -, hinput, hextras, hsupplied⟩ :=
    typeCheck_extraFunctions_inv options program program' factory moreFns h
  exact ⟨_, hC, hinput, hextras, hsupplied⟩

/-- Output soundness with extra functions: if `Core.typeCheck` turns `program` into `program'`,
    then at the context reached by checking and adding the extra functions in turn, `program'` is
    well typed over the empty variable scopes and its names are valid. -/
theorem typeCheck_sound_output_extraFunctions
    (options : VerifyOptions) (program program' : Program)
    (factory : Option (Lambda.Factory CoreLParams)) (moreFns : Lambda.Factory CoreLParams)
    (h : Core.typeCheck options program factory moreFns = .ok program') :
    ∃ C : Expression.TyContext,
      Factory.checkThenAdd { initTyContext with functions := factory.getD Core.Factory }
          Lambda.TEnv.default moreFns.toArray = .ok C
      ∧ ProgramHasType C (Lambda.TEnv.default (IDMeta := Unit)).context program
      ∧ (ProgramWellTyped C (Lambda.TEnv.default (IDMeta := Unit)).context.types program' ∧
          ProgramNamesWF C program')
      ∧ ∀ (i : Nat) (hi : i < moreFns.toArray.size), ∃ Ci : Expression.TyContext,
          Factory.checkThenAdd { initTyContext with functions := factory.getD Core.Factory }
              Lambda.TEnv.default (moreFns.toArray.take i) = .ok Ci
          ∧ FuncHasType Ci (Lambda.TEnv.default (IDMeta := Unit)).context
              moreFns.toArray[i].toFunc := by
  obtain ⟨functions, S, Env', hC, h_fac, h_known, hprog, hcov, hinput, hextras, -⟩ :=
    typeCheck_extraFunctions_inv options program program' factory moreFns h
  refine ⟨_, hC, hinput, ?_, hextras⟩
  obtain ⟨⟨hkinds, C', hdecls⟩, hnames⟩ :=
    Program.typeCheckIn_sound_output S _ Lambda.TEnv.default Env' program program' hprog hcov
      (Lambda.LExpr.TEnvWF_default (T := CoreLParams)) h_fac
      (Lambda.LExpr.checkContextTypesClosed_default (T := CoreLParams))
      aliasRegistryCoherent_init aliasBodiesKnown_init monoScope_init h_known
      (datatypesKnown_init functions)
      initTyContext_arrow_bool.2 allLiteralTysKnown_init (ambientTypesKnown_init _)
  have hfixed : FactorySigsFixed (Lambda.TEnv.default (IDMeta := Unit)).context.aliases
      ({ initTyContext with functions } : Expression.TyContext).functions :=
    h_known.sigsFixed fun _ hal =>
      absurd hal (not_mem_default_aliases _)
  rw [LContext.resolveTable_eq_self hfixed] at hdecls hnames
  exact ⟨⟨hkinds, C', hdecls.of_find? default_dealias_FindEq.1⟩, hnames⟩

/-! ### Hypothesis-free top-level soundness (default factory) -/

/-- With no extra functions, the check-then-add fold returns the context it starts from. -/
private theorem checkThenAdd_default (C : Expression.TyContext) (Env : Expression.TyEnv) :
    Factory.checkThenAdd C Env (Lambda.Factory.default : Lambda.Factory CoreLParams).toArray
      = .ok C := by
  rw [show (Lambda.Factory.default : Lambda.Factory CoreLParams).toArray = #[] from rfl]
  rfl

/-- Input soundness: a program `Core.typeCheck` accepts satisfies the typechecker spec
    (`ProgramHasType`) at the initial context and environment. -/
theorem typeCheck_sound
    (options : VerifyOptions) (program program' : Program)
    (h : Core.typeCheck options program = .ok program') :
    ProgramHasType initTyContext (Lambda.TEnv.default (IDMeta := Unit)).context program := by
  obtain ⟨C, hC, hprog, -⟩ :=
    typeCheck_sound_extraFunctions options program program' none Lambda.Factory.default h
  obtain rfl : C = initTyContext := Except.ok.inj (hC.symm.trans (checkThenAdd_default _ _))
  exact hprog

/-- Output soundness: the output of a successful `Core.typeCheck` is well typed
    (`ProgramWellTyped`) over the empty variable scopes and its names are valid
    (`ProgramNamesWF`). -/
theorem typeCheck_sound_output
    (options : VerifyOptions) (program program' : Program)
    (h : Core.typeCheck options program = .ok program') :
    ProgramWellTyped initTyContext (Lambda.TEnv.default (IDMeta := Unit)).context.types program' ∧
    ProgramNamesWF initTyContext program' := by
  obtain ⟨C, hC, -, hprog, -⟩ :=
    typeCheck_sound_output_extraFunctions options program program' none
      Lambda.Factory.default h
  obtain rfl : C = initTyContext := Except.ok.inj (hC.symm.trans (checkThenAdd_default _ _))
  exact hprog

/-- Every call in a program that `Core.typeCheck` returns is well formed
    (`Program.callsWellFormed`): it names a declared procedure, matches its signature, and has
    distinct result variables. -/
theorem typeCheck_callsWellFormed
    (options : VerifyOptions) (program program' : Program)
    (factory : Option (Lambda.Factory CoreLParams)) (moreFns : Lambda.Factory CoreLParams)
    (h : Core.typeCheck options program factory moreFns = .ok program') :
    program'.callsWellFormed := by
  obtain ⟨_, -, -, ⟨hA, -⟩, -⟩ :=
    typeCheck_sound_output_extraFunctions options program program' factory moreFns h
  obtain ⟨_, _, -, ⟨_, hprog⟩, -⟩ :=
    typeCheck_extraFunctions_reduces options program program' factory moreFns h
  exact hA.callsWellFormed
    (Program.typeCheckIn_cfgCallsWellFormed hprog)

end Core

end -- public section
