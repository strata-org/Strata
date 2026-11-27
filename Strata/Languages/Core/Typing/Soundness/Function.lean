/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.TypeSkolem
public import Strata.Languages.Core.Typing.Props.TypeSkolemProps
public import Strata.Languages.Core.Typing.Props.SourceExprResolveProps
public import Strata.Languages.Core.Typing.Props.SkolemScopeProps
public import Strata.Languages.Core.Typing.Props.SkolemizerProps
public import Strata.Languages.Core.FunctionType
public import Strata.Languages.Core.WrittenTyVarScope
public import Strata.Languages.Core.Typing.Props.FunctionTypeProps
public import Strata.Languages.Core.Typing.Spec.FunctionTypeSpec
public import Strata.Languages.Core.Typing.Spec.NamesWF
public import Strata.DL.Lambda.LExprTypeSpec
public import Strata.DL.Lambda.LExprTypeSpecProps
public import Strata.DL.Lambda.LExprT
public import Strata.DL.Lambda.FactoryWF
public import Strata.DL.Lambda.LExprTypeEnv
public import Strata.DL.Lambda.Denote.LExprResolveAnnotated
public import Strata.Util.ExceptProps
public import Strata.Util.ListUtilsProps
import Strata.Util.Tactics
import Strata.Languages.Core.Typing.Soundness.WrittenTyVarScope
public import Strata.Languages.Core.Typing.Soundness.TypingAssumptions
public import Strata.Languages.Core.Typing.Soundness.Command
import Strata.Languages.Core.Typing.Spec.TypeSpecShared
import all Strata.Languages.Core.Typing.Props.SkolemScopeProps
import all Strata.Languages.Core.FunctionType
import all Strata.Languages.Core.Identifiers
import Strata.Languages.Core.IdentifiersProps
import all Strata.Languages.Core.Typing.Spec.FunctionTypeSpec
import Strata.DL.Lambda.LExprWF
import Strata.DL.Lambda.FactoryProps
import Strata.DL.Lambda.LTyProps
import Strata.DL.Lambda.LExprProps
import Strata.DL.Lambda.LExprEvalFuelProps
import Strata.DL.Lambda.LExprTProps
import Strata.DL.Lambda.LExprWFProps
import Strata.DL.Lambda.LExprAnnotRel
import Strata.DL.Lambda.NamePrefixesProps
import all Strata.Languages.Core.Typing.Spec.NamesWF

/-! # Soundness of the function checker

The checker first renames reserved type parameters (`Function.renameReservedTypeArgs`), then
checks the renamed signature and definition. Most lemmas are about such a check.

Key theorems:
* `Function.typeCheck_sound`: an accepted function satisfies the typechecker spec.
* `Function.typeCheck_sound_output`: the elaborated function is well typed with valid names.
* `Function.typeCheckIn_funcHasType`, `Function.typeCheckIn_sound`,
  `Function.typeCheckIn_sound_output`: the same for the checker run against a given set of type
  names that covers those in scope (`Function.typeCheck_in` relates the two checkers).
* `Function.typeCheckIn_alphaVariant`, `Function.typeCheck_alphaVariant`: the renaming is a
  `FuncAlphaVariant`.
* `Function.typeCheck_sound_renamed`: the renamed function satisfies `FuncHasTypeExact`. -/

public section

namespace Core

open Lambda Imperative
open TypeSpec
open Strata.Util (HMap HMaps)

variable {sc : Thunk (Std.HashSet String)} {tn : Unit → List String}

/-! ## Inverting a successful function check -/

/-- If `checkTypeArgsNodup` succeeds, the type parameters are distinct. -/
theorem checkTypeArgsNodup_ok {pfx : String} {ta : List String}
    (h : checkTypeArgsNodup pfx ta = .ok ()) : ta.Nodup := by
  unfold checkTypeArgsNodup at h
  split at h
  · exact nomatch h
  · rename_i hnd
    simpa using hnd

/-- If `checkTypeArgsAllowed` succeeds, every type parameter is an allowed name. -/
theorem checkTypeArgsAllowed_ok {pfx : String} {ta : List String}
    (h : checkTypeArgsAllowed pfx ta = .ok ()) : ∀ a ∈ ta, isAllowedName a = true := by
  unfold checkTypeArgsAllowed at h
  split at h
  · exact nomatch h
  · rename_i hfind
    intro a ha
    have hneg := List.find?_eq_none.mp hfind a ha
    simpa using hneg

/-- An accepted signature-name check has distinct type parameters covering `sigVars`. -/
theorem checkSignatureNames_ok {kind name : String} {typeArgs sigVars : List String}
    (h : checkSignatureNames kind name typeArgs sigVars = .ok ()) :
    typeArgs.Nodup ∧ ∀ v ∈ sigVars, v ∈ typeArgs := by
  unfold checkSignatureNames at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  elim_err h with _ hta
  refine ⟨checkTypeArgsNodup_ok hta, ?_⟩
  intro v hv
  cases hcv : typeArgs.contains v with
  | true => simpa using hcv
  | false =>
    have hmem : v ∈ (List.filter (fun w => !typeArgs.contains w) sigVars).eraseDups :=
      List.mem_eraseDups.mpr (List.mem_filter.mpr ⟨hv, by simp only [hcv, Bool.not_false]⟩)
    simp_all

/-- The signature-name check accepts distinct type parameters that cover `sigVars`. -/
private theorem checkSignatureNames_eq_ok {kind name : String} {typeArgs sigVars : List String}
    (hnd : typeArgs.Nodup) (hsig : ∀ v ∈ sigVars, v ∈ typeArgs) :
    checkSignatureNames kind name typeArgs sigVars = .ok () := by
  have hcovered : ∀ v ∈ sigVars, ¬ (!typeArgs.contains v) = true := by
    intro v hv
    simp only [List.contains_iff_mem.mpr (hsig v hv), Bool.not_true, Bool.false_eq_true,
      not_false_eq_true]
  have hfilter : sigVars.filter (fun v => !typeArgs.contains v) = [] :=
    List.filter_eq_nil_iff.mpr hcovered
  unfold checkSignatureNames checkTypeArgsNodup
  simp only [decide_eq_true hnd, Bool.not_true, Bool.false_eq_true, ite_false, hfilter,
    List.eraseDups_nil, List.isEmpty_nil, bind, Except.bind, pure, Except.pure]

/-- What a successful signature resolution and definition check establish: their guards held,
    and `func'` and `EnvCore` are built from the resolved types `outR`, `insR` and the checked
    `positions`. -/
private structure Function.CoreRun (sc : Thunk (Std.HashSet String))
    (tn : Unit → List String) (C : Expression.TyContext)
    (Env EnvCore : Expression.TyEnv) (func func' : Function) (outR : LMonoTy) (insR : LMonoTys)
    (positions : Function.CheckedPositions) : Prop where
  /-- The formals are distinct. -/
  inputsNodup : func.inputs.keys.Nodup
  /-- The type parameters are distinct. -/
  typeArgsNodup : func.typeArgs.Nodup
  /-- Every type variable of the declared signature is a declared type parameter. -/
  sigDeclared : ∀ v ∈ LMonoTy.freeVars (LMonoTy.mkArrow' func.output func.inputs.values),
    v ∈ func.typeArgs
  /-- A constructor declares no body. -/
  constrNoBody : func.isConstr = true → func.body = none
  /-- Only a recursive function declares a measure. -/
  measureOnlyRecursive : func.isRecursive = false → func.measure = none
  /-- Resolving the output's aliases gives `outR` and keeps the environment unchanged. -/
  outResolved : LMonoTy.resolveAliases func.output Env = .ok (outR, Env)
  /-- The resolved output is an instance of a registered type. -/
  outKnown : isInstanceOfKnownType outR C = true
  /-- Each resolved input is the alias resolution of its declared type. -/
  insResolveEach : List.Rel₂ (fun ty ty' => LMonoTy.resolveAliases ty Env = .ok (ty', Env))
      func.inputs.values insR
  /-- Each resolved input is registered. -/
  insKnown : List.Rel₂ (fun _ ty' => isInstanceOfKnownType ty' C = true) func.inputs.values insR
  /-- Checking the four expression positions, with self-calls read as some `self` says,
      returned `positions`. -/
  positionsOk : ∃ self, Function.checkPositions self
    (addSkolemTypes C (Function.rigidNames sc C func tn)) Env
    func outR insR (Function.rigidNames sc C func tn) = .ok positions
  /-- The returned environment is the positions' final state. -/
  envCore : EnvCore = positions.env
  /-- Every type parameter occurs in the resolved signature. -/
  typeArgsInSig : ∀ a ∈ func.typeArgs, a ∈ (LMonoTy.mkArrow' outR insR).freeVars
  /-- The stored function: the resolved signature, and each checked expression under the
      returned substitution with rigid constants mapped back to the type parameters. -/
  stored : func' =
    { func with
      inputs := func.inputs.keys.zip insR
      output := outR
      body := positions.body.map
        (finishDeskolemized (Function.rigidNames sc C func tn) EnvCore.stateSubstInfo.subst)
      measure := positions.measure.map
        (finishDeskolemized (Function.rigidNames sc C func tn) EnvCore.stateSubstInfo.subst)
      preconditions := positions.preconditions.map (fun (md, eT) =>
        { expr :=
            finishDeskolemized (Function.rigidNames sc C func tn) EnvCore.stateSubstInfo.subst eT
          md := md })
      axioms := positions.axioms.map
        (finishDeskolemized (Function.rigidNames sc C func tn) EnvCore.stateSubstInfo.subst) }
  /-- Every type variable annotating a stored expression is a type parameter. -/
  annotsScoped : ∀ e ∈ func'.exprs, ∀ v ∈ annotTyVars e, v ∈ func'.typeArgs
  /-- The scope check found no annotation type variable outside the type parameters. -/
  writtenScoped : ∀ e ∈ func.exprs,
    WrittenTyVarScope.unboundAnnotVar? false func.typeArgs [] e = none

/-- Each resolved input of a successful run is alias-equivalent to its declared type and
    registered. -/
private theorem Function.CoreRun.insResolved
    {C : Expression.TyContext} {Env EnvCore : Expression.TyEnv} {func func' : Function}
    {outR : LMonoTy} {insR : LMonoTys} {positions : Function.CheckedPositions}
    (run : Function.CoreRun sc tn C Env EnvCore func func' outR insR positions) :
    List.Rel₂ (fun ty ty' => AliasEquiv Env.context.aliases ty ty'
      ∧ isInstanceOfKnownType ty' C = true) func.inputs.values insR := by
  have hequiv : List.Rel₂ (fun ty ty' => AliasEquiv Env.context.aliases ty ty')
      func.inputs.values insR :=
    run.insResolveEach.imp fun ty ty' hr =>
      (LMonoTy.resolveAliases_sourceTyResolves (T := CoreLParams) ty Env ty' Env hr).aliasEquiv
  exact hequiv.and run.insKnown

/-- A successful proposition check: the annotation type variables are in `rigid`, the skolemized
    proposition resolves at `bool` to `et`, the result is `et` under the final substitution,
    deskolemized, and the returned flag says whether every annotation of the result satisfies
    `ok`. -/
theorem Function.checkBoolProp_ok_inv
    {C : Expression.TyContext} {Env EnvR : Expression.TyEnv} {rigid : List TyIdentifier}
    {σ : RigidNames} {src : Std.Format} {ok : LMonoTy → Bool} {e e' : Expression.Expr}
    {stored : Bool}
    (h : Function.checkBoolProp C Env rigid σ src ok e = .ok (e', stored, EnvR)) :
    ∃ et,
      WrittenTyVarScope.unboundAnnotVar? false rigid [] e = none ∧
      resolveWithType C Env (skolemizeBody none σ e) LMonoTy.bool = .ok (et, EnvR) ∧
      e' = finishDeskolemized σ EnvR.stateSubstInfo.subst et ∧
      stored = (exprAnnotTys e').all ok := by
  unfold Function.checkBoolProp at h
  cases hsc : WrittenTyVarScope.unboundAnnotVar? false rigid [] e with
  | some _ =>
    simp [unboundAnnotMsg?_eq, hsc, throw, throwThe,
      MonadExceptOf.throw, bind, Except.bind] at h
  | none =>
  simp only [unboundAnnotMsg?_eq, List.findSome?_cons, List.findSome?_nil,
    hsc, Option.map_none, bind, Except.bind] at h
  elim_err h with v hres
  obtain ⟨et, EnvR'⟩ := v
  have hrw := Except.mapError_ok_h' (SourceExpr.orFreeVarError_eq_ok.mp hres)
  rw [skolemizeBody_unless_isEmpty] at hrw
  simp only [finishStored_eq, Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl, rfl⟩ := h
  exact ⟨et, rfl, hrw, rfl, rfl⟩

/-- A definition `Function.checkDefinition` accepts is accepted by `Function.checkDefinitionWith`
    with self-calls read in one of its two ways. -/
theorem Function.checkDefinition_ok_inv {sc : Thunk (Std.HashSet String)}
    {C : Expression.TyContext} {Env : Expression.TyEnv} {func : Function} {outR : LMonoTy}
    {insR : LMonoTys} {tn : Unit → List String} {r : Function × Expression.TyEnv}
    (h : Function.checkDefinition sc C Env func outR insR tn = .ok r) :
    ∃ self, Function.checkDefinitionWith self sc C Env func outR insR tn = .ok r := by
  unfold Function.checkDefinition at h
  split at h
  · rename_i hok
    exact ⟨_, hok.trans h⟩
  · split at h
    · rename_i hok
      exact ⟨_, hok.trans h⟩
    · split at h <;> cases h

/-- What the checker establishes for the function it checks: its signature names pass
    `checkHeaderNames`, its type parameters are allowed names, its signature resolves, and
    `Function.checkDefinition` accepts it at that signature with result `func'` and `EnvCore`,
    with rigid constants avoiding the names of `sc` and `tn ()`. -/
private structure Function.Checked (sc : Thunk (Std.HashSet String))
    (tn : Unit → List String) (C : Expression.TyContext) (Env EnvCore : Expression.TyEnv)
    (func func' : Function) : Prop where
  /-- The signature names pass the header check against the functions in scope. -/
  names : Function.checkHeaderNames func = .ok ()
  /-- Every type parameter is an allowed name. -/
  allowed : ∀ a ∈ func.typeArgs, isAllowedName a = true
  /-- The signature resolves, and the definition check accepts the function at it. -/
  core : ∃ outR insR, Function.resolveSignature C Env func = .ok (outR, insR) ∧
    Function.checkDefinition sc C Env func outR insR tn = .ok (func', EnvCore)

/-- A function the checker checks satisfies `CoreRun` for some resolved signature and checked
    positions. -/
private theorem Function.Checked.run
    {C : Expression.TyContext} {Env EnvCore : Expression.TyEnv} {func func' : Function}
    (hchecked : Function.Checked sc tn C Env EnvCore func func') :
    ∃ outR insR positions,
      Function.CoreRun sc tn C Env EnvCore func func' outR insR positions := by
  obtain ⟨outS, insS, hsigOk, h⟩ := hchecked.core
  obtain ⟨hta, hsig⟩ := checkSignatureNames_ok hchecked.names
  unfold Function.resolveSignature at hsigOk
  simp only [bind, Except.bind] at hsigOk
  elim_err hsigOk with hnd
  elim_err hsigOk with vOut hOutRes
  obtain ⟨outR, EnvA⟩ := vOut
  have hEA : EnvA = Env := LMonoTy.resolveAliases_env_eq func.output Env outR EnvA hOutRes
  subst EnvA
  elim_err hsigOk with houtKnown
  elim_err hsigOk with vIns hInsFold
  obtain ⟨insR, EnvB⟩ := vIns
  obtain ⟨-, -, hIns⟩ :=
    resolveKnownTys_ok_inv C _ func.inputs.values Env EnvB insR hInsFold
  elim_err hsigOk with hphantom
  simp only [Except.ok.injEq, Prod.mk.injEq] at hsigOk
  obtain ⟨rfl, rfl⟩ := hsigOk
  obtain ⟨self, h⟩ := Function.checkDefinition_ok_inv h
  unfold Function.checkDefinitionWith at h
  simp only [bind, Except.bind] at h
  elim_err h with hconstr
  elim_err h with hrec
  cases hscope :
      func.exprs.findSome? (WrittenTyVarScope.unboundAnnotVar? false func.typeArgs []) with
  | some _ => simp [unboundAnnotMsg?_eq, hscope] at h
  | none =>
  simp only [unboundAnnotMsg?_eq, hscope, Option.map_none] at h
  elim_err h with positions hpositions
  elim_err h with hstoredOk
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  obtain ⟨hfunc, hEnvCore⟩ := h
  subst hEnvCore
  have hfinish := funext (finishStored_eq (Function.rigidNames sc C func tn)
    positions.env.stateSubstInfo.subst (tyVarsIn func.typeArgs))
  simp only [hfinish, Option.map_map, List.map_map, Function.comp_def] at hfunc hstoredOk
  have hannots : ∀ e ∈ func'.exprs, ∀ v ∈ annotTyVars e, v ∈ func'.typeArgs := by
    subst hfunc
    intro e he
    apply annotTyVars_mem_of_tyVarsIn
    simp only [Strata.DL.Util.Func.exprs, List.mem_append, List.mem_map, Option.mem_toList,
      Option.map_eq_some_iff] at he
    simp only [Bool.not_eq_eq_eq_not, Bool.not_true, Option.all_map, List.all_map,
      Function.comp_def] at hstoredOk
    grind
  refine ⟨outR, insR, positions,
    { inputsNodup := by simpa using hnd
      typeArgsNodup := hta
      sigDeclared := hsig
      constrNoBody := ?_
      measureOnlyRecursive := ?_
      outResolved := hOutRes
      outKnown := by simpa using houtKnown
      insResolveEach := hIns.imp fun _ _ hr => hr.1
      insKnown := hIns.imp fun _ _ hr => hr.2.2
      positionsOk := ⟨self, hpositions⟩
      envCore := rfl
      typeArgsInSig := by simpa using hphantom
      stored := hfunc.symm
      annotsScoped := hannots
      writtenScoped := List.findSome?_eq_none_iff.mp hscope }⟩
  · intro hc
    rw [hc, Bool.true_and] at hconstr
    simpa using hconstr
  · intro hr
    rw [hr, Bool.not_false, Bool.true_and] at hrec
    simpa using hrec

/-- The checker's renaming of the reserved type parameters of a function does not change
    whether its signature names pass the check. -/
private theorem Function.checkHeaderNames_renameReservedTypeArgs
    {C : Expression.TyContext} {Env : Expression.TyEnv} {func : Function} :
    Function.checkHeaderNames (Function.renameReservedTypeArgs C Env func
        (fun _ => func.annotTys)) = .ok () ↔
      Function.checkHeaderNames func = .ok () := by
  constructor
  · intro h
    obtain ⟨hnd', hsig'⟩ := checkSignatureNames_ok h
    have hnd := Function.typeArgs_nodup_of_renameReservedTypeArgs C Env func _ hnd'
    obtain ⟨ren, hren, heq⟩ := Function.renameReservedTypeArgs_alphaVariant C Env func hnd
    rw [heq] at hsig'
    exact checkSignatureNames_eq_ok hnd (Function.sigDeclared_of_renameTypeArgs hren.1 hsig')
  · intro h
    obtain ⟨hnd, hsig⟩ := checkSignatureNames_ok h
    obtain ⟨ren, hren, heq⟩ := Function.renameReservedTypeArgs_alphaVariant C Env func hnd
    obtain ⟨hnd', hsig'⟩ := Function.renameTypeArgs_sigDeclared hren.1 hnd hsig
    rw [heq]
    exact checkSignatureNames_eq_ok hnd' hsig'

/-- `Function.typeCheckIn` returns the checker's renaming of the reserved type parameters of the
    function, and checks that renaming (`Function.Checked`), with rigid constants avoiding the
    names of `scope` and the type names the function mentions. -/
private theorem Function.typeCheckIn_checked {scope : Thunk (Std.HashSet String)}
    {C : Expression.TyContext} {Env : Expression.TyEnv} {func renamed func' : Function}
    (h : Function.typeCheckIn scope C Env func = .ok (renamed, func')) :
    renamed = Function.renameReservedTypeArgs C Env func (fun _ => func.annotTys) ∧
      ∃ EnvCore, Function.Checked scope (fun _ => func.tyNames func.annotTys) C Env EnvCore
          renamed func' := by
  unfold Function.typeCheckIn at h
  obtain ⟨⟨⟩, hnames, h⟩ := (Except.bind_is_ok _ _ _).mp h
  obtain ⟨sig, hsig, h⟩ := (Except.bind_is_ok _ _ _).mp h
  obtain ⟨⟨funcCore, EnvCore⟩, hdef, hfin⟩ := (Except.bind_is_ok _ _ _).mp h
  simp only [Except.ok.injEq, Prod.mk.injEq] at hfin
  obtain ⟨rfl, rfl⟩ := hfin
  obtain ⟨hren, hres, -, htn⟩ := Function.renameAndResolve_ok_inv hsig
  rw [htn] at hdef
  have hnames' : Function.checkHeaderNames sig.func = .ok () := by
    rw [hren]
    exact Function.checkHeaderNames_renameReservedTypeArgs.mpr hnames
  have hallowed : ∀ a ∈ sig.func.typeArgs, isAllowedName a = true := by
    rw [hren]
    exact Function.renameReservedTypeArgs_typeArgs_allowed C Env func _
  exact ⟨hren, EnvCore, hnames', hallowed, sig.output, sig.inputs, hres, hdef⟩

/-- `Function.typeCheckIn` against the set of the type names in scope accepts every function
    `Function.typeCheck` accepts, returning its renaming of the reserved type parameters and the
    same elaborated form. -/
theorem Function.typeCheck_in {C : Expression.TyContext} {Env Env' : Expression.TyEnv}
    {func func' : Function} (h : Function.typeCheck C Env func = .ok (func', Env')) :
    Function.typeCheckIn (scopeTyNameThunk C Env) C Env func =
      .ok (Function.renameReservedTypeArgs C Env func (fun _ => func.annotTys), func') := by
  unfold Function.typeCheck at h
  obtain ⟨⟨renamed, funcIn⟩, hIn, hfin⟩ := (Except.bind_is_ok _ _ _).mp h
  simp only [Except.ok.injEq, Prod.mk.injEq] at hfin
  obtain ⟨rfl, -⟩ := hfin
  rw [← (Function.typeCheckIn_checked hIn).1]
  exact hIn

/-- `Function.typeCheck` checks the renaming of the reserved type parameters of the function
    (`Function.Checked`), with rigid constants avoiding the type names in scope. -/
private theorem Function.typeCheck_checked {C : Expression.TyContext}
    {Env Env' : Expression.TyEnv} {func func' : Function}
    (h : Function.typeCheck C Env func = .ok (func', Env')) :
    ∃ tn EnvCore,
      Function.Checked (scopeTyNameThunk C Env) tn C Env EnvCore
          (Function.renameReservedTypeArgs C Env func (fun _ => func.annotTys)) func' := by
  obtain ⟨-, EnvCore, hc⟩ := Function.typeCheckIn_checked (Function.typeCheck_in h)
  exact ⟨_, EnvCore, hc⟩

/-- A core run keeps the name, constructor and recursion flags, and attributes of the function. -/
private theorem Function.CoreRun.untouchedFields
    {C : Expression.TyContext} {Env EnvCore : Expression.TyEnv}
    {func func' : Function} {outR : LMonoTy} {insR : LMonoTys}
    {positions : Function.CheckedPositions}
    (run : Function.CoreRun sc tn C Env EnvCore func func' outR insR positions) :
    func'.name = func.name ∧ func'.isConstr = func.isConstr ∧
      func'.isRecursive = func.isRecursive ∧ func'.attr = func.attr := by
  rw [run.stored]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- A core run's resolved signature pairs each formal name with its resolved input type, and
    its resolved output type is alias-equivalent to the declared one. -/
private theorem Function.CoreRun.resolvedSig
    {C : Expression.TyContext} {Env EnvCore : Expression.TyEnv}
    {func func' : Function} {outR : LMonoTy} {insR : LMonoTys}
    {positions : Function.CheckedPositions}
    (run : Function.CoreRun sc tn C Env EnvCore func func' outR insR positions) :
    ListMap.keys (func.inputs.keys.zip insR) = func.inputs.keys
    ∧ ListMap.values (func.inputs.keys.zip insR) = insR
    ∧ AliasEquiv Env.context.aliases func.output outR := by
  obtain ⟨hkeys, hvals⟩ :=
    listMap_keys_zip_values func.inputs insR (List.Rel₂.length_eq run.insResolved)
  exact ⟨hkeys, hvals, LExpr.resolveAliases_aliasEquiv (T := CoreLParams) (Γ := Env.context)
    func.output Env outR Env run.outResolved rfl⟩

/-- In a core run's resolved signature every type variable is a type parameter, the skolemized
    output is ground, and deskolemizing a skolemized signature type gives it back. -/
private theorem Function.CoreRun.signature
    {C : Expression.TyContext} {Env EnvCore : Expression.TyEnv}
    {func func' : Function} {outR : LMonoTy} {insR : LMonoTys}
    {positions : Function.CheckedPositions}
    (run : Function.CoreRun sc tn C Env EnvCore func func' outR insR positions)
    (h_aw : TContext.AliasesWF Env.context) :
    (∀ v ∈ LMonoTys.freeVars (ListMap.values (func.inputs.keys.zip insR)),
        v ∈ (Function.rigidNames sc C func tn).map Prod.fst)
    ∧ (∀ v ∈ LMonoTy.freeVars outR, v ∈ (Function.rigidNames sc C func tn).map Prod.fst)
    ∧ LMonoTy.freeVars (skolemizeTy (Function.rigidNames sc C func tn) outR) = []
    ∧ deskolemizeTy (Function.rigidNames sc C func tn)
        (skolemizeTy (Function.rigidNames sc C func tn) outR) = outR
    ∧ (∀ mty ∈ ListMap.values (func.inputs.keys.zip insR),
        deskolemizeTy (Function.rigidNames sc C func tn)
          (skolemizeTy (Function.rigidNames sc C func tn) mty) = mty) := by
  have hnd := (Function.rigidNames_fresh sc C func tn).2.1
  have hfresh := (Function.rigidNames_fresh sc C func tn).2.2.1
  obtain ⟨-, hvals, hoe⟩ := run.resolvedSig
  have hnudOut :
      ∀ v ∈ LMonoTy.freeVars outR, v ∈ (Function.rigidNames sc C func tn).map Prod.fst := by
    rw [(Function.rigidNames_fresh sc C func tn).2.2.2.1]
    intro v hv
    exact run.sigDeclared v (mem_freeVars_mkArrow'_output func.output v func.inputs.values
      ((AliasEquiv.freeVars_iff h_aw hoe v).mpr hv))
  have hnudSig : ∀ v ∈ LMonoTys.freeVars (ListMap.values (func.inputs.keys.zip insR)),
      v ∈ (Function.rigidNames sc C func tn).map Prod.fst := by
    rw [(Function.rigidNames_fresh sc C func tn).2.2.2.1]
    intro v hv
    rw [hvals] at hv
    obtain ⟨ty, hty, hvty⟩ := LMonoTys.freeVars_exists hv
    obtain ⟨tyD, htyD, hequiv, -⟩ := forall2_exists_left run.insResolved ty hty
    exact run.sigDeclared v (mem_freeVars_mkArrow'_input func.output v func.inputs.values tyD
      htyD ((AliasEquiv.freeVars_iff h_aw hequiv v).mpr hvty))
  have hrtOut : deskolemizeTy (Function.rigidNames sc C func tn)
      (skolemizeTy (Function.rigidNames sc C func tn) outR) = outR := by
    rw [deskolemizeTy_skolemizeTy_eq_deskolemizeTy hnd]
    exact deskolemizeTy_eq_self_of_knownInstance C hfresh outR run.outKnown
  refine ⟨hnudSig, hnudOut,
    LMonoTy.freeVars_skolemizeTy_eq_nil (Function.rigidNames sc C func tn) outR hnudOut,
    hrtOut, ?_⟩
  intro mty hmty
  rw [hvals] at hmty
  obtain ⟨-, -, -, hkn⟩ := forall2_exists_left run.insResolved mty hmty
  rw [deskolemizeTy_skolemizeTy_eq_deskolemizeTy hnd]
  exact deskolemizeTy_eq_self_of_knownInstance C hfresh mty hkn

/-- The type parameters of a function the checker checks are distinct names a user may write,
    and every type variable of its declared signature is one of them. -/
private theorem Function.Checked.declared_guards
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv) (func func' : Function)
    (h : Function.Checked sc tn C Env Env' func func') :
    func.typeArgs.Nodup
      ∧ (∀ v ∈ LMonoTy.freeVars (LMonoTy.mkArrow' func.output func.inputs.values),
          v ∈ func.typeArgs)
      ∧ (∀ a ∈ func.typeArgs, isAllowedName a = true) := by
  obtain ⟨_, _, _, run⟩ := h.run
  exact ⟨run.typeArgsNodup, run.sigDeclared, h.allowed⟩

/-- A successful function check keeps the declared formal identifiers in order and keeps the
    declared type parameters. -/
private theorem Function.Checked.signature_shape
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv) (func func' : Function)
    (h : Function.Checked sc tn C Env Env' func func') :
    (∃ insR : LMonoTys, func'.inputs = func.inputs.keys.zip insR)
      ∧ func'.typeArgs = func.typeArgs := by
  obtain ⟨_, insR, _, run⟩ := h.run
  rw [run.stored]
  exact ⟨⟨insR, rfl⟩, rfl⟩

/-! ## Identifiers -/

/-- Formals with distinct identifiers have distinct names. -/
private theorem nodup_names_of_nodup_keys (m : ListMap CoreIdent LMonoTy)
    (h : (ListMap.keys m).Nodup) : (m.map (fun p => p.1.name)).Nodup := by
  have hmap : m.map (fun p => p.1.name) = (ListMap.keys m).map (fun id => id.name) := by
    rw [ListMap.keys_eq_map_fst m, List.map_map (l := m)]; rfl
  rw [hmap]
  exact List.nodup_map_of_injective _ _ coreIdent_name_injective h

/-! ## The elaborated signature, the position walk, and a missing body -/

/-- A successful check elaborates the signature to types adding no type variables, keeping the
    formals and type parameters; each type parameter occurs in it. -/
private theorem Function.Checked.elaborated_shape
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv) (func func' : Function)
    (h : Function.Checked sc tn C Env Env' func func')
    (h_aw : TContext.AliasesWF Env.context) :
    ∃ outR insR,
      (∀ v ∈ LMonoTy.freeVars outR, v ∈ LMonoTy.freeVars func.output)
      ∧ (∀ ity ∈ insR, ∀ v ∈ LMonoTy.freeVars ity,
            v ∈ LMonoTy.freeVars (LMonoTy.mkArrow' func.output func.inputs.values))
      ∧ func'.output = outR
      ∧ func'.inputs = func.inputs.keys.zip insR
      ∧ func'.typeArgs = func.typeArgs
      ∧ (∀ ta ∈ func'.typeArgs,
          ta ∈ LMonoTy.freeVars (LMonoTy.mkArrow' func'.output func'.inputs.values)) := by
  obtain ⟨outR, insR, _, run⟩ := h.run
  have hvals := run.resolvedSig.2.1
  rw [run.stored]
  refine ⟨outR, insR, LExpr.LMonoTy_resolveAliases_freeVars_subset (T := CoreLParams)
    func.output Env outR Env run.outResolved h_aw, ?_, rfl, rfl, rfl, ?_⟩
  · intro ity hity v hv
    obtain ⟨tyD, htyD, hequiv, -⟩ := forall2_exists_left run.insResolved ity hity
    exact mem_freeVars_mkArrow'_input func.output v func.inputs.values tyD htyD
      ((AliasEquiv.freeVars_iff h_aw hequiv v).mpr hv)
  · intro ta hta
    change ta ∈ LMonoTy.freeVars
      (LMonoTy.mkArrow' outR (ListMap.values (func.inputs.keys.zip insR)))
    rw [hvals]
    exact run.typeArgsInSig ta hta

/-- A successful position walk runs the body, measure, precondition and axiom checks in that
    order, each from the state the previous one returned, and returns their results. -/
private theorem checkPositions_inv {self : Option String}
    {C : Expression.TyContext} {Env : Expression.TyEnv} {func : Function}
    {outR : LMonoTy} {insR : LMonoTys} {σ : RigidNames}
    {positions : Function.CheckedPositions}
    (h : Function.checkPositions self C Env func outR insR σ = .ok positions) :
    ∃ Ebody Emeasure Epre,
      Function.checkBody self C Env func outR σ (func.inputs.keys.zip insR)
          = .ok (positions.body, Ebody)
      ∧ Function.checkMeasure self C Ebody func σ (func.inputs.keys.zip insR)
          = .ok (positions.measure, Emeasure)
      ∧ Function.checkPreconditions C Emeasure func.name.name σ (func.inputs.keys.zip insR)
          func.preconditions = .ok (positions.preconditions, Epre)
      ∧ Function.checkAxioms C Epre func.name.name σ (func.inputs.keys.zip insR) func.axioms
          = .ok (positions.axioms, positions.env) := by
  unfold Function.checkPositions at h
  obtain ⟨⟨bodyT, Ebody⟩, hbody, h2⟩ := (Except.bind_is_ok _ _ _).mp h
  obtain ⟨⟨measureT, Emeasure⟩, hmeasure, h3⟩ := (Except.bind_is_ok _ _ _).mp h2
  obtain ⟨⟨preT, Epre⟩, hpre, h4⟩ := (Except.bind_is_ok _ _ _).mp h3
  obtain ⟨⟨axT, Eax⟩, hax, hfin⟩ := (Except.bind_is_ok _ _ _).mp h4
  simp only [Except.ok.injEq] at hfin
  subst positions
  exact ⟨Ebody, Emeasure, Epre, hbody, hmeasure, hpre, hax⟩

/-- Checking a missing body records no body and keeps the state unchanged. -/
private theorem checkBody_of_none (self : Option String)
    (C : Expression.TyContext) (Env : Expression.TyEnv) (func : Function)
    (outR : LMonoTy) (σ : RigidNames) (sig : @LMonoTySignature Unit)
    (hbody : func.body = none) :
    Function.checkBody self C Env func outR σ sig = .ok (none, Env) := by
  simp only [Function.checkBody, hbody]

/-- If the source function has no body, the position walk records no body. -/
private theorem checkPositions_body_none {self : Option String}
    (C : Expression.TyContext) (Env : Expression.TyEnv) (func : Function)
    (outR : LMonoTy) (insR : LMonoTys) (σ : RigidNames)
    (positions : Function.CheckedPositions)
    (h : Function.checkPositions self C Env func outR insR σ = .ok positions)
    (hbody : func.body = none) :
    positions.body = none := by
  obtain ⟨Ebody, -, -, hb, -⟩ := checkPositions_inv h
  rw [checkBody_of_none self C Env func outR σ (func.inputs.keys.zip insR) hbody] at hb
  simp only [Except.ok.injEq, Prod.mk.injEq] at hb
  exact hb.1.symm

/-- A function the checker accepted as a constructor has no elaborated body. -/
private theorem Function.Checked.constr_no_body
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv) (func func' : Function)
    (h : Function.Checked sc tn C Env Env' func func') :
    func'.isConstr = true → func'.body = none := by
  obtain ⟨_, _, _, run⟩ := h.run
  rw [run.stored]
  intro hc
  have hnone := checkPositions_body_none _ _ _ _ _ _ _ run.positionsOk.choose_spec
    (run.constrNoBody hc)
  simp only [hnone, Option.map_none]

/-! ## Elaborated signature types are registered -/

/-- A successfully checked function's elaborated input and output types use registered
    constructors. -/
private theorem Function.Checked.signatureTysKnown
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv) (func func' : Function)
    (h : Function.Checked sc tn C Env Env' func func') :
    (∀ ity ∈ func'.inputs.values, LMonoTy.knownInstance ity C.knownTypes = true) ∧
      LMonoTy.knownInstance func'.output C.knownTypes = true := by
  obtain ⟨_, _, _, run⟩ := h.run
  rw [run.stored]
  refine ⟨?_, run.outKnown⟩
  intro ity hity
  obtain ⟨k, hk⟩ := ListMap.mem_values _ ity hity
  obtain ⟨-, -, -, hknown⟩ := forall2_exists_left run.insResolved ity (List.of_mem_zip hk).2
  exact hknown

variable (C : Expression.TyContext) (Env Env' : Expression.TyEnv) (func func' : Function)

/-! ## Checking the four expression positions -/

/-! ### Input typing at one position -/

/-- A judgment for the skolemized expression in the substituted formals environment gives one for
    `e` in the scope binding each formal at its own type, at the deskolemized type. -/
private theorem formalsEnv_HasType_deskolemize
    (C : Expression.TyContext) (Env : Expression.TyEnv) (σ : RigidNames)
    (hpfx : RigidNamesPrefixed σ) (hnd : (σ.map Prod.snd).Nodup)
    (nm : Option String) (sigR : @LMonoTySignature Unit)
    (e : Expression.Expr) (mtySk : LMonoTy) (Ssub : Subst)
    (hHT : LExpr.HasType (T := CoreLParams) (addSkolemTypes C σ)
        (TContext.subst (Function.formalsEnv Env σ sigR).context Ssub)
        (skolemizeBody nm σ e) (.forAll [] mtySk))
    (h_closed' : LExpr.checkContextTypesClosed (T := CoreLParams)
      (Function.formalsEnv Env σ sigR))
    (h_aliasesWF : Lambda.TContext.AliasesWF Env.context)
    (h_fac : FactorySigWF C.functions)
    (h_amb : NoSkolemAmbient C Env.context σ)
    (h_mono : MonoScope Env.context)
    (h_rt_sig : ∀ mty ∈ sigR.values, deskolemizeTy σ (skolemizeTy σ mty) = mty)
    (h_allowed : allExprTys (mtyAllTyConsNames (notRigidConst σ)) e = true)
    (h_lits : ConstTysFixed σ e) :
    LExpr.HasType (T := CoreLParams) C
      { Env.context with types := Env.context.types.push (formalsScope sigR) }
      e (.forAll [] (deskolemizeTy σ mtySk)) := by
  have hHT2 : LExpr.HasType (T := CoreLParams) (addSkolemTypes C σ)
      (Function.formalsEnv Env σ sigR).context (skolemizeBody nm σ e) (.forAll [] mtySk) :=
    HasType_FindEq _ _ _ _ _
      (LExpr.TContext.FindEq_subst_of_closed (T := CoreLParams)
        (Function.formalsEnv Env σ sigR).context _
        (LExpr.ctx_closed_of_check (T := CoreLParams) (Function.formalsEnv Env σ sigR)
          h_closed')) hHT
  have hHT3 : LExpr.HasType (T := CoreLParams) (addSkolemTypes C σ)
      { Env.context with types := Env.context.types.push (skolemScope σ sigR) }
      (skolemizeBody nm σ e) (.forAll [] mtySk) := by
    rw [formalsEnv_eq_push Env σ sigR] at hHT2
    exact HasType_FindEq _ _ _ _ _ (push_addInNewestContext_FindEq (T := CoreLParams) Env _) hHT2
  exact HasType_of_skolemScope_general C Env.context σ hpfx sigR e (skolemizeBody nm σ e) mtySk
    hHT3 h_amb h_fac h_aliasesWF h_mono h_rt_sig
    (allExprTys_annotNoRigidClash_skolemizeBody nm σ e h_allowed)
    (ConstTysFixed_skolemizeBody nm h_lits)
    (mapExprTys_deskolemizeTy_skolemizeBody nm hnd e h_allowed)

/-- Resolving a skolemized expression against a ground type types the source expression at the
    deskolemized type, in the scope binding each formal at its own type. -/
theorem funcPosition_HasType
    (C : Expression.TyContext) (Env EnvR : Expression.TyEnv) (σ : RigidNames)
    (hpfx : RigidNamesPrefixed σ) (hnd : (σ.map Prod.snd).Nodup)
    (nm : Option String) (sigR : @LMonoTySignature Unit)
    (e : Expression.Expr) (mtySk : LMonoTy) (et : LExprT CoreLParams.mono)
    (h_res : resolveWithType (addSkolemTypes C σ) (Function.formalsEnv Env σ sigR)
        (skolemizeBody nm σ e) mtySk = .ok (et, EnvR))
    (h_ws : LExpr.WellScoped (T := CoreLParams) (skolemizeBody nm σ e)
        (Function.formalsEnv Env σ sigR).context)
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env)
    (h_closed : LExpr.checkContextTypesClosed (T := CoreLParams) Env)
    (h_fac : FactorySigWF C.functions)
    (h_amb : NoSkolemAmbient C Env.context σ)
    (h_mono : MonoScope Env.context)
    (h_nud : ∀ v ∈ LMonoTys.freeVars sigR.values, v ∈ σ.map Prod.fst)
    (h_rt_sig : ∀ mty ∈ sigR.values, deskolemizeTy σ (skolemizeTy σ mty) = mty)
    (h_allowed : allExprTys (mtyAllTyConsNames (notRigidConst σ)) e = true)
    (h_lits : ConstTysFixed σ e)
    (h_ground : LMonoTy.freeVars mtySk = []) :
    LExpr.HasType (T := CoreLParams) C
      { Env.context with types := Env.context.types.push (formalsScope sigR) }
      e (.forAll [] (deskolemizeTy σ mtySk)) := by
  have hwf := formalsEnv_TEnvWF Env σ sigR h_env h_nud
  have hclosed' := formalsEnv_typesClosed Env σ sigR h_closed h_nud
  have hfac' := FactorySigWF.addSkolemTypes C σ h_fac
  have hHT := resolveWithType_HasType_ground (addSkolemTypes C σ)
    (Function.formalsEnv Env σ sigR) EnvR (skolemizeBody nm σ e) et mtySk h_res h_ground hwf
    hfac' h_ws (formalsEnv_MonoScope Env σ sigR h_mono)
  exact formalsEnv_HasType_deskolemize C Env σ hpfx hnd nm sigR e mtySk EnvR.stateSubstInfo.subst
    hHT hclosed' h_env.aliasesWF h_fac h_amb h_mono h_rt_sig h_allowed h_lits

/-! ### The position walk, and well-formedness of the elaborated function -/

/-- Putting back an earlier context keeps the environment well formed if the generator only
    advanced. -/
theorem updateContext_preserves_TEnvWF_of_mono
    (Env0 Env : Expression.TyEnv)
    (h0 : LExpr.TEnvWF (T := CoreLParams) Env0)
    (h : LExpr.TEnvWF (T := CoreLParams) Env)
    (hmono : Env0.genEnv.genState.tyGen ≤ Env.genEnv.genState.tyGen) :
    LExpr.TEnvWF (T := CoreLParams) (Env.updateContext Env0.context) := by
  refine ⟨h0.aliasesWF, h.substFreshForGen, ?_, h0.boundVarsNodup, ?_⟩
  · intro v hv n hn
    exact h0.ctxFreshForGen v hv n (Nat.le_trans hmono hn)
  · intro y ty hfind v hv n hn
    exact h0.boundVarsFresh y ty hfind v hv n (Nat.le_trans hmono hn)

/-- Closing the formals scope after resolving a position gives a well-formed state with the
    caller's context, whose substitution absorbs the caller's. -/
private theorem closeFormals_after_resolve
    (C : Expression.TyContext) (Env EnvR : Expression.TyEnv)
    (σ : RigidNames) (sig : @LMonoTySignature Unit)
    (e : Expression.Expr) (et : LExprT CoreLParams.mono) (mty : LMonoTy)
    (hres : resolveWithType C (Function.formalsEnv Env σ sig) e mty = .ok (et, EnvR))
    (hground : LMonoTy.freeVars mty = [])
    (henv : LExpr.TEnvWF (T := CoreLParams) Env)
    (hnud : ∀ v ∈ LMonoTys.freeVars sig.values, v ∈ σ.map Prod.fst)
    (hfac : FactorySigWF C.functions) :
    LExpr.TEnvWF (T := CoreLParams) (Function.closeFormals Env EnvR)
      ∧ (Function.closeFormals Env EnvR).context = Env.context
      ∧ Subst.absorbs (Function.closeFormals Env EnvR).stateSubstInfo.subst
          Env.stateSubstInfo.subst := by
  have hformals : LExpr.TEnvWF (T := CoreLParams) (Function.formalsEnv Env σ sig) :=
    formalsEnv_TEnvWF Env σ sig henv hnud
  have hresolved : LExpr.TEnvWF (T := CoreLParams) EnvR :=
    resolveWithType_TEnvWF_ground C (Function.formalsEnv Env σ sig) EnvR e et mty hres
      hground hformals hfac
  have hmono :
      Env.genEnv.genState.tyGen ≤ EnvR.genEnv.genState.tyGen := by
    have hm := resolveWithType_genState_tyGen_mono C
      (Function.formalsEnv Env σ sig) EnvR e et mty hres
    change Env.genEnv.genState.tyGen ≤ EnvR.genEnv.genState.tyGen at hm
    exact hm
  have habs := resolveWithType_absorbs C
    (Function.formalsEnv Env σ sig) EnvR e et mty hres hformals hfac
  refine ⟨?_, ?_, ?_⟩
  · simpa only [Function.closeFormals] using
      updateContext_preserves_TEnvWF_of_mono Env EnvR henv hresolved hmono
  · rfl
  · simpa only [Function.closeFormals, Function.formalsEnv, TEnv.pushEmptyContext,
      TEnv.addInNewestContext, TEnv.updateContext] using habs

/-- One checked position: `e` resolves in the formals environment at `mty` to `et`; `EnvNext` is
    the resolver's final state with the context of `Env` put back. -/
private def PositionRun
    (C : Expression.TyContext) (Env : Expression.TyEnv) (σ : RigidNames)
    (sig : @LMonoTySignature Unit) (e : Expression.Expr) (mty : LMonoTy)
    (et : LExprT CoreLParams.mono) (EnvNext : Expression.TyEnv) : Prop :=
  ∃ EnvR,
    resolveWithType C (Function.formalsEnv Env σ sig) e mty = .ok (et, EnvR)
      ∧ EnvNext = Function.closeFormals Env EnvR

/-- A position run from a well-formed state with `EnvBase`'s context, where `EnvFinal`'s
    substitution absorbs the one right after the run. -/
private def ThreadedPosition
    (C : Expression.TyContext) (EnvBase EnvFinal : Expression.TyEnv) (σ : RigidNames)
    (sig : @LMonoTySignature Unit) (e : Expression.Expr) (mty : LMonoTy)
    (et : LExprT CoreLParams.mono) : Prop :=
  ∃ EnvStart EnvNext,
    EnvStart.context = EnvBase.context
      ∧ LExpr.TEnvWF (T := CoreLParams) EnvStart
      ∧ PositionRun C EnvStart σ sig e mty et EnvNext
      ∧ Subst.absorbs EnvFinal.stateSubstInfo.subst EnvNext.stateSubstInfo.subst

/-- A threaded position stays one across later checks and an equal base context. -/
private theorem ThreadedPosition.transfer
    (h : ThreadedPosition C EnvBase EnvMid σ sig e mty et)
    (hctx : EnvBase.context = EnvBase'.context)
    (habs : Subst.absorbs EnvFinal.stateSubstInfo.subst EnvMid.stateSubstInfo.subst) :
    ThreadedPosition C EnvBase' EnvFinal σ sig e mty et := by
  obtain ⟨EnvStart, EnvNext, hstart, hwf, hrun, hmid⟩ := h
  exact ⟨EnvStart, EnvNext, hstart.trans hctx, hwf, hrun,
    Subst.absorbs_trans _ _ _ hmid habs⟩

/-- A threaded position at a bare variable `x` whose result reads only formals of `sig`
    elaborates to an annotated `x`, and `x` is a formal of `sig`. -/
private theorem ThreadedPosition.fvar_mem_keys
    {C : Expression.TyContext} {EnvBase EnvFinal : Expression.TyEnv} {σ : RigidNames}
    {sig : @LMonoTySignature Unit} {s : Option String} {mid} {x : CoreIdent} {ann}
    {mty : LMonoTy} {et : LExprT CoreLParams.mono}
    (h : ThreadedPosition C EnvBase EnvFinal σ sig (skolemizeBody s σ (.fvar mid x ann)) mty et)
    (hclosed : Function.nonInputVars sig et = []) :
    x ∈ ListMap.keys sig ∧ ∃ md ty, et = .fvar md x (some ty) := by
  obtain ⟨_, _, -, -, ⟨_, hres, -, -⟩, -⟩ := h
  simp only [skolemizeBody_fvar] at hres
  obtain ⟨md, ty, rfl⟩ := resolveWithType_fvar_shape _ _ _ _ _ _ _ _ hres
  have hname : x.name ∈ (LExpr.LExpr.getVars (LExpr.fvar md x (some ty))).map (·.name) := by
    simp [LExpr.LExpr.getVars]
  exact ⟨mem_keys_of_name_mem (getVars_names_subset_of_nonInputVars_nil hclosed hname),
    md, ty, rfl⟩

/-- A position run from a well-formed state against a ground type keeps the context, ends in a
    well-formed state whose substitution absorbs the start's, and is a threaded position. -/
private theorem PositionRun.threaded
    {C : Expression.TyContext} {Env EnvNext : Expression.TyEnv} {σ : RigidNames}
    {sig : @LMonoTySignature Unit} {e : Expression.Expr} {mty : LMonoTy}
    {et : LExprT CoreLParams.mono}
    (hrun : PositionRun C Env σ sig e mty et EnvNext)
    (hground : LMonoTy.freeVars mty = [])
    (henv : LExpr.TEnvWF (T := CoreLParams) Env)
    (hnud : ∀ v ∈ LMonoTys.freeVars sig.values, v ∈ σ.map Prod.fst)
    (hfac : FactorySigWF C.functions) :
    EnvNext.context = Env.context
      ∧ LExpr.TEnvWF (T := CoreLParams) EnvNext
      ∧ Subst.absorbs EnvNext.stateSubstInfo.subst Env.stateSubstInfo.subst
      ∧ ThreadedPosition C Env EnvNext σ sig e mty et := by
  have hthread : ThreadedPosition C Env EnvNext σ sig e mty et := by
    refine ⟨Env, EnvNext, rfl, henv, hrun, ?_⟩
    exact Subst.absorbs_refl _ EnvNext.stateSubstInfo.isWF
  obtain ⟨EnvR, hres, rfl⟩ := hrun
  have hstep := closeFormals_after_resolve C Env EnvR σ sig e et mty hres hground henv hnud hfac
  exact ⟨hstep.2.1, hstep.1, hstep.2.2, hthread⟩

/-- A successful position elaboration is a position run against the given type. -/
private theorem resolvePosition_inv
    {C : Expression.TyContext} {Env Env' : Expression.TyEnv} {self : Option String}
    {σ : RigidNames} {sig : @LMonoTySignature Unit} {e : Expression.Expr} {expected : LMonoTy}
    {typeErr : ResolveWithTypeError → Std.Format} {et : LExprT CoreLParams.mono}
    (h : Function.resolvePosition C Env self σ sig e expected typeErr = .ok (et, Env')) :
    PositionRun C Env σ sig (skolemizeBody self σ e) expected et Env' := by
  simp only [Function.resolvePosition] at h
  obtain ⟨⟨eT, eEnv⟩, hresMap, h3⟩ := (Except.bind_is_ok _ _ _).mp h
  simp only [Except.ok.injEq, Prod.mk.injEq] at h3
  obtain ⟨rfl, rfl⟩ := h3
  have hres := Except.mapError_ok_h' (SourceExpr.orFreeVarError_eq_ok.mp hresMap)
  rw [skolemizeBody_unless_isEmpty] at hres
  exact ⟨eEnv, hres, rfl⟩

/-- A successful position check is a position run against the given type whose result reads
    only formals of `sig`. -/
private theorem checkPosition_inv
    {C : Expression.TyContext} {Env Env' : Expression.TyEnv} {self : Option String}
    {σ : RigidNames} {sig : @LMonoTySignature Unit} {e : Expression.Expr} {expected : LMonoTy}
    {typeErr : ResolveWithTypeError → Std.Format} {extraErr : List String → Std.Format}
    {et : LExprT CoreLParams.mono}
    (h : Function.checkPosition C Env self σ sig e expected typeErr extraErr = .ok (et, Env')) :
    PositionRun C Env σ sig (skolemizeBody self σ e) expected et Env'
      ∧ Function.nonInputVars sig et = [] := by
  simp only [Function.checkPosition] at h
  obtain ⟨⟨eT, Enext⟩, hres, h2⟩ := (Except.bind_is_ok _ _ _).mp h
  split at h2
  · simp only [throw, throwThe, MonadExceptOf.throw, bind, Except.bind, reduceCtorEq] at h2
  rename_i hempty
  simp only [Except.ok.injEq, Prod.mk.injEq] at h2
  obtain ⟨rfl, rfl⟩ := h2
  have hclosed : Function.nonInputVars sig eT = [] := by
    simpa [List.isEmpty_iff] using hempty
  exact ⟨resolvePosition_inv hres, hclosed⟩

/-- A successful body check either finds no body and keeps the state, or checks the body as one
    position against the skolemized output type, reading only formals. -/
private theorem checkBody_inv {self : Option String}
    {C : Expression.TyContext} {Env Env' : Expression.TyEnv} {func : Function}
    {outR : LMonoTy} {σ : RigidNames} {sig : @LMonoTySignature Unit}
    {bodyT : Option (LExprT CoreLParams.mono)}
    (h : Function.checkBody self C Env func outR σ sig = .ok (bodyT, Env')) :
    (func.body = none ∧ bodyT = none ∧ Env' = Env)
      ∨ ∃ body et, func.body = some body ∧ bodyT = some et
          ∧ PositionRun C Env σ sig (skolemizeBody self σ body)
              (skolemizeTy σ outR) et Env'
          ∧ Function.nonInputVars sig et = [] := by
  cases hb : func.body with
  | none =>
    rw [checkBody_of_none self C Env func outR σ sig hb] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    exact Or.inl ⟨rfl, h.1.symm, h.2.symm⟩
  | some body =>
    rw [Function.checkBody, hb] at h
    dsimp only at h
    simp only [bind, Except.bind] at h
    obtain ⟨⟨et, EnvR⟩, hpos, h2⟩ := (Except.bind_is_ok _ _ _).mp h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h2
    obtain ⟨rfl, rfl⟩ := h2
    exact Or.inr ⟨body, et, rfl, rfl, checkPosition_inv hpos⟩

/-- A successful optional-measure check either finds no measure, or checks the measure as one
    position against its `measureTy` and finds that it reads only formals. -/
private theorem checkMeasure_inv {self : Option String}
    {C : Expression.TyContext} {Env Env' : Expression.TyEnv} {func : Function}
    {σ : RigidNames} {sig : @LMonoTySignature Unit}
    {measureT : Option (LExprT CoreLParams.mono)}
    (h : Function.checkMeasure self C Env func σ sig = .ok (measureT, Env')) :
    (func.measure = none ∧ measureT = none ∧ Env' = Env)
      ∨ ∃ m et, func.measure = some m ∧ measureT = some et
          ∧ PositionRun C Env σ sig (skolemizeBody self σ m)
              (skolemizeTy σ (Function.measureTy C sig m)) et Env'
          ∧ Function.nonInputVars sig et = [] := by
  cases hm : func.measure with
  | none =>
    rw [Function.checkMeasure, hm] at h
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h
    exact Or.inl ⟨rfl, h.1.symm, h.2.symm⟩
  | some m =>
    rw [Function.checkMeasure, hm] at h
    simp only [bind, Except.bind] at h
    obtain ⟨⟨et, EnvR⟩, hpos, h2⟩ := (Except.bind_is_ok _ _ _).mp h
    simp only [pure, Except.pure, Except.ok.injEq, Prod.mk.injEq] at h2
    obtain ⟨rfl, rfl⟩ := h2
    exact Or.inr ⟨m, et, rfl, rfl, checkPosition_inv hpos⟩

/-- A non-recursive function the checker accepted has no elaborated measure. -/
private theorem Function.Checked.measureOnlyRecursive
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv) (func func' : Function)
    (h : Function.Checked sc tn C Env Env' func func') :
    func'.isRecursive = false → func'.measure = none := by
  obtain ⟨_, _, _, run⟩ := h.run
  rw [run.stored]
  intro hr
  obtain ⟨_, _, _, -, hm, -⟩ := checkPositions_inv run.positionsOk.choose_spec
  rcases checkMeasure_inv hm with ⟨-, hnone, -⟩ | ⟨m, -, hsome, -⟩
  · simp only [hnone, Option.map_none]
  · rw [run.measureOnlyRecursive hr] at hsome
    exact absurd hsome (by simp)

/-- A successful check of `p :: ps` checks `p` as one position against `bool`, reading only
    formals, then checks `ps` from the state that position left. -/
private theorem checkPreconditions_cons_inv
    {C : Expression.TyContext} {Env Env' : Expression.TyEnv} {name : String}
    {σ : RigidNames} {sig : @LMonoTySignature Unit}
    {p : Strata.DL.Util.FuncPrecondition Expression.Expr Expression.ExprMetadata}
    {ps : List (Strata.DL.Util.FuncPrecondition Expression.Expr Expression.ExprMetadata)}
    {pts : List (Expression.ExprMetadata × LExprT CoreLParams.mono)}
    (h : Function.checkPreconditions C Env name σ sig (p :: ps) = .ok (pts, Env')) :
    ∃ pT Emid psT,
      PositionRun C Env σ sig (skolemizeBody (some name) σ p.expr) LMonoTy.bool pT Emid
      ∧ Function.nonInputVars sig pT = []
      ∧ Function.checkPreconditions C Emid name σ sig ps = .ok (psT, Env')
      ∧ pts = (p.md, pT) :: psT := by
  simp only [Function.checkPreconditions] at h
  obtain ⟨⟨pT, Emid⟩, hpos, h2⟩ := (Except.bind_is_ok _ _ _).mp h
  obtain ⟨⟨psT, Efinal⟩, hrest, hfin⟩ := (Except.bind_is_ok _ _ _).mp h2
  simp only [Except.ok.injEq, Prod.mk.injEq] at hfin
  obtain ⟨rfl, rfl⟩ := hfin
  obtain ⟨hrun, hclosed⟩ := checkPosition_inv hpos
  exact ⟨pT, Emid, psT, hrun, hclosed, hrest, rfl⟩

/-- Every precondition the precondition walk accepts reads no variable other than a formal of
    `sig`. -/
private theorem checkPreconditions_closed
    {C : Expression.TyContext} {name : String} {σ : RigidNames} {sig : @LMonoTySignature Unit} :
    ∀ (ps : List (Strata.DL.Util.FuncPrecondition Expression.Expr Expression.ExprMetadata))
      (Env Env' : Expression.TyEnv)
      (pts : List (Expression.ExprMetadata × LExprT CoreLParams.mono)),
      Function.checkPreconditions C Env name σ sig ps = .ok (pts, Env') →
      ∀ q ∈ pts, Function.nonInputVars sig q.2 = []
  | [], E, Env', pts, h => by
    simp only [Function.checkPreconditions, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    intro q hq
    exact absurd hq List.not_mem_nil
  | p :: ps, E, Env', pts, h => by
    obtain ⟨pT, Emid, psT, -, hhead, hrest, rfl⟩ := checkPreconditions_cons_inv h
    intro q hq
    rcases List.mem_cons.mp hq with rfl | hq'
    · exact hhead
    · exact checkPreconditions_closed ps _ _ psT hrest q hq'

/-- A successful axiom walk over a nonempty list checks the first axiom as one position against
    `bool` and then walks the rest from the state that position left. -/
private theorem checkAxioms_cons_inv
    {C : Expression.TyContext} {Env Env' : Expression.TyEnv} {name : String}
    {σ : RigidNames} {sig : @LMonoTySignature Unit}
    {ax : Expression.Expr} {axs : List Expression.Expr}
    {ats : List (LExprT CoreLParams.mono)}
    (h : Function.checkAxioms C Env name σ sig (ax :: axs) = .ok (ats, Env')) :
    ∃ axT Emid axsT,
      PositionRun C Env σ sig (skolemizeBody (some name) σ ax) LMonoTy.bool axT Emid
      ∧ Function.checkAxioms C Emid name σ sig axs = .ok (axsT, Env')
      ∧ ats = axT :: axsT := by
  simp only [Function.checkAxioms] at h
  obtain ⟨⟨axT, Emid⟩, hpos, h2⟩ := (Except.bind_is_ok _ _ _).mp h
  obtain ⟨⟨axsT, Efinal⟩, hrest, hfin⟩ := (Except.bind_is_ok _ _ _).mp h2
  simp only [Except.ok.injEq, Prod.mk.injEq] at hfin
  obtain ⟨rfl, rfl⟩ := hfin
  exact ⟨axT, Emid, axsT, resolvePosition_inv hpos, hrest, rfl⟩

/-- Storing an elaborated expression keeps its free-variable names. -/
private theorem freeVarNames_stored (σ : RigidNames) (S : Subst) (eT : LExprT CoreLParams.mono) :
    (LExpr.freeVars (finishDeskolemized σ S eT)).map (fun p => p.1.name)
      = (LExpr.LExpr.getVars eT).map (fun x => x.name) := by
  have hcomp : (fun p : CoreIdent × Option LMonoTy => p.1.name)
      = (fun x : CoreIdent => x.name) ∘ Prod.fst := rfl
  rw [hcomp, ← List.map_map, ← getVars_eq_freeVars_idents (T := CoreLParams), finishDeskolemized,
    getVars_replaceUserProvidedType, LExpr.Proofs.getVars_unresolved,
    LExpr.Proofs.getVars_applySubstT]

/-- The body and every precondition of a function the checker accepted read only the
    function's inputs. -/
private theorem Function.Checked.closed
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv) (func func' : Function)
    (h : Function.Checked sc tn C Env Env' func func') :
    (∀ b, func'.body = some b →
      (LExpr.freeVars b).map (fun p => p.1.name) ⊆ func'.inputs.map (fun p => p.1.name))
    ∧ ∀ p ∈ func'.preconditions,
      (LExpr.freeVars p.expr).map (fun p => p.1.name) ⊆ func'.inputs.map (fun p => p.1.name) := by
  obtain ⟨outR, insR, positions, run⟩ := h.run
  obtain ⟨_, _, _, hbody, -, hpre, -⟩ := checkPositions_inv run.positionsOk.choose_spec
  rw [run.stored]
  refine ⟨?_, ?_⟩
  · intro b hb
    obtain ⟨eT, heT, rfl⟩ := Option.map_eq_some_iff.mp hb
    rw [freeVarNames_stored]
    rw [heT] at hbody
    rcases checkBody_inv hbody with ⟨-, hnone, -⟩ | ⟨-, et, -, hsome, -, hclosed⟩
    · simp only [reduceCtorEq] at hnone
    · rw [Option.some.inj hsome]
      exact getVars_names_subset_of_nonInputVars_nil hclosed
  · intro p hp
    obtain ⟨⟨md, eT⟩, hq, rfl⟩ := List.mem_map.mp hp
    rw [freeVarNames_stored]
    exact getVars_names_subset_of_nonInputVars_nil
      (checkPreconditions_closed _ _ _ _ hpre (md, eT) hq)

/-- The elaborated form of a function the checker checks is a well-formed `LFunc` when the
    aliases are well formed. -/
private theorem Function.Checked.lFuncWF
    (h : Function.Checked sc tn C Env Env' func func')
    (h_aw : TContext.AliasesWF Env.context) :
    LFuncWF (T := CoreLParams) (func'.toLFunc none) := by
  obtain ⟨hta, hsigDecl, hallow⟩ :=
    Function.Checked.declared_guards C Env Env' func func' h
  obtain ⟨_, _, _, run⟩ := h.run
  have hnd := run.inputsNodup
  obtain ⟨outR, insR, hOutFree, hInsFree, hOutEq, hInEq, hTaEq, -⟩ :=
    Function.Checked.elaborated_shape C Env Env' func func' h h_aw
  refine
    { arg_nodup := ?_
      typeArgs_nodup := ?_
      inputs_typevars_in_typeArgs := ?_
      output_typevars_in_typeArgs := ?_
      body_freevars := (Function.Checked.closed C Env Env' func func' h).1
      precond_freevars := (Function.Checked.closed C Env Env' func func' h).2
      constr_no_eval := ?_
      typeArgs_no_gen_prefix := ?_
      concreteEval_argmatch := by
        intro fn _ _ _ _ hfn; simp [LFuncDefined.toLFunc] at hfn
      body_or_concreteEval := by simp [LFuncDefined.toLFunc]
      concreteEval_eraseMetadata := by
        intro _ hce; simp [LFuncDefined.toLFunc] at hce
      concreteEval_freeVars := by
        intro _ hce; simp [LFuncDefined.toLFunc] at hce
      shortCircuit_substFvars := by
        intro _ _ hce; simp [LFuncDefined.toLFunc] at hce }
  · show (func'.inputs.map (fun p => p.1.name)).Nodup
    rw [hInEq]
    have hsub : ((func.inputs.keys.zip insR).map Prod.fst).Sublist func.inputs.keys :=
      List.map_fst_zip_sublist _ _
    have hsubn : (((func.inputs.keys.zip insR).map Prod.fst).map (fun id => id.name)).Sublist
        (func.inputs.keys.map (fun id => id.name)) := hsub.map _
    rw [List.map_map] at hsubn
    exact List.Nodup.sublist hsubn
      (List.nodup_map_of_injective _ _ coreIdent_name_injective hnd)
  · show func'.typeArgs.Nodup
    rw [hTaEq]; exact hta
  · intro ty hty v hv
    obtain ⟨k, hk⟩ := ListMap.mem_values _ ty (hInEq ▸ hty)
    have htyIns : ty ∈ insR := (List.of_mem_zip hk).2
    have hvdecl : v ∈ LMonoTy.freeVars (LMonoTy.mkArrow' func.output func.inputs.values) :=
      hInsFree ty htyIns v hv
    exact hTaEq ▸ hsigDecl v hvdecl
  · intro v hv0
    replace hv0 : v ∈ LMonoTy.freeVars func'.output := hv0
    rw [hOutEq] at hv0
    have hvdecl : v ∈ LMonoTy.freeVars (LMonoTy.mkArrow' func.output func.inputs.values) :=
      mem_freeVars_mkArrow'_output func.output v func.inputs.values (hOutFree v hv0)
    exact hTaEq ▸ hsigDecl v hvdecl
  · intro hc
    exact ⟨Function.Checked.constr_no_body C Env Env' func func' h hc, rfl⟩
  · intro ta hta0
    replace hta0 : ta ∈ func'.typeArgs := hta0
    exact not_genTyPrefix_of_isAllowedName
      (hallow ta (hTaEq ▸ hta0))

/-- For any name sets, a function elaborated by a successful `Function.typeCheckIn` run yields a
    well-formed `LFunc` when the aliases are well formed. -/
theorem LFuncWF_of_typeCheckIn
    (scope : Thunk (Std.HashSet String)) (C : Expression.TyContext) (Env : Expression.TyEnv)
    (func renamed func' : Function)
    (h : Function.typeCheckIn scope C Env func = .ok (renamed, func'))
    (h_aw : TContext.AliasesWF Env.context) :
    LFuncWF (T := CoreLParams) (func'.toLFunc none) := by
  obtain ⟨-, EnvCore, hc⟩ := Function.typeCheckIn_checked h
  exact Function.Checked.lFuncWF C Env EnvCore _ func' hc h_aw

/-- A successful check of an optional position preserves the threaded invariants and pairs a
    present source expression with its resolver run against its ground type, reading only
    formals. -/
private theorem optPosition_trace
    {C : Expression.TyContext} {Env Env' : Expression.TyEnv} {self : Option String}
    {σ : RigidNames} {sig : @LMonoTySignature Unit} {src : Option Expression.Expr}
    {mtyOf : Expression.Expr → LMonoTy} {resT : Option (LExprT CoreLParams.mono)}
    (hinv : (src = none ∧ resT = none ∧ Env' = Env)
      ∨ ∃ e et, src = some e ∧ resT = some et
          ∧ PositionRun C Env σ sig (skolemizeBody self σ e) (mtyOf e) et Env'
          ∧ Function.nonInputVars sig et = [])
    (hground : ∀ e, src = some e → LMonoTy.freeVars (mtyOf e) = [])
    (henv : LExpr.TEnvWF (T := CoreLParams) Env)
    (hnud : ∀ v ∈ LMonoTys.freeVars sig.values, v ∈ σ.map Prod.fst)
    (hfac : FactorySigWF C.functions) :
    Env'.context = Env.context
      ∧ LExpr.TEnvWF (T := CoreLParams) Env'
      ∧ Subst.absorbs Env'.stateSubstInfo.subst Env.stateSubstInfo.subst
      ∧ (∀ e, src = some e → ∃ et, resT = some et
          ∧ ThreadedPosition C Env Env' σ sig (skolemizeBody self σ e) (mtyOf e) et
          ∧ Function.nonInputVars sig et = [])
      ∧ (∀ et, resT = some et → ∃ e, src = some e
          ∧ ThreadedPosition C Env Env' σ sig (skolemizeBody self σ e) (mtyOf e) et
          ∧ Function.nonInputVars sig et = []) := by
  rcases hinv with ⟨hsrc, rfl, rfl⟩ | ⟨e, et, hsrc, rfl, hrun, hclosed⟩
  · refine ⟨rfl, henv, Subst.absorbs_refl _ Env'.stateSubstInfo.isWF, ?_, ?_⟩
    · intro e he
      rw [hsrc] at he
      exact absurd he (by simp)
    · intro et het
      exact absurd het (by simp)
  · obtain ⟨hctx, hwf, habs, hthread⟩ := hrun.threaded (hground e hsrc) henv hnud hfac
    refine ⟨hctx, hwf, habs, ?_, ?_⟩
    · intro e' he'
      rw [hsrc, Option.some.injEq] at he'
      subst e'
      exact ⟨et, rfl, hthread, hclosed⟩
    · intro et' het'
      rw [Option.some.injEq] at het'
      subst et'
      exact ⟨e, hsrc, hthread, hclosed⟩

/-- A walk checking each element of a list as one position against `bool`, from the state the
    previous element left, and recording `out x et` for an element `x` elaborated to `et`. -/
private structure BoolWalk {α β : Type} (C : Expression.TyContext) (name : String)
    (σ : RigidNames) (sig : @LMonoTySignature Unit) (expr : α → Expression.Expr)
    (out : α → LExprT CoreLParams.mono → β)
    (walk : Expression.TyEnv → List α → Except Std.Format (List β × Expression.TyEnv)) : Prop where
  /-- The empty walk records nothing and keeps the state. -/
  nil : ∀ E, walk E [] = .ok ([], E)
  /-- A nonempty walk checks the head, then walks the tail from the state the head left. -/
  cons : ∀ E E' x xs r, walk E (x :: xs) = .ok (r, E') → ∃ xT Emid rest,
    PositionRun C E σ sig (skolemizeBody (some name) σ (expr x)) LMonoTy.bool xT Emid
      ∧ walk Emid xs = .ok (rest, E') ∧ r = out x xT :: rest

/-- A successful `bool` walk preserves the threaded environment invariants and pairs every source
    element with the resolver run that produced its record. -/
private theorem BoolWalk.trace {α β : Type} {C : Expression.TyContext} {name : String}
    {σ : RigidNames} {sig : @LMonoTySignature Unit} {expr : α → Expression.Expr}
    {out : α → LExprT CoreLParams.mono → β}
    {walk : Expression.TyEnv → List α → Except Std.Format (List β × Expression.TyEnv)}
    (hw : BoolWalk C name σ sig expr out walk)
    (hnud : ∀ v ∈ LMonoTys.freeVars sig.values, v ∈ σ.map Prod.fst)
    (hfac : FactorySigWF C.functions) :
    ∀ (xs : List α) (Env Env' : Expression.TyEnv) (r : List β), walk Env xs = .ok (r, Env') →
      LExpr.TEnvWF (T := CoreLParams) Env →
      Env'.context = Env.context
        ∧ LExpr.TEnvWF (T := CoreLParams) Env'
        ∧ Subst.absorbs Env'.stateSubstInfo.subst Env.stateSubstInfo.subst
        ∧ List.Rel₂ (fun x y => ∃ et, y = out x et
            ∧ ThreadedPosition C Env Env' σ sig (skolemizeBody (some name) σ (expr x))
                LMonoTy.bool et) xs r := by
  intro xs
  induction xs with
  | nil =>
    intro Env Env' r h henv
    rw [hw.nil, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, hE⟩ := h
    rw [← hE]
    exact ⟨rfl, henv, Subst.absorbs_refl _ Env.stateSubstInfo.isWF, .nil⟩
  | cons x xs ih =>
    intro Env Env' r h henv
    obtain ⟨xT, Emid, rest, hrun, hrest, rfl⟩ := hw.cons _ _ _ _ _ h
    obtain ⟨hctx, hwf, habs, hthread⟩ := hrun.threaded rfl henv hnud hfac
    obtain ⟨hrestCtx, hrestWF, hrestAbs, hrestRel⟩ := ih Emid Env' rest hrest hwf
    refine ⟨hrestCtx.trans hctx, hrestWF, Subst.absorbs_trans _ _ _ habs hrestAbs,
      .cons ⟨xT, rfl, ThreadedPosition.transfer (C := C) hthread rfl hrestAbs⟩
        (hrestRel.imp fun _ _ hq => ?_)⟩
    obtain ⟨et, hy, hq⟩ := hq
    exact ⟨et, hy, ThreadedPosition.transfer (C := C) hq hctx
      (Subst.absorbs_refl _ Env'.stateSubstInfo.isWF)⟩

/-- A property that every `bool` run of a walked element preserves holds after a successful walk if
    it held before. -/
private theorem BoolWalk.preserves {α β : Type} {C : Expression.TyContext} {name : String}
    {σ : RigidNames} {sig : @LMonoTySignature Unit} {expr : α → Expression.Expr}
    {out : α → LExprT CoreLParams.mono → β}
    {walk : Expression.TyEnv → List α → Except Std.Format (List β × Expression.TyEnv)}
    (hw : BoolWalk C name σ sig expr out walk) (P : Expression.TyEnv → Prop) :
    ∀ (xs : List α),
      (∀ E x et E', P E → x ∈ xs →
        PositionRun C E σ sig (skolemizeBody (some name) σ (expr x)) LMonoTy.bool et E' → P E') →
      ∀ (Env Env' : Expression.TyEnv) (r : List β),
        walk Env xs = .ok (r, Env') → P Env → P Env' := by
  intro xs
  induction xs with
  | nil =>
    intro _ Env Env' r h h0
    rw [hw.nil, Except.ok.injEq, Prod.mk.injEq] at h
    rw [← h.2]
    exact h0
  | cons x xs ih =>
    intro hP Env Env' r h h0
    obtain ⟨xT, Emid, rest, hrun, hrest, -⟩ := hw.cons _ _ _ _ _ h
    exact ih (fun E q et E' hE hq hr => hP E q et E' hE (List.mem_cons_of_mem x hq) hr)
      Emid Env' rest hrest (hP _ _ _ _ h0 List.mem_cons_self hrun)

/-- A successful `bool` walk records one entry `out x et` for each source element `x`, in
    order. -/
private theorem BoolWalk.records {α β : Type} {C : Expression.TyContext} {name : String}
    {σ : RigidNames} {sig : @LMonoTySignature Unit} {expr : α → Expression.Expr}
    {out : α → LExprT CoreLParams.mono → β}
    {walk : Expression.TyEnv → List α → Except Std.Format (List β × Expression.TyEnv)}
    (hw : BoolWalk C name σ sig expr out walk) :
    ∀ (xs : List α) (Env Env' : Expression.TyEnv) (r : List β), walk Env xs = .ok (r, Env') →
      List.Rel₂ (fun x y => ∃ et, y = out x et) xs r
  | [], E, Env', r, h => by
    rw [hw.nil, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact .nil
  | x :: xs, E, Env', r, h => by
    obtain ⟨xT, Emid, rest, -, hrest, rfl⟩ := hw.cons _ _ _ _ _ h
    exact .cons ⟨xT, rfl⟩ (BoolWalk.records hw xs Emid Env' rest hrest)

/-- The precondition walk is a `bool` walk recording each precondition's metadata. -/
private theorem checkPreconditions_boolWalk (C : Expression.TyContext) (name : String)
    (σ : RigidNames) (sig : @LMonoTySignature Unit) :
    BoolWalk C name σ sig (·.expr) (fun p et => (p.md, et))
      (fun E ps => Function.checkPreconditions C E name σ sig ps) where
  nil E := by simp only [Function.checkPreconditions]
  cons _ _ _ _ _ h := by
    obtain ⟨pT, Emid, psT, hrun, -, hrest, hr⟩ := checkPreconditions_cons_inv h
    exact ⟨pT, Emid, psT, hrun, hrest, hr⟩

/-- The axiom walk is a `bool` walk recording each elaborated axiom. -/
private theorem checkAxioms_boolWalk (C : Expression.TyContext) (name : String)
    (σ : RigidNames) (sig : @LMonoTySignature Unit) :
    BoolWalk C name σ sig id (fun _ et => et)
      (fun E axs => Function.checkAxioms C E name σ sig axs) where
  nil E := by simp only [Function.checkAxioms]
  cons _ _ _ _ _ h := checkAxioms_cons_inv h

/-- The complete position walk threads one well-formed, absorbing inference state through body,
    measure, preconditions, and axioms in that order. -/
private theorem checkPositions_trace {self : Option String}
    (C : Expression.TyContext) (Env : Expression.TyEnv) (func : Function)
    (outR : LMonoTy) (insR : LMonoTys) (σ : RigidNames)
    (positions : Function.CheckedPositions)
    (h : Function.checkPositions self C Env func outR insR σ = .ok positions)
    (henv : LExpr.TEnvWF (T := CoreLParams) Env)
    (hnud : ∀ v ∈ LMonoTys.freeVars (ListMap.values (func.inputs.keys.zip insR)),
      v ∈ σ.map Prod.fst)
    (hground : LMonoTy.freeVars (skolemizeTy σ outR) = [])
    (hfac : FactorySigWF C.functions) :
    positions.env.context = Env.context
      ∧ LExpr.TEnvWF (T := CoreLParams) positions.env
      ∧ Subst.absorbs positions.env.stateSubstInfo.subst Env.stateSubstInfo.subst
      ∧ (∀ body, func.body = some body → ∃ et,
          positions.body = some et
            ∧ ThreadedPosition C Env positions.env σ (func.inputs.keys.zip insR)
                (skolemizeBody self σ body)
                (skolemizeTy σ outR) et)
      ∧ (∀ m, func.measure = some m → ∃ et, positions.measure = some et
          ∧ ThreadedPosition C Env positions.env σ (func.inputs.keys.zip insR)
              (skolemizeBody self σ m)
              (skolemizeTy σ (Function.measureTy C (func.inputs.keys.zip insR) m)) et
          ∧ Function.nonInputVars (func.inputs.keys.zip insR) et = [])
      ∧ List.Rel₂
          (fun p pt =>
            pt.1 = p.md
              ∧ ThreadedPosition C Env positions.env σ (func.inputs.keys.zip insR)
                  (skolemizeBody (some func.name.name) σ p.expr) LMonoTy.bool pt.2)
          func.preconditions positions.preconditions
      ∧ List.Rel₂
          (fun ax axT =>
            ThreadedPosition C Env positions.env σ (func.inputs.keys.zip insR)
              (skolemizeBody (some func.name.name) σ ax) LMonoTy.bool axT)
          func.axioms positions.axioms
      ∧ (∀ et, positions.body = some et → ∃ body, func.body = some body
          ∧ ThreadedPosition C Env positions.env σ (func.inputs.keys.zip insR)
              (skolemizeBody self σ body)
              (skolemizeTy σ outR) et)
      ∧ (∀ et, positions.measure = some et → ∃ m, func.measure = some m
          ∧ ThreadedPosition C Env positions.env σ (func.inputs.keys.zip insR)
              (skolemizeBody self σ m)
              (skolemizeTy σ (Function.measureTy C (func.inputs.keys.zip insR) m)) et
          ∧ Function.nonInputVars (func.inputs.keys.zip insR) et = []) := by
  obtain ⟨Ebody, Emeasure, Epre, hbody, hmeasure, hpre, hax⟩ := checkPositions_inv h
  have hb := optPosition_trace (checkBody_inv hbody) (fun _ _ => hground) henv hnud hfac
  have hm := optPosition_trace (checkMeasure_inv hmeasure)
    (fun m _ => Function.freeVars_skolemizeTy_measureTy C _ σ m hnud) hb.2.1 hnud hfac
  have hp := (checkPreconditions_boolWalk C func.name.name σ _).trace hnud hfac
    func.preconditions Emeasure Epre positions.preconditions hpre hm.2.1
  have ha := (checkAxioms_boolWalk C func.name.name σ _).trace hnud hfac
    func.axioms Epre positions.env positions.axioms hax hp.2.1
  have habsBodyFinal :
      Subst.absorbs positions.env.stateSubstInfo.subst Ebody.stateSubstInfo.subst :=
    Subst.absorbs_trans _ _ _ hm.2.2.1
      (Subst.absorbs_trans _ _ _ hp.2.2.1 ha.2.2.1)
  have habsMeasureFinal :
      Subst.absorbs positions.env.stateSubstInfo.subst Emeasure.stateSubstInfo.subst :=
    Subst.absorbs_trans _ _ _ hp.2.2.1 ha.2.2.1
  refine ⟨ha.1.trans (hp.1.trans (hm.1.trans hb.1)), ha.2.1,
    Subst.absorbs_trans _ _ _ hb.2.2.1
      (Subst.absorbs_trans _ _ _ hm.2.2.1
        (Subst.absorbs_trans _ _ _ hp.2.2.1 ha.2.2.1)),
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro body hbodyMem
    obtain ⟨et, hbodyEq, hpos, -⟩ := hb.2.2.2.1 body hbodyMem
    exact ⟨et, hbodyEq, ThreadedPosition.transfer
      (C := C) (EnvBase := Env) (EnvMid := Ebody) (EnvBase' := Env)
      (EnvFinal := positions.env) hpos rfl habsBodyFinal⟩
  · intro m hmeasureMem
    obtain ⟨et, hmeasureEq, hthread, hclosed⟩ := hm.2.2.2.1 m hmeasureMem
    exact ⟨et, hmeasureEq,
      ThreadedPosition.transfer
        (C := C) (EnvBase := Ebody) (EnvMid := Emeasure) (EnvBase' := Env)
        (EnvFinal := positions.env) hthread hb.1 habsMeasureFinal, hclosed⟩
  · refine List.Rel₂.imp (fun p pt hpt => ?_) hp.2.2.2
    obtain ⟨et, rfl, hthread⟩ := hpt
    exact ⟨rfl, ThreadedPosition.transfer
      (C := C) (EnvBase := Emeasure) (EnvMid := Epre) (EnvBase' := Env)
      (EnvFinal := positions.env) hthread (hm.1.trans hb.1) ha.2.2.1⟩
  · refine List.Rel₂.imp (fun ax axT hat => ?_) ha.2.2.2
    obtain ⟨et, rfl, hthread⟩ := hat
    exact ThreadedPosition.transfer
      (C := C) (EnvBase := Epre) (EnvMid := positions.env) (EnvBase' := Env)
      (EnvFinal := positions.env) hthread (hp.1.trans (hm.1.trans hb.1))
      (Subst.absorbs_refl _ positions.env.stateSubstInfo.isWF)
  · intro et het
    obtain ⟨body, hbody, hthread, -⟩ := hb.2.2.2.2 et het
    exact ⟨body, hbody, ThreadedPosition.transfer
      (C := C) (EnvBase := Env) (EnvMid := Ebody) (EnvBase' := Env)
      (EnvFinal := positions.env) hthread rfl habsBodyFinal⟩
  · intro et het
    obtain ⟨m, hmSource, hthread, hclosed⟩ := hm.2.2.2.2 et het
    exact ⟨m, hmSource, ThreadedPosition.transfer
      (C := C) (EnvBase := Ebody) (EnvMid := Emeasure) (EnvBase' := Env)
      (EnvFinal := positions.env) hthread hb.1 habsMeasureFinal, hclosed⟩

/-- Each precondition expression of a function is among the expressions the function carries. -/
private theorem precondition_expr_mem_func_exprs {IdentT ExprT TyT MetadataT : Type}
    {f : Strata.DL.Util.Func IdentT ExprT TyT MetadataT}
    {p : Strata.DL.Util.FuncPrecondition ExprT MetadataT} (hp : p ∈ f.preconditions) :
    p.expr ∈ f.exprs := by
  simp only [Strata.DL.Util.Func.exprs, List.mem_append, List.mem_map]
  exact Or.inl (Or.inr ⟨p, hp, rfl⟩)

/-- Each axiom of a function is among the expressions the function carries. -/
private theorem axiom_mem_func_exprs {IdentT ExprT TyT MetadataT : Type}
    {f : Strata.DL.Util.Func IdentT ExprT TyT MetadataT} {ax : ExprT} (hax : ax ∈ f.axioms) :
    ax ∈ f.exprs := by
  simp only [Strata.DL.Util.Func.exprs, List.mem_append]
  exact Or.inl (Or.inl (Or.inr hax))

/-- A property that every run of one of the function's positions preserves holds after a
    successful position walk if it held before. -/
private theorem checkPositions_preserves_src {self : Option String}
    {C : Expression.TyContext} {Env : Expression.TyEnv} {func : Function}
    {outR : LMonoTy} {insR : LMonoTys} {σ : RigidNames}
    {positions : Function.CheckedPositions}
    (P : Expression.TyEnv → Prop)
    (hP : ∀ (self : Option String) E e0 mty et E', P E → e0 ∈ func.exprs
      → (mty = skolemizeTy σ outR
          ∨ mty = skolemizeTy σ (Function.measureTy C (func.inputs.keys.zip insR) e0)
          ∨ mty = LMonoTy.bool)
      → PositionRun C E σ (func.inputs.keys.zip insR) (skolemizeBody self σ e0)
          mty et E' → P E')
    (h : Function.checkPositions self C Env func outR insR σ = .ok positions)
    (h0 : P Env) :
    P positions.env := by
  obtain ⟨Ebody, Emeasure, Epre, hbody, hmeasure, hpre, hax⟩ := checkPositions_inv h
  have hPbody : P Ebody := by
    rcases checkBody_inv hbody with ⟨-, -, rfl⟩ | ⟨body, _, hb, -, hrun, -⟩
    · exact h0
    · refine hP _ _ _ _ _ _ h0 ?_ (Or.inl rfl) hrun
      simp only [Strata.DL.Util.Func.exprs, hb, Option.toList_some, List.append_assoc,
        List.cons_append, List.mem_cons, true_or]
  have hPmeasure : P Emeasure := by
    rcases checkMeasure_inv hmeasure with ⟨-, -, rfl⟩ | ⟨m, _, hm, -, hrun, -⟩
    · exact hPbody
    · refine hP _ _ _ _ _ _ hPbody ?_ (Or.inr (Or.inl rfl)) hrun
      simp only [Strata.DL.Util.Func.exprs, hm, Option.toList_some, List.mem_append,
        List.mem_singleton, or_true]
  exact (checkAxioms_boolWalk C func.name.name σ _).preserves P func.axioms
    (fun E ax et E' hE hax hr =>
      hP _ E ax _ et E' hE (axiom_mem_func_exprs hax) (Or.inr (Or.inr rfl)) hr)
    Epre positions.env _ hax
    ((checkPreconditions_boolWalk C func.name.name σ _).preserves P func.preconditions
      (fun E p et E' hE hp hr =>
        hP _ E p.expr _ et E' hE (precondition_expr_mem_func_exprs hp) (Or.inr (Or.inr rfl)) hr)
      Emeasure Epre _ hpre hPmeasure)

/-! ### Registered substitution ranges through the position walk -/

/-- Resolving one position and closing the formals scope keeps the substitution range registered
    when the expected type, function arrows, Booleans and literal types are registered. -/
private theorem closeFormals_RangeKnown
    (C : Expression.TyContext) (Env EnvR : Expression.TyEnv)
    (σ : RigidNames) (sig : @LMonoTySignature Unit)
    (e : Expression.Expr) (et : LExprT CoreLParams.mono) (mty : LMonoTy)
    (hres : resolveWithType C (Function.formalsEnv Env σ sig) e mty = .ok (et, EnvR))
    (henv : LExpr.TEnvWF (T := CoreLParams) Env)
    (hnud : ∀ v ∈ LMonoTys.freeVars sig.values, v ∈ σ.map Prod.fst)
    (hfac : FactorySigWF C.functions)
    (harrow : C.knownTypes["arrow"]? = some 2) (hbool : C.knownTypes["bool"]? = some 0)
    (hlit : LExpr.LiteralTysKnown C)
    (hmty : LMonoTy.knownInstance mty C.knownTypes = true)
    (hrange : Subst.RangeKnown Env.stateSubstInfo.subst C.knownTypes) :
    Subst.RangeKnown (Function.closeFormals Env EnvR).stateSubstInfo.subst C.knownTypes := by
  have hformals : LExpr.TEnvWF (T := CoreLParams) (Function.formalsEnv Env σ sig) :=
    formalsEnv_TEnvWF Env σ sig henv hnud
  have hrange' : Subst.RangeKnown (Function.formalsEnv Env σ sig).stateSubstInfo.subst
      C.knownTypes := by
    simpa only [Function.formalsEnv, skolemScope, TEnv.pushEmptyContext, TEnv.addInNewestContext,
      TEnv.updateContext] using hrange
  have hR := resolveWithType_RangeKnown C _ EnvR e et mty hres hformals hfac harrow hbool hlit
    hmty hrange'
  simpa only [Function.closeFormals, TEnv.updateContext] using hR

/-- The complete position walk keeps the substitution range registered when function arrows,
    Booleans, literal types, integers, and the skolemized signature types are registered. -/
private theorem checkPositions_RangeKnown {self : Option String}
    (C : Expression.TyContext) (Env : Expression.TyEnv) (func : Function)
    (outR : LMonoTy) (insR : LMonoTys) (σ : RigidNames)
    (positions : Function.CheckedPositions)
    (h : Function.checkPositions self C Env func outR insR σ = .ok positions)
    (henv : LExpr.TEnvWF (T := CoreLParams) Env)
    (hnud : ∀ v ∈ LMonoTys.freeVars (ListMap.values (func.inputs.keys.zip insR)),
      v ∈ σ.map Prod.fst)
    (hground : LMonoTy.freeVars (skolemizeTy σ outR) = [])
    (hfac : FactorySigWF C.functions)
    (harrow : C.knownTypes["arrow"]? = some 2) (hbool : C.knownTypes["bool"]? = some 0)
    (hlit : LExpr.LiteralTysKnown C)
    (hint : LMonoTy.knownInstance LMonoTy.int C.knownTypes = true)
    (hboolK : LMonoTy.knownInstance LMonoTy.bool C.knownTypes = true)
    (hout : LMonoTy.knownInstance (skolemizeTy σ outR) C.knownTypes = true)
    (hins : ∀ ty ∈ ListMap.values (func.inputs.keys.zip insR),
      LMonoTy.knownInstance (skolemizeTy σ ty) C.knownTypes = true)
    (hrange : Subst.RangeKnown Env.stateSubstInfo.subst C.knownTypes) :
    Subst.RangeKnown positions.env.stateSubstInfo.subst C.knownTypes := by
  have hstep : ∀ (self : Option String) E e0 mty et E',
      (LExpr.TEnvWF (T := CoreLParams) E ∧ Subst.RangeKnown E.stateSubstInfo.subst C.knownTypes)
      → (mty = skolemizeTy σ outR
          ∨ mty = skolemizeTy σ (Function.measureTy C (func.inputs.keys.zip insR) e0)
          ∨ mty = LMonoTy.bool)
      → PositionRun C E σ (func.inputs.keys.zip insR) (skolemizeBody self σ e0)
          mty et E'
      → LExpr.TEnvWF (T := CoreLParams) E'
          ∧ Subst.RangeKnown E'.stateSubstInfo.subst C.knownTypes := by
    intro self E e0 mty et E' hE hmty hrun
    have hgroundMty : LMonoTy.freeVars mty = [] := by
      rcases hmty with rfl | rfl | rfl
      · exact hground
      · exact Function.freeVars_skolemizeTy_measureTy C _ σ e0 hnud
      · rfl
    have hknownMty : LMonoTy.knownInstance mty C.knownTypes = true := by
      rcases hmty with rfl | rfl | rfl
      · exact hout
      · rcases Function.measureTy_int_or_mem C (func.inputs.keys.zip insR) e0 with hmint | hmem
        · rw [hmint, skolemizeTy_int]
          exact hint
        · exact hins _ hmem
      · exact hboolK
    have hwf := (hrun.threaded hgroundMty hE.1 hnud hfac).2.1
    obtain ⟨EnvR, hres, rfl⟩ := hrun
    exact ⟨hwf, closeFormals_RangeKnown C E EnvR σ _ _ et mty hres hE.1 hnud hfac harrow hbool
      hlit hknownMty hE.2⟩
  exact (checkPositions_preserves_src _
    (fun self E e0 mty et E' hE _ hmty hr => hstep self E e0 mty et E' hE hmty hr) h
    ⟨henv, hrange⟩).2

/-! ### The stored form of a checked position -/

/-- `stored` is what the checker keeps at a position resolved against `mty` in `Env0`: the
    elaboration under a substitution `S` absorbing the resolver's, with rigid constants mapped back
    to variables. -/
private def StoredElabAt (C : Expression.TyContext) (Env0 : Expression.TyEnv)
    (σ : RigidNames) (S : Subst) (mty : LMonoTy) (stored : Expression.Expr) : Prop :=
  ∃ (e0 : Expression.Expr) (et : LExprT CoreLParams.mono) (EnvR : Expression.TyEnv),
    resolveWithType (addSkolemTypes C σ) Env0 e0 mty = .ok (et, EnvR)
    ∧ Subst.absorbs S EnvR.stateSubstInfo.subst
    ∧ stored = finishDeskolemized σ S et
    ∧ ConstTysFixed σ (LExpr.unresolved (LExpr.applySubstT et S))

/-- A position stored under `S`, resolved from a well-formed state with `EnvBase`'s context in a
    well-formed formals environment. -/
private def StoredPositionAt
    (C : Expression.TyContext) (EnvBase : Expression.TyEnv) (σ : RigidNames) (S : Subst)
    (sig : @LMonoTySignature Unit) (mty : LMonoTy) (stored : Expression.Expr) : Prop :=
  ∃ EnvStart,
    EnvStart.context = EnvBase.context
      ∧ LExpr.TEnvWF (T := CoreLParams) EnvStart
      ∧ LExpr.TEnvWF (T := CoreLParams) (Function.formalsEnv EnvStart σ sig)
      ∧ StoredElabAt C (Function.formalsEnv EnvStart σ sig) σ S mty stored

/-- A position stored under some substitution, with `EnvBase`'s aliases resolved. -/
private def StoredPosition
    (C : Expression.TyContext) (EnvBase : Expression.TyEnv) (σ : RigidNames)
    (sig : @LMonoTySignature Unit) (mty : LMonoTy) (stored : Expression.Expr) : Prop :=
  Lambda.TContext.AliasesResolved EnvBase.context
    ∧ ∃ S, StoredPositionAt C EnvBase σ S sig mty stored

/-- Materializing a threaded position under a substitution `S` yields a `StoredPositionAt` at
    `S`, when `S` absorbs every substitution the walk's final substitution absorbs. -/
private theorem StoredPositionAt.of_threaded (S : Subst)
    (hthread : ThreadedPosition (addSkolemTypes C σ) EnvBase EnvFinal σ sig e mty et)
    (hS : ∀ X, Subst.absorbs EnvFinal.stateSubstInfo.subst X → Subst.absorbs S X)
    (hnud : ∀ v ∈ LMonoTys.freeVars sig.values, v ∈ σ.map Prod.fst)
    (hstored : stored = finishDeskolemized σ S et)
    (hlits : ConstTysFixed σ e) :
    StoredPositionAt C EnvBase σ S sig mty stored := by
  obtain ⟨EnvStart, EnvNext, hctx, hwf, ⟨EnvR, hres, hnext⟩, habs⟩ := hthread
  have habsRaw :
      Subst.absorbs EnvFinal.stateSubstInfo.subst EnvR.stateSubstInfo.subst := by
    rw [hnext] at habs
    simpa only [Function.closeFormals, TEnv.updateContext] using habs
  have hwfF := formalsEnv_TEnvWF EnvStart σ sig hwf hnud
  exact ⟨EnvStart, hctx, hwf, hwfF, e, et, EnvR, hres, hS _ habsRaw, hstored,
    ConstTysFixed_resolveWithType (addSkolemTypes C σ) _ EnvR e et mty hres S hlits⟩

/-- Forgetting the exposed materializing substitution recovers an ordinary stored position. -/
private theorem StoredPositionAt.toStored
    (h : StoredPositionAt C EnvBase σ S sig mty stored)
    (hresolved : Lambda.TContext.AliasesResolved EnvBase.context) :
    StoredPosition C EnvBase σ sig mty stored :=
  ⟨hresolved, S, h⟩

/-! ### The measure obligation -/

/-- The measure obligation of the typechecker spec for functions holds of `m` when `m` has the
    type it is checked at, a bare `m` names a formal of `inputs`, and each formal's type in `sig`
    is related by `R` to its type in `inputs`. -/
private theorem measureObligation_of_measureTy
    {C : Expression.TyContext} {sig inputs : @LMonoTySignature Unit}
    {R : LMonoTy → LMonoTy → Prop} {T : LMonoTy → Prop} {m : Expression.Expr} :
    (∀ x ty', sig.find? x = some ty' → ∃ ty, inputs.find? x = some ty ∧ R ty ty') →
    (∀ md x ann, m = .fvar md x ann → x ∈ inputs.keys) →
    T (Function.measureTy C sig m) →
    match m with
    | .fvar _ x _ => ∃ ty, inputs.find? x = some ty ∧
        (T .int ∨ ∃ n args, R ty (.tcons n args) ∧ (C.datatypes.getType n).isSome ∧
          T (.tcons n args))
    | _ => T .int := by
  intro hrel hkey htyped
  cases m
  case fvar md x ann =>
    have hint : T .int → ∃ ty, inputs.find? x = some ty ∧
        (T .int ∨ ∃ n args, R ty (.tcons n args) ∧ (C.datatypes.getType n).isSome ∧
          T (.tcons n args)) := by
      intro hT
      obtain ⟨ty, hty⟩ := Option.ne_none_iff_exists'.mp
        (fun hnone => ListMap.find?_of_not_mem_values inputs hnone (hkey md x ann rfl))
      exact ⟨ty, hty, Or.inl hT⟩
    simp only [Function.measureTy] at htyped
    split at htyped
    · rename_i n args hfind
      split at htyped
      · rename_i hdt
        obtain ⟨ty, hty, hR⟩ := hrel x _ hfind
        exact ⟨ty, hty, Or.inr ⟨n, args, hR, hdt, htyped⟩⟩
      · exact hint htyped
    · exact hint htyped
  all_goals exact htyped

/-! ### Input typing at all four positions -/

/-- With `sc` holding every type name in scope and `tn ()` holding every type name the function
    mentions, each expression position of a checked function has its expected type in
    `funcContext`; a bare-variable measure is a formal, at `int` or at a registered datatype
    alias-equivalent to its declared type. -/
private theorem Function.Checked.inputTyped
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv) (func func' : Function)
    (h : Function.Checked sc tn C Env Env' func func')
    (hcov : ∀ n ∈ scopeTyNames C Env, n ∈ sc.get)
    (htn : ∀ n ∈ func.tyNames func.annotTys, n ∈ tn ())
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env) (h_fac : FactorySigWF C.functions)
    (h_closed : LExpr.checkContextTypesClosed (T := CoreLParams) Env)
    (h_mono : MonoScope Env.context) :
    (∀ body, func.body = some body →
        LExpr.HasType C (funcContext Env.context func) body (.forAll [] func.output))
    ∧ (∀ m, func.measure = some m →
        match m with
        | .fvar _ x _ => ∃ ty, func.inputs.find? x = some ty ∧
            (LExpr.HasType C (funcContext Env.context func) m (.forAll [] .int) ∨
              ∃ n args, AliasEquiv Env.context.aliases ty (.tcons n args)
                ∧ (C.datatypes.getType n).isSome
                ∧ LExpr.HasType C (funcContext Env.context func) m (.forAll [] (.tcons n args)))
        | _ => LExpr.HasType C (funcContext Env.context func) m (.forAll [] .int))
    ∧ (∀ p ∈ func.preconditions,
        LExpr.HasType C (funcContext Env.context func) p.expr (.forAll [] .bool))
    ∧ (∀ ax ∈ func.axioms,
        LExpr.HasType C (funcContext Env.context func) ax (.forAll [] .bool)) := by
  have hsr := Function.rigidNames_spec sc C Env func tn hcov
  have hpfx := hsr.prefixed
  have hnd := hsr.nodup
  obtain ⟨outR, insR, positions, run⟩ := h.run
  have hoe : AliasEquiv Env.context.aliases func.output outR := run.resolvedSig.2.2
  have h_aw : Lambda.TContext.AliasesWF Env.context := h_env.aliasesWF
  have h_amb := hsr.noSkolemAmbient
  obtain ⟨hkeys, hvals, -⟩ := run.resolvedSig
  obtain ⟨hnudSig, -, hgroundOut, hrtOut, hrtSig⟩ := run.signature h_aw
  have haeList : AliasEquivList Env.context.aliases func.inputs.values insR :=
    AliasEquivList.of_forall₂ (fun _ _ hr => hr.1) run.insResolved
  have hfacSk := FactorySigWF.addSkolemTypes C (Function.rigidNames sc C func tn) h_fac
  have htrace := checkPositions_trace
    (addSkolemTypes C (Function.rigidNames sc C func tn)) Env func outR insR
    (Function.rigidNames sc C func tn) positions run.positionsOk.choose_spec h_env hnudSig
    hgroundOut hfacSk
  have hall := Function.rigidNames_annots sc C func tn htn
  have hlits := Function.rigidNames_consts sc C func tn htn
  have hexprs : func.exprs = func.body.toList ++ func.axioms
      ++ func.preconditions.map (fun p => p.expr) ++ func.measure.toList := rfl
  have hscope : ∀ (e : Expression.Expr) (mty : LMonoTy),
      LExpr.HasType (T := CoreLParams) C
        { Env.context with
          types := Env.context.types.push (formalsScope (func.inputs.keys.zip insR)) }
        e (.forAll [] mty) →
      LExpr.HasType (T := CoreLParams) C (funcContext Env.context func) e (.forAll [] mty) := by
    intro e mty hh
    have haeInputs : AliasEquivList Env.context.aliases func.inputs.values
        (ListMap.values (func.inputs.keys.zip insR)) := by
      rw [hvals]
      exact haeList
    exact LExpr.HasType_pushScope_aliasEquiv C Env.context func.inputs
      (func.inputs.keys.zip insR) e mty h_aw hkeys.symm haeInputs hh
  have hpos : ∀ (self : Option String) (e : Expression.Expr) (mty : LMonoTy)
      (eT : LExprT CoreLParams.mono),
      e ∈ func.exprs → LMonoTy.freeVars mty = [] →
      ThreadedPosition (addSkolemTypes C (Function.rigidNames sc C func tn)) Env positions.env
        (Function.rigidNames sc C func tn) (func.inputs.keys.zip insR)
        (skolemizeBody self (Function.rigidNames sc C func tn) e) mty eT →
      LExpr.HasType (T := CoreLParams) C (funcContext Env.context func) e
        (.forAll [] (deskolemizeTy (Function.rigidNames sc C func tn) mty)) := by
    intro self e mty eT hmem hground hthread
    obtain ⟨Estart, Enext, hctx, hwf, ⟨eE, hres, -⟩, -⟩ := hthread
    have hws := resolveWithType_WellScoped _ _ _ _ _ _ hres
    have hclosedStart : LExpr.checkContextTypesClosed (T := CoreLParams) Estart := by
      rw [LExpr.checkContextTypesClosed_of_context_eq (T := CoreLParams) Estart Env hctx]
      exact h_closed
    have hht := funcPosition_HasType C Estart eE (Function.rigidNames sc C func tn) hpfx hnd
      self (func.inputs.keys.zip insR) e mty eT hres hws hwf
      hclosedStart h_fac (by simpa only [hctx] using h_amb)
      (by simpa only [hctx] using h_mono) hnudSig hrtSig (hall e hmem) (hlits e hmem) hground
    rw [hctx] at hht
    exact hscope e _ hht
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro body hbody
    obtain ⟨bT, -, hthread⟩ := htrace.2.2.2.1 body hbody
    have hmem : body ∈ func.exprs := by rw [hexprs, hbody]; simp
    have hht := hpos _ body _ bT hmem hgroundOut hthread
    rw [hrtOut] at hht
    exact LExpr.HasType.talias (T := CoreLParams) _ body outR func.output
      (LExpr.AliasEquiv.symm hoe) hht
  · intro m hm
    obtain ⟨mT, -, hthread, hclosed⟩ := htrace.2.2.2.2.1 m hm
    rw [Function.measureTy_addSkolemTypes] at hthread
    have hmem : m ∈ func.exprs := by rw [hexprs, hm]; simp
    have htyped := hpos _ m _ mT hmem
      (Function.freeVars_skolemizeTy_measureTy C _ _ m hnudSig) hthread
    rw [Function.deskolemizeTy_skolemizeTy_measureTy C _ m hpfx hrtSig] at htyped
    have hkey : ∀ md x ann, m = .fvar md x ann → x ∈ func.inputs.keys := by
      intro md x ann hfv
      subst hfv
      have hx := (ThreadedPosition.fvar_mem_keys hthread hclosed).1
      rwa [hkeys] at hx
    exact measureObligation_of_measureTy
      (T := fun ty => LExpr.HasType C (funcContext Env.context func) m (.forAll [] ty))
      (ListMap.find?_zip_of_rel₂ func.inputs insR (run.insResolved.imp fun _ _ hr => hr.1)) hkey
      htyped
  · intro p hp
    obtain ⟨pt, -, -, hthread⟩ := List.Rel₂.exists_of_mem_left htrace.2.2.2.2.2.1 hp
    simpa only [deskolemizeTy_bool hpfx] using
      hpos _ p.expr LMonoTy.bool pt.2 (precondition_expr_mem_func_exprs hp) rfl hthread
  · intro ax hax
    obtain ⟨aT, -, hthread⟩ := List.Rel₂.exists_of_mem_left htrace.2.2.2.2.2.2.1 hax
    simpa only [deskolemizeTy_bool hpfx] using
      hpos _ ax LMonoTy.bool aT (axiom_mem_func_exprs hax) rfl hthread

/-! ## Facts about the input function from a successful check -/

/-- Every type parameter of a function the checker accepts occurs in its declared signature, given
    well-formed type aliases. -/
private theorem Function.Checked.typeArgsInSignature_input
    (h : Function.Checked sc tn C Env Env' func func')
    (h_aw : TContext.AliasesWF Env.context) :
    ∀ ta ∈ func.typeArgs,
      ta ∈ LMonoTy.freeVars (LMonoTy.mkArrow' func.output func.inputs.values) := by
  obtain ⟨outR, insR, hOutFree, hInsFree, hOutEq, hInEq, hTaEq, hSig⟩ :=
    Function.Checked.elaborated_shape C Env Env' func func' h h_aw
  intro ta hta
  rcases freeVars_mkArrow'_cases func'.output ta func'.inputs.values (hSig ta (hTaEq ▸ hta))
    with hout | ⟨ty, hty, hvty⟩
  · rw [hOutEq] at hout
    exact mem_freeVars_mkArrow'_output func.output ta func.inputs.values (hOutFree ta hout)
  · obtain ⟨k, hk⟩ := ListMap.mem_values _ ty (hInEq ▸ hty)
    exact hInsFree ty (List.of_mem_zip hk).2 ta hvty

/-- With no type alias in scope, every input and output type of the renaming of the reserved
    type parameters that `Function.typeCheckIn` returns is a registered instance. -/
theorem Function.typeCheckIn_declaredSigKnown_of_aliases_nil
    {scope : Thunk (Std.HashSet String)}
    (h : Function.typeCheckIn scope C Env func = .ok (renamed, func'))
    (h_nil : Env.context.aliases = []) :
    ∀ ty ∈ renamed.output :: renamed.inputs.values,
      LMonoTy.knownInstance ty C.knownTypes = true := by
  obtain ⟨rfl, _, hc⟩ := Function.typeCheckIn_checked h
  obtain ⟨outR, insR, _, run⟩ := hc.run
  intro ty hty
  rcases List.mem_cons.mp hty with rfl | hin
  · have hequiv := run.resolvedSig.2.2
    rw [h_nil] at hequiv
    rw [AliasEquiv.eq_of_nil hequiv]
    exact run.outKnown
  · obtain ⟨r, -, hequiv, hknown⟩ := List.Rel₂.exists_of_mem_left run.insResolved hin
    rw [h_nil] at hequiv
    rw [AliasEquiv.eq_of_nil hequiv]
    exact hknown

/-! ## The elaborated signature and stored expressions of a successful check -/

/-- An expression stored at a checked position with a ground expected type is annotated-typed,
    with no binders in scope, at that type's deskolemization. -/
private theorem HasTypeA_of_StoredPosition {C : Expression.TyContext}
    {EnvBase : Expression.TyEnv} {σ : RigidNames} {sig : @LMonoTySignature Unit} {mty : LMonoTy}
    {stored : Expression.Expr} (hpfx : RigidNamesPrefixed σ)
    (h_stored : StoredPosition C EnvBase σ sig mty stored)
    (h_ground : LMonoTy.freeVars mty = [])
    (h_fac : FactorySigWF C.functions) :
    LExpr.HasTypeA (T := CoreLParams) [] stored (deskolemizeTy σ mty) := by
  obtain ⟨hresolved, S, EnvStart, hctx, -, h_wf, e0, et, EnvR, hres, habs, hst, hlits⟩ :=
    h_stored
  have h_res := formalsEnv_AliasesResolved EnvStart σ sig (hctx ▸ hresolved)
  have hfac' := FactorySigWF.addSkolemTypes C σ h_fac
  have hA := resolveWithType_HasTypeA_ground_absorbing
    (addSkolemTypes C σ) (Function.formalsEnv EnvStart σ sig) EnvR e0 et mty hres h_ground h_wf
    hfac' h_res S habs
  have hD := HasTypeA_replaceUserProvidedType_deskolemizeTy hpfx []
    (LExpr.unresolved (LExpr.applySubstT et S)) mty hlits hA
  rw [hst]
  simpa only [List.map_nil] using hD

/-- An expression stored at a checked `bool` position is annotated-typed at `bool`, with no
    binders in scope. -/
private theorem HasTypeA_bool_of_StoredPosition {C : Expression.TyContext}
    {EnvBase : Expression.TyEnv} {σ : RigidNames} {sig : @LMonoTySignature Unit}
    {stored : Expression.Expr} (hpfx : RigidNamesPrefixed σ)
    (h_stored : StoredPosition C EnvBase σ sig .bool stored)
    (h_fac : FactorySigWF C.functions) :
    LExpr.HasTypeA (T := CoreLParams) [] stored .bool := by
  have hA := HasTypeA_of_StoredPosition hpfx h_stored rfl h_fac
  rwa [deskolemizeTy_bool hpfx] at hA

/-- After a successful core run, resolved inputs are alias-free under resolved aliases, every
    stored expression is its position's stored form, and a bare stored measure names a formal. -/
private theorem Function.checkedRun_storedPositionsAt
    {C : Expression.TyContext} {Env EnvCore : Expression.TyEnv} {func func' : Function}
    {outR : LMonoTy} {insR : LMonoTys} {positions : Function.CheckedPositions}
    (run : Function.CoreRun sc tn C Env EnvCore func func' outR insR positions)
    (htn : ∀ n ∈ func.tyNames func.annotTys, n ∈ tn ())
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env)
    (h_fac : FactorySigWF C.functions) :
    (Lambda.TContext.AliasesResolved Env.context →
          ∀ t ∈ insR, LMonoTy.aliasFree Env.context.aliases t)
      ∧ (∀ body, func'.body = some body →
            StoredPositionAt C Env (Function.rigidNames sc C func tn)
              EnvCore.stateSubstInfo.subst
              (func.inputs.keys.zip insR)
              (skolemizeTy (Function.rigidNames sc C func tn) outR) body)
      ∧ (∀ m, func'.measure = some m →
            (∀ md x ann, m = .fvar md x ann → x ∈ func.inputs.keys)
            ∧ StoredPositionAt C Env (Function.rigidNames sc C func tn)
                EnvCore.stateSubstInfo.subst (func.inputs.keys.zip insR)
                (skolemizeTy (Function.rigidNames sc C func tn)
                  (Function.measureTy C (func.inputs.keys.zip insR) m)) m)
      ∧ (∀ p ∈ func'.preconditions,
          StoredPositionAt C Env (Function.rigidNames sc C func tn)
            EnvCore.stateSubstInfo.subst
            (func.inputs.keys.zip insR) LMonoTy.bool p.expr)
      ∧ (∀ ax ∈ func'.axioms,
          StoredPositionAt C Env (Function.rigidNames sc C func tn)
            EnvCore.stateSubstInfo.subst
            (func.inputs.keys.zip insR) LMonoTy.bool ax) := by
  have hAf : Lambda.TContext.AliasesResolved Env.context →
      ∀ t ∈ insR, LMonoTy.aliasFree Env.context.aliases t := by
    intro h_resolved t ht
    obtain ⟨ty, -, hra⟩ := forall2_exists_left run.insResolveEach t ht
    exact Lambda.resolveAliases_output_aliasFree (T := CoreLParams) ty Env t Env hra h_resolved
  have hzipKeys := run.resolvedSig.1
  obtain ⟨hnudSig, -, hground, -⟩ := run.signature h_env.aliasesWF
  have htrace := checkPositions_trace
    (addSkolemTypes C (Function.rigidNames sc C func tn)) Env func outR insR
    (Function.rigidNames sc C func tn) positions run.positionsOk.choose_spec h_env hnudSig hground
    (FactorySigWF.addSkolemTypes C (Function.rigidNames sc C func tn) h_fac)
  have hst := run.stored
  subst hst
  have hS : ∀ X, Subst.absorbs positions.env.stateSubstInfo.subst X →
      Subst.absorbs EnvCore.stateSubstInfo.subst X := by
    rw [run.envCore]
    exact fun X hX => hX
  have hlits := Function.rigidNames_consts sc C func tn htn
  have hexprs : func.exprs = func.body.toList ++ func.axioms
      ++ func.preconditions.map (fun p => p.expr) ++ func.measure.toList := rfl
  refine ⟨hAf, ?_, ?_, ?_, ?_⟩
  · intro body hbody
    obtain ⟨et, het, hstored⟩ := Option.map_eq_some_iff.mp hbody
    obtain ⟨body0, hb0, hthread⟩ := htrace.2.2.2.2.2.2.2.1 et het
    have hmem : body0 ∈ func.exprs := by rw [hexprs, hb0]; simp
    exact StoredPositionAt.of_threaded (C := C) (EnvBase := Env) _ hthread hS hnudSig
      hstored.symm (ConstTysFixed_skolemizeBody _ (hlits body0 hmem))
  · intro m hm
    obtain ⟨et, het, hstored⟩ := Option.map_eq_some_iff.mp hm
    obtain ⟨m0, hm0, hthread, hclosed⟩ := htrace.2.2.2.2.2.2.2.2 et het
    have hmem : m0 ∈ func.exprs := by rw [hexprs, hm0]; simp
    rw [Function.measureTy_addSkolemTypes] at hthread
    have hsame : Function.measureTy C (func.inputs.keys.zip insR) m
          = Function.measureTy C (func.inputs.keys.zip insR) m0
        ∧ ∀ md x ann, m = .fvar md x ann → x ∈ func.inputs.keys := by
      by_cases hfv : ∃ mid x ann, m0 = .fvar mid x ann
      · obtain ⟨mid, x, ann, rfl⟩ := hfv
        obtain ⟨hx, md, ty, rfl⟩ := ThreadedPosition.fvar_mem_keys hthread hclosed
        subst hstored
        rw [hzipKeys] at hx
        simp only [finishDeskolemized, LExpr.applySubstT, LExpr.replaceMetadata, LExpr.unresolved,
          LExpr.replaceUserProvidedType]
        refine ⟨rfl, ?_⟩
        intro md' x' ann' heq
        injection heq with _ hx'
        rw [← hx']
        exact hx
      have hnon : ∀ mid x ann, m0 ≠ .fvar mid x ann := fun mid x ann heq => hfv ⟨mid, x, ann, heq⟩
      rw [Function.measureTy_of_ne_fvar _ (func.inputs.keys.zip insR) m0 hnon,
        skolemizeTy_int] at hthread
      obtain ⟨Estart, Enext, hctx, hwf, ⟨EnvR, hres, hnext⟩, habs⟩ := hthread
      have hstoredNe : ∀ mid x ann,
          finishDeskolemized (Function.rigidNames sc C func tn) EnvCore.stateSubstInfo.subst et
            ≠ .fvar mid x ann :=
        resolveWithType_stored_ne_fvar_of_ne_fvar
          (addSkolemTypes C (Function.rigidNames sc C func tn))
          (Function.formalsEnv Estart (Function.rigidNames sc C func tn)
            (func.inputs.keys.zip insR))
          EnvR
          (skolemizeBody _ (Function.rigidNames sc C func tn) m0)
          LMonoTy.int et hres
          (skolemizeBody_ne_fvar _ _ m0 hnon)
          (Function.rigidNames sc C func tn) EnvCore.stateSubstInfo.subst
      have hmNe : ∀ mid x ann, m ≠ .fvar mid x ann := by
        intro mid x ann heq
        apply hstoredNe mid x ann
        exact hstored.trans heq
      rw [Function.measureTy_of_ne_fvar _ (func.inputs.keys.zip insR) m hmNe,
        Function.measureTy_of_ne_fvar _ (func.inputs.keys.zip insR) m0 hnon]
      exact ⟨rfl, fun md x ann heq => absurd heq (hmNe md x ann)⟩
    refine ⟨hsame.2, ?_⟩
    rw [hsame.1]
    exact StoredPositionAt.of_threaded (C := C) (EnvBase := Env) _ hthread hS hnudSig
      hstored.symm (ConstTysFixed_skolemizeBody _ (hlits m0 hmem))
  · intro p hp
    obtain ⟨pt, hpt, rfl⟩ := List.mem_map.mp hp
    obtain ⟨p0, hp0, hrel⟩ :=
      forall2_exists_left htrace.2.2.2.2.2.1 pt hpt
    have hmem : p0.expr ∈ func.exprs := by
      rw [hexprs]
      exact List.mem_append_left _ (List.mem_append_right _ (List.mem_map_of_mem hp0))
    exact StoredPositionAt.of_threaded (C := C) (EnvBase := Env) _ hrel.2 hS hnudSig rfl
      (ConstTysFixed_skolemizeBody _ (hlits p0.expr hmem))
  · intro ax hax
    obtain ⟨et, het, rfl⟩ := List.mem_map.mp hax
    obtain ⟨ax0, hax0, hthread⟩ :=
      forall2_exists_left htrace.2.2.2.2.2.2.1 et het
    have hmem : ax0 ∈ func.exprs := by
      rw [hexprs]
      exact List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hax0))
    exact StoredPositionAt.of_threaded (C := C) (EnvBase := Env) _ hthread hS hnudSig rfl
      (ConstTysFixed_skolemizeBody _ (hlits ax0 hmem))

/-- A successful function check gives the elaborated signature and the stored form of each checked
    position. -/
private theorem Function.Checked.storedPositions
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv) (func func' : Function)
    (h : Function.Checked sc tn C Env Env' func func')
    (htn : ∀ n ∈ func.tyNames func.annotTys, n ∈ tn ())
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env)
    (h_fac : FactorySigWF C.functions)
    (h_resolved : Lambda.TContext.AliasesResolved Env.context) :
    ∃ (outR : LMonoTy) (insR : LMonoTys),
      func'.output = outR
      ∧ func'.inputs = func.inputs.keys.zip insR
      ∧ func'.inputs.keys = func.inputs.keys
      ∧ LMonoTy.resolveAliases func.output Env = .ok (outR, Env)
      ∧ List.Rel₂ (fun ty ty' => AliasEquiv Env.context.aliases ty ty'
            ∧ isInstanceOfKnownType ty' C = true) func.inputs.values insR
      ∧ (∀ t ∈ insR, LMonoTy.aliasFree Env.context.aliases t)
      ∧ LMonoTy.freeVars (skolemizeTy (Function.rigidNames sc C func tn) outR) = []
      ∧ (∀ body, func'.body = some body →
            StoredPosition C Env (Function.rigidNames sc C func tn)
              (func.inputs.keys.zip insR)
              (skolemizeTy (Function.rigidNames sc C func tn) outR) body)
      ∧ (∀ m, func'.measure = some m →
            (∀ md x ann, m = .fvar md x ann → x ∈ func.inputs.keys)
            ∧ StoredPosition C Env (Function.rigidNames sc C func tn) (func.inputs.keys.zip insR)
                (skolemizeTy (Function.rigidNames sc C func tn)
                  (Function.measureTy C (func.inputs.keys.zip insR) m)) m)
      ∧ (∀ p ∈ func'.preconditions,
          StoredPosition C Env (Function.rigidNames sc C func tn)
            (func.inputs.keys.zip insR) LMonoTy.bool p.expr)
      ∧ (∀ ax ∈ func'.axioms,
          StoredPosition C Env (Function.rigidNames sc C func tn)
            (func.inputs.keys.zip insR) LMonoTy.bool ax) := by
  obtain ⟨outR, insR, _, run⟩ := h.run
  obtain ⟨hafCond, hbody, hmeasure, hpre, hax⟩ :=
    Function.checkedRun_storedPositionsAt run htn h_env h_fac
  have hzipKeys := run.resolvedSig.1
  obtain ⟨-, -, hground, -⟩ := run.signature h_env.aliasesWF
  have hout : func'.output = outR := by rw [run.stored]
  have hins : func'.inputs = func.inputs.keys.zip insR := by rw [run.stored]
  have hkeys : func'.inputs.keys = func.inputs.keys := by rw [hins, hzipKeys]
  refine ⟨outR, insR, hout, hins, hkeys, run.outResolved, run.insResolved,
    hafCond h_resolved, hground, ?_, ?_, ?_, ?_⟩
  · intro body hb
    exact (hbody body hb).toStored (hresolved := h_resolved)
  · intro m hm
    exact ⟨(hmeasure m hm).1, (hmeasure m hm).2.toStored (hresolved := h_resolved)⟩
  · intro p hp
    exact (hpre p hp).toStored (hresolved := h_resolved)
  · intro ax hax'
    exact (hax ax hax').toStored (hresolved := h_resolved)

/-! ## Facts about the elaborated function from a successful check -/

/-- Every free type variable of the elaborated signature is one of the elaborated function's type
    parameters, given well-formed type aliases. -/
private theorem Function.Checked.noUndeclaredVars_output
    (h : Function.Checked sc tn C Env Env' func func')
    (h_aw : TContext.AliasesWF Env.context) :
    ∀ v, v ∈ LMonoTy.freeVars (LMonoTy.mkArrow' func'.output func'.inputs.values) →
      v ∈ func'.typeArgs := by
  intro v hv
  have hwf := Function.Checked.lFuncWF C Env Env' func func' h h_aw
  rcases freeVars_mkArrow'_cases func'.output v func'.inputs.values hv with hout | ⟨ty, hty, hvty⟩
  · exact hwf.output_typevars_in_typeArgs hout
  · exact hwf.inputs_typevars_in_typeArgs ty hty hvty

/-- For any name sets, every input and output type of the signature `Function.typeCheckIn`
    elaborates is a registered instance. -/
theorem Function.typeCheckIn_signatureKnown_output {scope : Thunk (Std.HashSet String)}
    {C : Expression.TyContext} {Env : Expression.TyEnv} {func renamed func' : Function}
    (h : Function.typeCheckIn scope C Env func = .ok (renamed, func')) :
    ∀ ty ∈ func'.output :: func'.inputs.values,
      LMonoTy.knownInstance ty C.knownTypes = true := by
  obtain ⟨-, _, hc⟩ := Function.typeCheckIn_checked h
  obtain ⟨outR, insR, _, run⟩ := hc.run
  rw [run.stored]
  intro ty hty
  rcases List.mem_cons.mp hty with heq | hin
  · rw [heq]
    exact run.outKnown
  · obtain ⟨k, hk⟩ := ListMap.mem_values _ ty hin
    obtain ⟨_, -, -, hknown⟩ := forall2_exists_left run.insResolved ty (List.of_mem_zip hk).2
    exact hknown

/-- A successfully checked function's elaborated body is annotated-typed at its elaborated
    output type. -/
private theorem Function.Checked.bodyTyped_output
    (h : Function.Checked sc tn C Env Env' func func')
    (htn : ∀ n ∈ func.tyNames func.annotTys, n ∈ tn ())
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env) (h_fac : FactorySigWF C.functions)
    (h_resolved : TContext.AliasesResolved Env.context) :
    ∀ body, func'.body = some body → LExpr.HasTypeA [] body func'.output := by
  have hpfx := (Function.rigidNames_fresh sc C func tn).1
  have hnd := (Function.rigidNames_fresh sc C func tn).2.1
  obtain ⟨outR, _, houtEq, -, -, -, -, -, hground, hB, -, -, -⟩ :=
    Function.Checked.storedPositions C Env Env' func func' h htn h_env h_fac h_resolved
  intro body hbody
  have houtKnown : LMonoTy.knownInstance outR C.knownTypes = true := by
    rw [← houtEq]
    exact (Function.Checked.signatureTysKnown C Env Env' func func' h).2
  have hfix : deskolemizeTy (Function.rigidNames sc C func tn) outR = outR :=
    deskolemizeTy_eq_self_of_knownInstance C ((Function.rigidNames_fresh sc C func tn).2.2.1) outR
        houtKnown
  have hA := HasTypeA_of_StoredPosition hpfx (hB body hbody) hground h_fac
  rw [deskolemizeTy_skolemizeTy_eq_deskolemizeTy hnd, hfix] at hA
  rw [houtEq]
  exact hA

/-- A bare elaborated measure names a formal, and every elaborated measure is annotated-typed at
    the type it is checked at. -/
private theorem Function.Checked.measureTyped_output
    (h : Function.Checked sc tn C Env Env' func func')
    (htn : ∀ n ∈ func.tyNames func.annotTys, n ∈ tn ())
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env) (h_fac : FactorySigWF C.functions)
    (h_resolved : TContext.AliasesResolved Env.context) :
    ∀ m, func'.measure = some m →
      (∀ md x ann, m = .fvar md x ann → x ∈ func'.inputs.keys)
      ∧ LExpr.HasTypeA [] m (Function.measureTy C func'.inputs m) := by
  have hpfx := (Function.rigidNames_fresh sc C func tn).1
  obtain ⟨-, insR, -, hins, hkeys, -, -, -, -, -, hM, -, -⟩ :=
    Function.Checked.storedPositions C Env Env' func func' h htn h_env h_fac h_resolved
  obtain ⟨_, insRun, _, run⟩ := h.run
  obtain ⟨hnudSig, -, -, -, hrtSig⟩ := run.signature h_env.aliasesWF
  have hinsRun : func'.inputs = func.inputs.keys.zip insRun := by rw [run.stored]
  rw [← hinsRun] at hnudSig hrtSig
  intro m hm
  obtain ⟨hkey, hpos⟩ := hM m hm
  rw [← hins] at hpos
  have hA := HasTypeA_of_StoredPosition hpfx hpos
    (Function.freeVars_skolemizeTy_measureTy C _ _ m hnudSig) h_fac
  rw [Function.deskolemizeTy_skolemizeTy_measureTy C _ m hpfx hrtSig] at hA
  exact ⟨fun md x ann heq => hkeys ▸ hkey md x ann heq, hA⟩

/-- Each elaborated precondition is annotated-typed at `bool`. -/
private theorem Function.Checked.preconditionsTyped_output
    (h : Function.Checked sc tn C Env Env' func func')
    (htn : ∀ n ∈ func.tyNames func.annotTys, n ∈ tn ())
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env) (h_fac : FactorySigWF C.functions)
    (h_resolved : TContext.AliasesResolved Env.context) :
    ∀ p ∈ func'.preconditions, LExpr.HasTypeA [] p.expr .bool := by
  have hpfx := (Function.rigidNames_fresh sc C func tn).1
  obtain ⟨-, _, -, -, -, -, -, -, -, -, -, hP, -⟩ :=
    Function.Checked.storedPositions C Env Env' func func' h htn h_env h_fac h_resolved
  exact fun p hp => HasTypeA_bool_of_StoredPosition hpfx (hP p hp) h_fac

/-- Each elaborated axiom is annotated-typed at `bool`. -/
private theorem Function.Checked.axiomsTyped_output
    (h : Function.Checked sc tn C Env Env' func func')
    (htn : ∀ n ∈ func.tyNames func.annotTys, n ∈ tn ())
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env) (h_fac : FactorySigWF C.functions)
    (h_resolved : TContext.AliasesResolved Env.context) :
    ∀ ax ∈ func'.axioms, LExpr.HasTypeA [] ax .bool := by
  have hpfx := (Function.rigidNames_fresh sc C func tn).1
  obtain ⟨-, _, -, -, -, -, -, -, -, -, -, -, hA⟩ :=
    Function.Checked.storedPositions C Env Env' func func' h htn h_env h_fac h_resolved
  exact fun ax hax => HasTypeA_bool_of_StoredPosition hpfx (hA ax hax) h_fac

/-- Every type variable annotating an elaborated expression is a type parameter of the elaborated
    function. -/
private theorem Function.Checked.annotsScoped_output
    (h : Function.Checked sc tn C Env Env' func func') :
    ∀ e ∈ func'.exprs, ∀ v ∈ annotTyVars e, v ∈ func'.typeArgs := by
  obtain ⟨_, _, _, run⟩ := h.run
  exact run.annotsScoped

/-! ## Annotation agreement in the formals scope -/

/-- The substituted resolved formals environment deskolemizes to the declared formals scope over
    the deskolemized ambient scope, both with aliases `A`. -/
theorem formalsEnv_deskolemizes_substDeskolemizedAmbient
    (σ : RigidNames) (S : Subst) (Env : Expression.TyEnv) (sig : @LMonoTySignature Unit)
    (A : List TypeAlias)
    (h_sigFreeVars : ∀ v ∈ LMonoTys.freeVars sig.values, v ∈ σ.map Prod.fst)
    (h_rt : ∀ mty ∈ sig.values, deskolemizeTy σ (skolemizeTy σ mty) = mty)
    (h_res : ∀ mty ∈ sig.values, Env.context.resolveTy (skolemizeTy σ mty) = skolemizeTy σ mty) :
    DeskolemizesScope σ
      { TContext.subst (Function.formalsEnv Env σ sig).context.dealias S with aliases := A }
      { substDeskolemizedAmbient σ S Env.context with
          aliases := A,
          types :=
            (substDeskolemizedAmbient σ S Env.context).types.push (formalsScope sig) } := by
  have hscheme := TContext.resolveScheme_congr (T := CoreLParams) (formalsEnv_aliases Env σ sig)
  refine ⟨rfl, fun x => ?_⟩
  show HMaps.find? (formalsScope sig :: (substDeskolemizedAmbient σ S Env.context).types) x
      = ((TContext.subst (Function.formalsEnv Env σ sig).context.dealias S).types.find? x).map
            (mapLTyTys (deskolemizeTy σ))
  rw [TContext.subst_dealias_find?, formalsEnv_types Env σ sig, hscheme]
  cases hd : (formalsScope sig).find? x with
  | none =>
    simp only [HMaps.find?, HMap.union_empty, find?_skolemScope, hd, Option.map_none]
    exact substDeskolemizedAmbient_find? σ S Env.context x
  | some t =>
    obtain ⟨mty, hmty, rfl⟩ := formalsScope_find?_mem sig x t hd
    have hfind : (skolemScope σ sig).find? x
        = some (mapLTyTys (skolemizeTy σ) (LTy.forAll [] mty)) := by
      rw [find?_skolemScope, hd]; rfl
    have hclosed := skolemScope_closed σ sig h_sigFreeVars _ (HMap.find?_mem_values _ hfind)
    have hres : Env.context.resolveScheme (mapLTyTys (skolemizeTy σ) (LTy.forAll [] mty))
        = mapLTyTys (skolemizeTy σ) (LTy.forAll [] mty) := by
      show Env.context.resolveScheme (LTy.forAll [] (skolemizeTy σ mty))
        = LTy.forAll [] (skolemizeTy σ mty)
      rw [TContext.resolveScheme_forAll, h_res mty hmty]
    have hsub : LTy.subst S (mapLTyTys (skolemizeTy σ) (LTy.forAll [] mty))
        = mapLTyTys (skolemizeTy σ) (LTy.forAll [] mty) :=
      LTy.subst_of_closed S _ hclosed.1
    have hrt : mapLTyTys (deskolemizeTy σ)
        (mapLTyTys (skolemizeTy σ) (LTy.forAll [] mty)) = LTy.forAll [] mty := by
      show LTy.forAll [] (deskolemizeTy σ (skolemizeTy σ mty)) = LTy.forAll [] mty
      rw [h_rt mty hmty]
    simp only [HMaps.find?, HMap.union_empty, find?_skolemScope, hd, Option.map_some,
      hres, hsub, hrt]

/-- When the ambient types are closed monotypes registered once alias-resolved, and `σ`'s
    constants are unregistered, the deskolemized ambient scope finds the alias-resolved types. -/
theorem substDeskolemizedAmbient_find?_of_known (σ : RigidNames) (S : Subst)
    (C : Expression.TyContext) (Env : Expression.TyEnv)
    (h_aw : TContext.AliasesWF Env.context)
    (h_closed : LExpr.checkContextTypesClosed (T := CoreLParams) Env)
    (h_mono : MonoScope Env.context) (h_known : AmbientTypesKnown C.knownTypes Env)
    (h_fresh : RigidNamesFresh C.knownTypes σ) (x : Expression.Ident) :
    (Env.context.types.find? x).map Env.context.resolveScheme
      = (substDeskolemizedAmbient σ S Env.context).types.find? x := by
  rw [substDeskolemizedAmbient_find?, ← TContext.subst_dealias_find?,
    subst_dealias_find?_of_closed S Env Env.context (TContext.FindEq.refl _) h_aw h_closed
      h_mono x,
    TContext.dealias_find? (T := CoreLParams)]
  cases hamb : Env.context.types.find? x with
  | none => rfl
  | some t =>
    obtain ⟨vs, mty⟩ := t
    simp only [Option.map_some, TContext.resolveScheme_forAll]
    show some (LTy.forAll vs (Env.context.resolveTy mty))
      = some (LTy.forAll vs (deskolemizeTy σ (Env.context.resolveTy mty)))
    rw [deskolemizeTy_eq_self_of_knownInstance C h_fresh _ (h_known x vs mty hamb)]

/-- The substituted alias-resolved scope without aliases deskolemizes to the deskolemized ambient
    scope without aliases. -/
theorem substDeskolemizedAmbient_deskolemizes (σ : RigidNames) (S : Subst) (Γ : TContext Unit) :
    DeskolemizesScope σ { TContext.subst Γ.dealias S with aliases := [] }
      { substDeskolemizedAmbient σ S Γ with aliases := [] } := by
  refine ⟨rfl, fun x => ?_⟩
  show (substDeskolemizedAmbient σ S Γ).types.find? x
    = ((TContext.subst Γ.dealias S).types.find? x).map (mapLTyTys (deskolemizeTy σ))
  rw [substDeskolemizedAmbient_find?, TContext.subst_dealias_find?]

/-- The deskolemized ambient scope with the parameter scope pushed and no aliases has the lookups
    of the parameter context with its types alias-resolved and no aliases. -/
theorem substDeskolemizedAmbient_push_FindEq (σ : RigidNames) (S : Subst)
    (C : Expression.TyContext) (Env : Expression.TyEnv) (sig : @LMonoTySignature Unit)
    (h_aw : TContext.AliasesWF Env.context)
    (h_closed : LExpr.checkContextTypesClosed (T := CoreLParams) Env)
    (h_mono : MonoScope Env.context) (h_known : AmbientTypesKnown C.knownTypes Env)
    (h_fresh : RigidNamesFresh C.knownTypes σ)
    (h_res : ∀ mty ∈ sig.values, Env.context.resolveTy mty = mty) :
    TContext.FindEq (T := CoreLParams)
      { Env.context with types := Env.context.types.push (formalsScope sig) }.dealias
      { substDeskolemizedAmbient σ S Env.context with
          aliases := [],
          types :=
            (substDeskolemizedAmbient σ S Env.context).types.push (formalsScope sig) } := by
  refine (formalsScope_push_dealias_FindEq Env.context sig h_res).trans
    (push_FindEq (T := CoreLParams) { substDeskolemizedAmbient σ S Env.context with aliases := [] }
      Env.context.dealias (formalsScope sig) ⟨fun x => ?_, rfl⟩)
  rw [TContext.dealias_find? (T := CoreLParams)]
  exact substDeskolemizedAmbient_find?_of_known σ S C Env h_aw h_closed h_mono h_known h_fresh x

/-- An expression resolved in `E` with `σ`'s constants registered, substituted and deskolemized,
    agrees with the table and any alias-free scope lookup-equal to `E`'s scope treated likewise,
    when deskolemization fixes every factory scheme. -/
theorem resolveWithType_deskolemized_annotAgree
    (C : Expression.TyContext) (E ER : Expression.TyEnv) (σ : RigidNames)
    (e : Expression.Expr) (mty : LMonoTy)
    (et : LExprT CoreLParams.mono) (S : Subst)
    (h : resolveWithType (addSkolemTypes C σ) E e mty = .ok (et, ER))
    (h_abs : Subst.absorbs S ER.stateSubstInfo.subst)
    (h_wf : LExpr.TEnvWF (T := CoreLParams) E) (h_fac : FactorySigWF C.functions)
    (h_mono : MonoScope E.context)
    (hfixed : ∀ (nm : String) (f : LFunc CoreLParams) (ty : LTy),
      C.functions[nm]? = some f → f.type = .ok ty → mapLTyTys (deskolemizeTy σ) ty = ty)
    (h_sigsFixed : FactorySigsFixed E.context.aliases C.functions)
    {Γd Γ : TContext Unit}
    (hsc : DeskolemizesScope σ { TContext.subst E.context.dealias S with aliases := [] } Γd)
    (hEq : TContext.FindEq (T := CoreLParams) Γ Γd) :
    ScopesAnnotAgree C Γ.types (finishDeskolemized σ S et) := by
  have hfac' := FactorySigWF.addSkolemTypes C σ h_fac
  have hA := resolveWithType_annotAgree (addSkolemTypes C σ) E ER e et mty h h_wf hfac' h_mono
    h_sigsFixed S h_abs
  have hA0 : ScopesAnnotAgree (addSkolemTypes C σ)
      { TContext.subst E.context.dealias S with aliases := [] }.types
      (LExpr.unresolved (LExpr.applySubstT et S)) :=
    ScopesAnnotAgree.of_find? (Γ := TContext.subst E.context.resolveTypes S) (fun _ => rfl) hA
  have hamb : AmbientDeskol σ (addSkolemTypes C σ)
      { C with rigidTypeVars := C.rigidTypeVars ++ σ.map Prod.fst } :=
    ⟨fun _ => rfl, rfl, FactorySigDeskolemizes.refl_of_fixed _ _ hfixed⟩
  have hD := TypeSpec.ScopesAnnotAgree.deskolemize hamb hsc hfac'
    (FactorySigDeskolSafe.of_fixed _ _ hfixed) hA0
  exact ScopesAnnotAgree.of_functions_eq
    (C := { C with rigidTypeVars := C.rigidTypeVars ++ σ.map Prod.fst }) rfl
    (ScopesAnnotAgree.of_find? hEq.1 hD)

/-- A formals-environment resolution, substituted by any `S` absorbing the resolver's substitution
    and deskolemized, agrees with the table and the dealiased declared formals context, when
    deskolemization fixes every factory scheme. -/
theorem formalsEnv_resolveWithType_annotAgree
    (C : Expression.TyContext) (Env EnvStart EnvR : Expression.TyEnv) (σ : RigidNames)
    (sig : @LMonoTySignature Unit)
    (e : Expression.Expr) (mty : LMonoTy) (et : LExprT CoreLParams.mono) (S : Subst)
    (h : resolveWithType (addSkolemTypes C σ) (Function.formalsEnv EnvStart σ sig) e mty
      = .ok (et, EnvR))
    (h_abs : Subst.absorbs S EnvR.stateSubstInfo.subst)
    (h_ctx : EnvStart.context = Env.context)
    (h_wf : LExpr.TEnvWF (T := CoreLParams) EnvStart) (h_fac : FactorySigWF C.functions)
    (h_closed : LExpr.checkContextTypesClosed (T := CoreLParams) Env)
    (h_mono : MonoScope Env.context) (h_known : AmbientTypesKnown C.knownTypes Env)
    (h_fresh : RigidNamesFresh C.knownTypes σ)
    (hfixed : ∀ (nm : String) (f : LFunc CoreLParams) (ty : LTy),
      C.functions[nm]? = some f → f.type = .ok ty → mapLTyTys (deskolemizeTy σ) ty = ty)
    (h_sigsFixed : FactorySigsFixed Env.context.aliases C.functions)
    (h_sigFreeVars : ∀ v ∈ LMonoTys.freeVars sig.values, v ∈ σ.map Prod.fst)
    (h_rt : ∀ mty ∈ sig.values, deskolemizeTy σ (skolemizeTy σ mty) = mty)
    (h_resSk : ∀ mty ∈ sig.values,
      Env.context.resolveTy (skolemizeTy σ mty) = skolemizeTy σ mty)
    (h_res : ∀ mty ∈ sig.values, Env.context.resolveTy mty = mty) :
    ScopesAnnotAgree C
      { Env.context with types := Env.context.types.push (formalsScope sig) }.dealias.types
      (mapExprTys (deskolemizeTy σ) (LExpr.unresolved (LExpr.applySubstT et S))) := by
  have hmono : MonoScope EnvStart.context := by
    rw [h_ctx]
    exact h_mono
  have hresSk : ∀ mty ∈ sig.values,
      EnvStart.context.resolveTy (skolemizeTy σ mty) = skolemizeTy σ mty := by
    rw [h_ctx]
    exact h_resSk
  have hsc := formalsEnv_deskolemizes_substDeskolemizedAmbient σ S EnvStart sig []
    h_sigFreeVars h_rt hresSk
  rw [h_ctx] at hsc
  have hEq := substDeskolemizedAmbient_push_FindEq σ S C Env sig
    (h_ctx ▸ h_wf.aliasesWF) h_closed h_mono h_known h_fresh h_res
  exact resolveWithType_deskolemized_annotAgree C _ EnvR σ e mty et S h h_abs
    (formalsEnv_TEnvWF EnvStart σ sig h_wf h_sigFreeVars) h_fac
    (formalsEnv_MonoScope EnvStart σ sig hmono) hfixed
    (((formalsEnv_aliases EnvStart σ sig).trans (congrArg TContext.aliases h_ctx)) ▸ h_sigsFixed)
    hsc hEq

/-! ## Substitution ranges, binder annotations, and assembling function typing -/

/-- After a successful run the substitution range is registered once the rigid constants
    are, when the starting range, function arrows, Booleans and literal types are registered. -/
private theorem Function.checkedRun_RangeKnown
    (C : Expression.TyContext) (Env EnvCore : Expression.TyEnv) (func func' : Function)
    {outR : LMonoTy} {insR : LMonoTys} {positions : Function.CheckedPositions}
    (run : Function.CoreRun sc tn C Env EnvCore func func' outR insR positions)
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env)
    (h_fac : FactorySigWF C.functions)
    (h_arrow : C.knownTypes["arrow"]? = some 2)
    (h_lit : ∀ c : Lambda.LConst, c.isPrimitive = true →
      LMonoTy.knownInstance c.ty C.knownTypes = true)
    (h_range : Subst.RangeKnown Env.stateSubstInfo.subst C.knownTypes) :
    Subst.RangeKnown EnvCore.stateSubstInfo.subst
      (addSkolemTypes C (Function.rigidNames sc C func tn)).knownTypes := by
  have hvals := run.resolvedSig.2.1
  obtain ⟨hnudSig, -, hground, -⟩ := run.signature h_env.aliasesWF
  have hpfx := (Function.rigidNames_fresh sc C func tn).1
  have hfresh := (Function.rigidNames_fresh sc C func tn).2.2.1
  have hinsK : ∀ ty ∈ ListMap.values (func.inputs.keys.zip insR),
      LMonoTy.knownInstance (skolemizeTy (Function.rigidNames sc C func tn) ty)
        (addSkolemTypes C (Function.rigidNames sc C func tn)).knownTypes = true := by
    intro ty hty
    rw [hvals] at hty
    obtain ⟨tyDecl, -, hknown⟩ := forall2_exists_left run.insResolved ty hty
    exact knownInstance_skolemizeTy C hfresh ty hknown.2
  have hext := KnownTypesExtends_addSkolemTypes C hfresh
  have harrowSk :
      (addSkolemTypes C (Function.rigidNames sc C func tn)).knownTypes["arrow"]? = some 2 := by
    rw [addSkolemTypes_getElem?_of_find?_none C _ "arrow"
      (find?_rigid_isAllowedName_none hpfx (nm := "arrow") (isAllowedName_eq_toList ▸ rfl))]
    exact h_arrow
  have hboolSk :
      (addSkolemTypes C (Function.rigidNames sc C func tn)).knownTypes["bool"]? = some 0 := by
    rw [addSkolemTypes_getElem?_of_find?_none C _ "bool"
      (find?_rigid_isAllowedName_none hpfx (nm := "bool") (isAllowedName_eq_toList ▸ rfl))]
    exact knownTypes_bool_of_literalTys h_lit
  have hlitSk : LExpr.LiteralTysKnown (addSkolemTypes C (Function.rigidNames sc C func tn)) :=
    fun c hp _ => knownInstance_mono _ _ _ hext (h_lit c hp)
  have hint : LMonoTy.knownInstance LMonoTy.int
      (addSkolemTypes C (Function.rigidNames sc C func tn)).knownTypes = true :=
    knownInstance_mono _ _ _ hext (h_lit (.intConst 0) rfl)
  have hboolK : LMonoTy.knownInstance LMonoTy.bool
      (addSkolemTypes C (Function.rigidNames sc C func tn)).knownTypes = true :=
    knownInstance_mono _ _ _ hext (h_lit (.boolConst true) rfl)
  rw [run.envCore]
  exact checkPositions_RangeKnown
    (addSkolemTypes C (Function.rigidNames sc C func tn)) Env func outR
    insR (Function.rigidNames sc C func tn) positions run.positionsOk.choose_spec h_env hnudSig
    hground
    (FactorySigWF.addSkolemTypes C (Function.rigidNames sc C func tn) h_fac) harrowSk hboolSk
    hlitSk hint hboolK
    (knownInstance_skolemizeTy C hfresh outR run.outKnown) hinsK
    (Subst.RangeKnown_mono _ _ _ hext h_range)

/-- Every binder annotation of a stored position is a registered type of the context, when the
    substitution's range is registered once the rigid constants are. -/
private theorem binderAnnotsKnown_of_StoredPositionAt
    (C : Expression.TyContext) (EnvBase : Expression.TyEnv) (σ : RigidNames) (S : Subst)
    (sig : @LMonoTySignature Unit) (mty : LMonoTy) (stored : Expression.Expr)
    (h : StoredPositionAt C EnvBase σ S sig mty stored)
    (h_fac : FactorySigWF C.functions)
    (h_range : Subst.RangeKnown S (addSkolemTypes C σ).knownTypes) :
    BinderAnnotsKnown C stored := by
  obtain ⟨EnvStart, -, -, hwfFormal, e0, et, EnvR, hres, habs, hst, -⟩ := h
  have hfac' := FactorySigWF.addSkolemTypes C σ h_fac
  subst hst
  exact binderAnnotations_known_deskolemize (Csk := addSkolemTypes C σ) (Crig := C)
    (knownTypes_contains_of_getElem?_addSkolemTypes (fun _ => rfl)) _
    (resolveWithType_binderAnnotations_known_absorbing _ _ _ _ _ _ hres hwfFormal hfac' S habs
      h_range)

/-- Every binder annotation in a checked function's elaborated expressions is a registered type,
    when function arrows, Booleans, literal types and the incoming substitution's range are. -/
private theorem Function.Checked.binderAnnotsKnown
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv) (func func' : Function)
    (h : Function.Checked sc tn C Env Env' func func')
    (htn : ∀ n ∈ func.tyNames func.annotTys, n ∈ tn ())
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env) (h_fac : FactorySigWF C.functions)
    (h_arrow : C.knownTypes["arrow"]? = some 2)
    (h_lit : ∀ c : Lambda.LConst, c.isPrimitive = true →
      LMonoTy.knownInstance c.ty C.knownTypes = true)
    (h_substRange : Lambda.Subst.RangeKnown Env.stateSubstInfo.subst C.knownTypes) :
    (∀ body, func'.body = some body → BinderAnnotsKnown C body)
      ∧ (∀ m, func'.measure = some m → BinderAnnotsKnown C m)
      ∧ (∀ p ∈ func'.preconditions, BinderAnnotsKnown C p.expr)
      ∧ (∀ ax ∈ func'.axioms, BinderAnnotsKnown C ax) := by
  obtain ⟨_, _, _, run⟩ := h.run
  have hRK := Function.checkedRun_RangeKnown C Env Env' func func' run h_env h_fac
    h_arrow h_lit h_substRange
  obtain ⟨-, hbody, hmeasure, hpre, hax⟩ :=
    Function.checkedRun_storedPositionsAt run htn h_env h_fac
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro body hb
    exact binderAnnotsKnown_of_StoredPositionAt C Env _ _ _ _ body (hbody body hb) h_fac hRK
  · intro m hm
    exact binderAnnotsKnown_of_StoredPositionAt C Env _ _ _ _ _ (hmeasure m hm).2 h_fac hRK
  · intro p hp
    exact binderAnnotsKnown_of_StoredPositionAt C Env _ _ _ _ _ (hpre p hp) h_fac hRK
  · intro ax hax'
    exact binderAnnotsKnown_of_StoredPositionAt C Env _ _ _ _ _ (hax ax hax') h_fac hRK

/-- A checked function's elaborated form is well typed in variable scopes `ts` once its body,
    measure, preconditions and axioms are well typed over its formals. -/
private theorem Function.Checked.funcWellTyped_of_exprsTyped {ts : TypeScopes}
    (h : Function.Checked sc tn C Env Env' func func')
    (h_aw : TContext.AliasesWF Env.context)
    (h_body : ∀ body, func'.body = some body →
      ExprWellTyped C (funcScopes ts func') body func'.output)
    (h_measure : ∀ m, func'.measure = some m →
      match m with
      | .fvar _ x _ => ∃ ty, func'.inputs.find? x = some ty ∧
          (ExprWellTyped C (funcScopes ts func') m .int ∨
            ∃ n args, ty = .tcons n args ∧ (C.datatypes.getType n).isSome ∧
              ExprWellTyped C (funcScopes ts func') m (.tcons n args))
      | _ => ExprWellTyped C (funcScopes ts func') m .int)
    (h_pre : ∀ p ∈ func'.preconditions, ExprWellTyped C (funcScopes ts func') p.expr .bool)
    (h_axioms : ∀ ax ∈ func'.axioms, ExprWellTyped C (funcScopes ts func') ax .bool) :
    FuncWellTyped C ts func' := by
  obtain ⟨_, _, _, run⟩ := h.run
  obtain ⟨⟨insR, hInEq⟩, htaEq⟩ :=
    Function.Checked.signature_shape C Env Env' func func' h
  obtain ⟨hnodup, -, -⟩ :=
    Function.Checked.declared_guards C Env Env' func func' h
  obtain ⟨-, -, -, -, -, -, -, hSig⟩ :=
    Function.Checked.elaborated_shape C Env Env' func func' h h_aw
  have hwf : ∀ ty ∈ func'.output :: func'.inputs.values,
      ResolvedTyWF C TyVarAdmissibility.all ty := by
    obtain ⟨hins, hout⟩ := Function.Checked.signatureTysKnown C Env Env' func func' h
    intro ty hty
    rcases List.mem_cons.mp hty with rfl | hin
    · exact ResolvedTyWF.of_knownInstance hout
    · exact ResolvedTyWF.of_knownInstance (hins ty hin)
  have hkeysSub : func'.inputs.keys.Sublist func.inputs.keys := by
    rw [hInEq, ListMap.keys_eq_map_fst (func.inputs.keys.zip insR)]
    exact List.map_fst_zip_sublist _ _
  exact
    { inputsNodup := hkeysSub.nodup run.inputsNodup
      typeArgsNodup := htaEq ▸ hnodup
      noUndeclaredVars := Function.Checked.noUndeclaredVars_output C Env Env' func func' h h_aw
      typeArgsInSignature := hSig
      signatureWellKinded := fun ty hty => (hwf ty hty).wellKinded
      bodyTyped := h_body
      measureOnlyRecursive := Function.Checked.measureOnlyRecursive C Env Env' func func' h
      measureTyped := h_measure
      preconditionsTyped := h_pre
      axiomsTyped := h_axioms
      annotsScoped := Function.Checked.annotsScoped_output C Env Env' func func' h
      constrNoBody := Function.Checked.constr_no_body C Env Env' func func' h }

/-- At a threaded position, every free-variable annotation written in the source is a valid source
    type with no reserved type-variable name, and no written binder annotation uses one. -/
private theorem ThreadedPosition.writtenAnnotsOk
    (C : Expression.TyContext) (EnvBase EnvFinal : Expression.TyEnv)
    (σ : RigidNames) (sig : @LMonoTySignature Unit) (nm : Option String)
    (source : Expression.Expr) (expected : LMonoTy)
    (typed : LExprT CoreLParams.mono)
    (h : ThreadedPosition (addSkolemTypes C σ) EnvBase EnvFinal σ sig
      (skolemizeBody nm σ source) expected typed)
    (h_nd : (σ.map Prod.snd).Nodup)
    (h_aliases : AliasesNoSkolem σ EnvBase.context.aliases)
    (h_rig : ∀ p ∈ σ, TyVarAdmissibility.notGeneratedOrRigid p.1 = true)
    (h_allowed : allExprTys (mtyAllTyConsNames (notRigidConst σ)) source = true) :
    FVarAnnotsWF C TyVarAdmissibility.notGeneratedOrRigid
      EnvBase.context.aliases source ∧
      BinderAnnotTyVarsAdmissible TyVarAdmissibility.notGeneratedOrRigid source := by
  obtain ⟨EnvStart, EnvNext, hctx, -, ⟨EnvR, hres, -, -⟩, -⟩ := h
  have hbinder := TypeSpec.BinderAnnotTyVarsAdmissible.deskolemize σ h_rig
    (resolveWithType_binderAnnotTyVarsAdmissible (addSkolemTypes C σ) _ EnvR _ typed
      expected hres)
  rw [mapExprTys_deskolemizeTy_skolemizeBody nm h_nd source h_allowed] at hbinder
  refine ⟨fun t ht => ?_, hbinder⟩
  have hsk := resolveWithType_fvarAnnotsWF (addSkolemTypes C σ) _ EnvR _ typed
    expected hres
  simp only [TypeSpec.FVarAnnotsWF] at hsk
  rw [fvarAnnotations_skolemizeBody, formalsEnv_aliases, hctx] at hsk
  obtain ⟨r, hr⟩ := hsk (skolemizeTy σ t) (List.mem_map_of_mem ht)
  exact SourceTyWF_of_skolemizeTy C EnvBase.context σ h_nd h_aliases h_rig
    (allUserProvidedTypes_fvarAnnotations source
      ((allExprTys_eq_allUserProvidedTypes _ source).symm.trans h_allowed) t ht) hr

/-- When the checker accepts a function, with `sc` holding every type name in scope and `tn ()`
    holding every type name the function mentions, every free-variable annotation written in a
    position it resolves is a valid source type with no reserved type-variable name, and no
    written binder annotation uses one. -/
private theorem Function.Checked.writtenAnnotsOk
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv) (func func' : Function)
    (h : Function.Checked sc tn C Env Env' func func')
    (hcov : ∀ n ∈ scopeTyNames C Env, n ∈ sc.get)
    (htn : ∀ n ∈ func.tyNames func.annotTys, n ∈ tn ())
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env) (h_fac : FactorySigWF C.functions) :
    ∀ e ∈ func.exprs, WrittenAnnotsOk C (funcContext Env.context func) e := by
  have hsr := Function.rigidNames_spec sc C Env func tn hcov
  have hAliases := hsr.noSkolemAmbient.aliases
  have hpfx := hsr.prefixed
  have hnd := hsr.nodup
  obtain ⟨outR, insR, positions, run⟩ := h.run
  have hguards := Function.Checked.declared_guards C Env Env' func func' h
  obtain ⟨hnudSig, -, hgroundOut, -⟩ := run.signature h_env.aliasesWF
  have hfacSk := FactorySigWF.addSkolemTypes C (Function.rigidNames sc C func tn) h_fac
  obtain ⟨-, -, -, hbodyTrace, hmeasureTrace, hpreTrace, haxiomTrace, -, -⟩ :=
    checkPositions_trace (addSkolemTypes C (Function.rigidNames sc C func tn)) Env func outR insR
      (Function.rigidNames sc C func tn) positions run.positionsOk.choose_spec h_env hnudSig
      hgroundOut hfacSk
  have hrigAdm : ∀ p ∈ Function.rigidNames sc C func tn,
      TyVarAdmissibility.notGeneratedOrRigid p.1 = true := by
    intro p hp
    have hmem := List.mem_map_of_mem (f := Prod.fst) hp
    rw [hsr.map_fst] at hmem
    exact TyVarAdmissibility.notGeneratedOrRigid_of_isAllowedName (hguards.2.2 _ hmem)
  have hallowedData := Function.rigidNames_annots sc C func tn htn
  intro e he
  have hcases := he
  simp only [Strata.DL.Util.Func.exprs, List.mem_append, Option.mem_toList, List.mem_map]
    at hcases
  rcases hcases with ((hb | hax) | ⟨p, hp, rfl⟩) | hm
  · obtain ⟨et, -, hthread⟩ := hbodyTrace e hb
    exact hthread.writtenAnnotsOk C Env positions.env _ _ _ e _ et
      hnd hAliases hrigAdm (hallowedData e he)
  · obtain ⟨axT, -, hthread⟩ := List.Rel₂.exists_of_mem_left haxiomTrace hax
    exact hthread.writtenAnnotsOk C Env positions.env _ _ (some func.name.name) e
      LMonoTy.bool axT hnd hAliases hrigAdm (hallowedData e he)
  · obtain ⟨pt, -, -, hthread⟩ := List.Rel₂.exists_of_mem_left hpreTrace hp
    exact hthread.writtenAnnotsOk C Env positions.env _ _ (some func.name.name) p.expr
      LMonoTy.bool pt.2 hnd hAliases hrigAdm (hallowedData p.expr he)
  · obtain ⟨et, -, hthread, -⟩ := hmeasureTrace e hm
    exact hthread.writtenAnnotsOk C Env positions.env _ _ _ e
      _ et hnd hAliases hrigAdm (hallowedData e he)

/-! ## Soundness theorems -/

/-- Input soundness for a function the checker checks (`Function.Checked`) against a set `sc`
    holding every type name in scope and a list `tn ()` holding every type name the function
    mentions: when every ambient scheme is a monotype, the function satisfies `FuncHasTypeExact`. -/
private theorem Function.Checked.sound
    (h : Function.Checked sc tn C Env Env' func func')
    (hcov : ∀ n ∈ scopeTyNames C Env, n ∈ sc.get)
    (htn : ∀ n ∈ func.tyNames func.annotTys, n ∈ tn ())
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env) (h_fac : FactorySigWF C.functions)
    (h_closed : LExpr.checkContextTypesClosed (T := CoreLParams) Env)
    (h_mono : MonoScope Env.context) :
    FuncHasTypeExact C Env.context func := by
  obtain ⟨hbody, hmeasure, hpre, haxioms⟩ := Function.Checked.inputTyped C Env Env' func func'
    h hcov htn h_env h_fac h_closed h_mono
  obtain ⟨hnodup, hundeclared, hallowed⟩ :=
    Function.Checked.declared_guards C Env Env' func func' h
  obtain ⟨outR, _, _, run⟩ := h.run
  have hwk : ∀ ty ∈ func.output :: func.inputs.values,
      ∃ r, SourceTyWF C TyVarAdmissibility.all Env.context.aliases ty r := by
    intro ty hty
    rcases List.mem_cons.mp hty with rfl | hin
    · exact ⟨outR,
        LMonoTy.resolveAliases_sourceTyResolves (T := CoreLParams) _ Env outR Env run.outResolved,
        ResolvedTyWF.of_knownInstance run.outKnown⟩
    · obtain ⟨ty', hty', hres⟩ := List.Rel₂.exists_of_mem_left run.insResolveEach hin
      obtain ⟨-, -, -, hknown⟩ := forall2_exists_left run.insResolved ty' hty'
      exact ⟨ty', LMonoTy.resolveAliases_sourceTyResolves (T := CoreLParams) ty Env ty' Env hres,
        ResolvedTyWF.of_knownInstance hknown⟩
  have hnoScope : ∀ v w, ([] : WrittenTyVarScope.ScopeMap).lookup v = some w →
      ((fun _ => none : WrittenEnv) v).isSome := by
    intro v w hl
    simp at hl
  exact
    { inputsNodup := run.inputsNodup
      typeArgsNodup := hnodup
      noUndeclaredVars := hundeclared
      typeArgsInSignature :=
        Function.Checked.typeArgsInSignature_input C Env Env' func func' h h_env.aliasesWF
      signatureWellKinded := hwk
      bodyTyped := hbody
      measureOnlyRecursive := run.measureOnlyRecursive
      measureTyped := hmeasure
      preconditionsTyped := hpre
      axiomsTyped := haxioms
      annotsScoped := fun e he =>
        annotsInScope_of_unboundAnnotVar? hnoScope (run.writtenScoped e he)
      writtenAnnotsOk :=
        Function.Checked.writtenAnnotsOk C Env Env' func func' h hcov htn h_env h_fac
      typeArgsNotReserved := hallowed
      constrNoBody := run.constrNoBody }

/-- Output soundness for a function the checker checks (`Function.Checked`) against a set `sc`
    holding every type name in scope: the elaborated form is well typed over the alias-resolved
    variable scopes. -/
private theorem Function.Checked.sound_output
    (h : Function.Checked sc tn C Env Env' func func')
    (hcov : ∀ n ∈ scopeTyNames C Env, n ∈ sc.get)
    (htn : ∀ n ∈ func.tyNames func.annotTys, n ∈ tn ())
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env) (h_fac : FactorySigWF C.functions)
    (h_resolved : TContext.AliasesResolved Env.context)
    (h_arrow : C.knownTypes["arrow"]? = some 2)
    (h_lit : ∀ c : Lambda.LConst, c.isPrimitive = true →
      LMonoTy.knownInstance c.ty C.knownTypes = true)
    (h_substRange : Lambda.Subst.RangeKnown Env.stateSubstInfo.subst C.knownTypes)
    (h_closed : LExpr.checkContextTypesClosed (T := CoreLParams) Env)
    (h_mono : MonoScope Env.context) (h_known : AmbientTypesKnown C.knownTypes Env)
    (h_aliasNamesFresh : ∀ al ∈ Env.context.aliases, C.knownTypes.containsName al.name = false)
    (h_sigsFixed : FactorySigsFixed Env.context.aliases C.functions) :
    FuncWellTyped C Env.context.dealias.types func' := by
  have hbind := Function.Checked.binderAnnotsKnown C Env Env' func func' h htn h_env h_fac
    h_arrow h_lit h_substRange
  obtain ⟨outR, insR, positions, run⟩ := h.run
  obtain ⟨-, hbodyAt, hmeasureAt, hpreAt, haxAt⟩ :=
    Function.checkedRun_storedPositionsAt run htn h_env h_fac
  obtain ⟨hnudSig, -, -, -, hrtSig⟩ := run.signature h_env.aliasesWF
  have hins : func'.inputs = func.inputs.keys.zip insR := by rw [run.stored]
  have hsr := Function.rigidNames_spec sc C Env func tn hcov
  have hpfx := hsr.prefixed
  have hfresh := hsr.fresh
  have hknown : ∀ mty ∈ ListMap.values (func.inputs.keys.zip insR),
      LMonoTy.knownInstance mty C.knownTypes = true := by
    intro mty hm
    rw [← hins] at hm
    exact (Function.Checked.signatureTysKnown C Env Env' func func' h).1 mty hm
  have hres :
      ∀ mty ∈ ListMap.values (func.inputs.keys.zip insR), Env.context.resolveTy mty = mty :=
    fun mty hm =>
      TContext.resolveTy_of_knownInstance (T := CoreLParams) h_aliasNamesFresh (hknown mty hm)
  have hresSk : ∀ mty ∈ ListMap.values (func.inputs.keys.zip insR),
      Env.context.resolveTy (skolemizeTy (Function.rigidNames sc C func tn) mty)
        = skolemizeTy (Function.rigidNames sc C func tn) mty :=
    fun mty hm => TContext.resolveTy_of_knownInstance (T := CoreLParams)
      (fun al hal => addSkolemTypes_notContains_of_ne C _ al.name
        (hsr.aliasNames al hal)
        (h_aliasNamesFresh al hal))
      (knownInstance_skolemizeTy C hfresh mty (hknown mty hm))
  have hctxEq : TContext.FindEq (T := CoreLParams) (funcContext Env.context.dealias func')
      { Env.context with
          types :=
            Env.context.types.push (formalsScope (func.inputs.keys.zip insR)) }.dealias := by
    unfold funcContext funcScopes
    rw [hins]
    exact (formalsScope_push_dealias_FindEq Env.context _ hres).symm
  have hagree : ∀ mty stored, StoredPositionAt C Env (Function.rigidNames sc C func tn)
      Env'.stateSubstInfo.subst (func.inputs.keys.zip insR) mty stored →
      ScopesAnnotAgree C (funcScopes Env.context.dealias.types func') stored := by
    rintro mty _ ⟨EnvStart, hctx, hwf, -, e0, et, EnvR, hrun, habs, rfl, -⟩
    exact ScopesAnnotAgree.of_find? (Ξ := funcContext Env.context.dealias func') hctxEq.1
      (formalsEnv_resolveWithType_annotAgree C Env EnvStart EnvR _ _ e0 mty et _ hrun habs
        hctx hwf h_fac h_closed h_mono h_known hfresh
        hsr.noSkolemAmbient.functions h_sigsFixed
        hnudSig hrtSig
        hresSk hres)
  refine Function.Checked.funcWellTyped_of_exprsTyped C Env Env' func func' h
    h_env.aliasesWF
    (fun body hb =>
      ⟨Function.Checked.bodyTyped_output C Env Env' func func' h htn h_env h_fac h_resolved
        body hb, hbind.1 body hb, hagree _ _ (hbodyAt body hb)⟩)
    ?_
    (fun p hp =>
      ⟨Function.Checked.preconditionsTyped_output C Env Env' func func' h htn
        h_env h_fac h_resolved p hp, hbind.2.2.1 p hp, hagree _ _ (hpreAt p hp)⟩)
    (fun ax hax =>
      ⟨Function.Checked.axiomsTyped_output C Env Env' func func' h htn
        h_env h_fac h_resolved ax hax, hbind.2.2.2 ax hax, hagree _ _ (haxAt ax hax)⟩)
  intro m hm
  obtain ⟨hkey, hA⟩ := Function.Checked.measureTyped_output C Env Env' func func' h htn
    h_env h_fac h_resolved m hm
  exact measureObligation_of_measureTy (R := Eq)
    (T := fun ty => LExpr.HasTypeA [] m ty ∧ BinderAnnotsKnown C m ∧
      ScopesAnnotAgree C (funcScopes Env.context.dealias.types func') m)
    (fun _ ty' hfind => ⟨ty', hfind, rfl⟩) hkey
    ⟨hA, hbind.2.1 m hm, hagree _ _ (hmeasureAt m hm).2⟩

/-- `Function.typeCheckIn` returns the checker's renaming of the reserved type parameters of the
    function it accepts. -/
theorem Function.typeCheckIn_renamed {scope : Thunk (Std.HashSet String)}
    {C : Expression.TyContext} {Env : Expression.TyEnv} {func renamed func' : Function}
    (h : Function.typeCheckIn scope C Env func = .ok (renamed, func')) :
    renamed = Function.renameReservedTypeArgs C Env func (fun _ => func.annotTys) :=
  (Function.typeCheckIn_checked h).1

/-- Input soundness for functions checked against a given set of type names: when `scope` holds
    every type name in scope, the renaming of the reserved type parameters that
    `Function.typeCheckIn` returns satisfies `FuncHasTypeExact`. The environment is well formed,
    the factory's function signatures are well formed, and every ambient scheme is closed and a
    monotype. -/
theorem Function.typeCheckIn_sound (scope : Thunk (Std.HashSet String))
    (C : Expression.TyContext) (Env : Expression.TyEnv) (func renamed func' : Function)
    (h : Function.typeCheckIn scope C Env func = .ok (renamed, func'))
    (hcov : ∀ n ∈ scopeTyNames C Env, n ∈ scope.get)
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env) (h_fac : FactorySigWF C.functions)
    (h_closed : LExpr.checkContextTypesClosed (T := CoreLParams) Env)
    (h_mono : MonoScope Env.context) :
    FuncHasTypeExact C Env.context renamed := by
  obtain ⟨rfl, EnvCore, hc⟩ := Function.typeCheckIn_checked h
  have htn := Function.tyNames_renameReservedTypeArgs C Env func (fun _ => func.annotTys)
  exact Function.Checked.sound C Env EnvCore _ func' hc hcov (fun _ hn => htn ▸ hn) h_env
    h_fac h_closed h_mono

/-- Output soundness for functions checked against a given set of type names: when `scope` holds
    every type name in scope, the elaborated form `Function.typeCheckIn` returns is well typed
    over the alias-resolved variable scopes.
    The environment is well formed with closed monotype schemes whose alias-resolved types are
    registered; no alias body mentions an alias, and no registered type is named like an alias;
    the factory's function signatures are well formed and built from registered types; and
    `arrow`, the type of every primitive literal and the range of the substitution are
    registered. -/
theorem Function.typeCheckIn_sound_output (scope : Thunk (Std.HashSet String))
    (C : Expression.TyContext) (Env : Expression.TyEnv) (func renamed func' : Function)
    (h : Function.typeCheckIn scope C Env func = .ok (renamed, func'))
    (hcov : ∀ n ∈ scopeTyNames C Env, n ∈ scope.get)
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env) (h_fac : FactorySigWF C.functions)
    (h_resolved : TContext.AliasesResolved Env.context)
    (h_arrow : C.knownTypes["arrow"]? = some 2)
    (h_lit : ∀ c : Lambda.LConst, c.isPrimitive = true →
      LMonoTy.knownInstance c.ty C.knownTypes = true)
    (h_substRange : Lambda.Subst.RangeKnown Env.stateSubstInfo.subst C.knownTypes)
    (h_closed : LExpr.checkContextTypesClosed (T := CoreLParams) Env)
    (h_mono : MonoScope Env.context) (h_known : AmbientTypesKnown C.knownTypes Env)
    (h_aliasNamesFresh : ∀ al ∈ Env.context.aliases, C.knownTypes.containsName al.name = false)
    (h_sigsFixed : FactorySigsFixed Env.context.aliases C.functions) :
    FuncWellTyped C Env.context.dealias.types func' := by
  obtain ⟨rfl, EnvCore, hc⟩ := Function.typeCheckIn_checked h
  have htn := Function.tyNames_renameReservedTypeArgs C Env func (fun _ => func.annotTys)
  exact Function.Checked.sound_output C Env EnvCore _ func' hc hcov
    (fun _ hn => htn ▸ hn) h_env h_fac h_resolved
    h_arrow h_lit h_substRange h_closed h_mono h_known h_aliasNamesFresh h_sigsFixed

/-- For any name sets, the renaming of the reserved type parameters that `Function.typeCheckIn`
    returns renames distinct parameters to distinct fresh names that neither the function nor the
    context uses, so it captures no type variable. -/
theorem Function.typeCheckIn_alphaVariant {scope : Thunk (Std.HashSet String)}
    {C : Expression.TyContext} {Env : Expression.TyEnv} {func renamed func' : Function}
    (h : Function.typeCheckIn scope C Env func = .ok (renamed, func')) :
    FuncAlphaVariant C Env.context func renamed := by
  obtain ⟨rfl, EnvCore, hc⟩ := Function.typeCheckIn_checked h
  exact Function.renameReservedTypeArgs_alphaVariant C Env func
    (Function.typeArgs_nodup_of_renameReservedTypeArgs C Env func _
      (Function.Checked.declared_guards C Env EnvCore _ func' hc).1)

/-- Input soundness for functions checked against a given set of type names: when `scope` holds
    every type name in scope, a function `Function.typeCheckIn` accepts satisfies the
    typechecker spec. The environment is well formed, the factory's function signatures are well
    formed, and every ambient scheme is closed and a monotype. -/
theorem Function.typeCheckIn_funcHasType (scope : Thunk (Std.HashSet String))
    (C : Expression.TyContext) (Env : Expression.TyEnv) (func renamed func' : Function)
    (h : Function.typeCheckIn scope C Env func = .ok (renamed, func'))
    (hcov : ∀ n ∈ scopeTyNames C Env, n ∈ scope.get)
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env) (h_fac : FactorySigWF C.functions)
    (h_closed : LExpr.checkContextTypesClosed (T := CoreLParams) Env)
    (h_mono : MonoScope Env.context) :
    FuncHasType C Env.context func :=
  ⟨renamed, Function.typeCheckIn_alphaVariant h,
    Function.typeCheckIn_sound scope C Env func renamed func' h hcov h_env h_fac h_closed h_mono⟩

/-- The checker's renaming of the reserved type parameters of a function it accepts renames
    distinct parameters to distinct fresh names that neither the function nor the context uses,
    so it captures no type variable. -/
theorem Function.typeCheck_alphaVariant
    {C : Expression.TyContext} {Env Env' : Expression.TyEnv} {func func' : Function}
    (h : Function.typeCheck C Env func = .ok (func', Env')) :
    FuncAlphaVariant C Env.context func
      (Function.renameReservedTypeArgs C Env func (fun _ => func.annotTys)) :=
  Function.typeCheckIn_alphaVariant (Function.typeCheck_in h)

/-- Input soundness for functions, for the function the checker types: the renaming of the
    reserved type parameters of an accepted function satisfies `FuncHasTypeExact`. The
    environment is well formed, the factory's function signatures are well formed, and every
    ambient scheme is closed and a monotype. -/
theorem Function.typeCheck_sound_renamed
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv) (func func' : Function)
    (h : Function.typeCheck C Env func = .ok (func', Env'))
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env) (h_fac : FactorySigWF C.functions)
    (h_closed : LExpr.checkContextTypesClosed (T := CoreLParams) Env)
    (h_mono : MonoScope Env.context) :
    FuncHasTypeExact C Env.context
      (Function.renameReservedTypeArgs C Env func (fun _ => func.annotTys)) :=
  Function.typeCheckIn_sound _ C Env func _ func' (Function.typeCheck_in h)
    (scopeTyNameThunk_cover C Env) h_env h_fac h_closed h_mono

/-- Input soundness for functions: a function the checker accepts satisfies the typechecker spec.
    The function the spec types is the checker's renaming of the reserved type parameters, a
    renaming that captures no type variable. The environment is well formed, the factory's
    function signatures are well formed, and every ambient scheme is closed and a monotype. -/
theorem Function.typeCheck_sound
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv) (func func' : Function)
    (h : Function.typeCheck C Env func = .ok (func', Env'))
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env) (h_fac : FactorySigWF C.functions)
    (h_closed : LExpr.checkContextTypesClosed (T := CoreLParams) Env)
    (h_mono : MonoScope Env.context) :
    FuncHasType C Env.context func := by
  have hIn := Function.typeCheck_in h
  exact Function.typeCheckIn_funcHasType _ C Env func _ func' hIn (scopeTyNameThunk_cover C Env)
    h_env h_fac h_closed h_mono

/-- Output soundness for functions: the elaborated form of an accepted function is well typed over
    the alias-resolved variable scopes.
    The environment is well formed with closed monotype schemes whose alias-resolved types are
    registered; no alias body mentions an alias, and no registered type is named like an alias;
    the factory's function signatures are well formed and built from registered types; and
    `arrow`, the type of every primitive literal and the range of the substitution are
    registered. -/
theorem Function.typeCheck_sound_output
    (C : Expression.TyContext) (Env Env' : Expression.TyEnv) (func func' : Function)
    (h : Function.typeCheck C Env func = .ok (func', Env'))
    (h_env : LExpr.TEnvWF (T := CoreLParams) Env) (h_fac : FactorySigWF C.functions)
    (h_resolved : TContext.AliasesResolved Env.context)
    (h_arrow : C.knownTypes["arrow"]? = some 2)
    (h_lit : ∀ c : Lambda.LConst, c.isPrimitive = true →
      LMonoTy.knownInstance c.ty C.knownTypes = true)
    (h_substRange : Lambda.Subst.RangeKnown Env.stateSubstInfo.subst C.knownTypes)
    (h_closed : LExpr.checkContextTypesClosed (T := CoreLParams) Env)
    (h_mono : MonoScope Env.context) (h_known : AmbientTypesKnown C.knownTypes Env)
    (h_aliasNamesFresh : ∀ al ∈ Env.context.aliases, C.knownTypes.containsName al.name = false)
    (h_sigsFixed : FactorySigsFixed Env.context.aliases C.functions) :
    FuncWellTyped C Env.context.dealias.types func' := by
  have hIn := Function.typeCheck_in h
  exact Function.typeCheckIn_sound_output _ C Env func _ func' hIn (scopeTyNameThunk_cover C Env)
    h_env h_fac h_resolved h_arrow h_lit h_substRange h_closed h_mono h_known
    h_aliasNamesFresh h_sigsFixed

/-! ## Properties of `Function.typeCheck` -/

/-- For any name sets, the name, constructor and recursion flags, and attributes of a function
    `Function.typeCheckIn` accepts are the declared ones. -/
theorem Function.typeCheckIn_copies_untouched_fields (scope : Thunk (Std.HashSet String))
    (C : Expression.TyContext) (Env : Expression.TyEnv) (func renamed func' : Function)
    (h : Function.typeCheckIn scope C Env func = .ok (renamed, func')) :
    func'.name = func.name
      ∧ func'.isConstr = func.isConstr
      ∧ func'.isRecursive = func.isRecursive
      ∧ func'.attr = func.attr := by
  obtain ⟨hname, hconstr, hrec, hattr, -⟩ :=
    Function.renameReservedTypeArgs_fields C Env func (fun _ => func.annotTys)
  rw [← hname, ← hconstr, ← hrec, ← hattr]
  obtain ⟨rfl, _, hc⟩ := Function.typeCheckIn_checked h
  obtain ⟨_, _, _, run⟩ := hc.run
  exact run.untouchedFields

/-- For any name sets, a function `Function.typeCheckIn` accepts keeps the name, type parameters
    and formal names of the renaming it returns, and stores input and output types
    alias-equivalent to those of the renaming. -/
theorem Function.typeCheckIn_funcSigAgree (scope : Thunk (Std.HashSet String))
    (C : Expression.TyContext) (Env : Expression.TyEnv) (func renamed func' : Function)
    (h : Function.typeCheckIn scope C Env func = .ok (renamed, func')) :
    FuncSigAgree Env.context.aliases renamed.toLFunc func'.toLFunc := by
  obtain ⟨-, EnvCore, h⟩ := Function.typeCheckIn_checked h
  obtain ⟨outR, insR, _, run⟩ := h.run
  obtain ⟨hkeys, hvals, hoe⟩ := run.resolvedSig
  have hins : AliasEquivList Env.context.aliases renamed.inputs.values
      (ListMap.values (renamed.inputs.keys.zip insR)) := by
    rw [hvals]
    exact AliasEquivList.of_forall₂ (fun _ _ hr => hr.1) run.insResolved
  have hstored := run.stored
  subst hstored
  exact ⟨rfl, rfl, hkeys.symm, hins, hoe⟩

/-- For any name sets, a function `Function.typeCheckIn` accepts keeps the constructor and
    recursion flags, the attributes, whether there is a body and a measure, the number of axioms
    and the precondition metadata of the renaming it returns. -/
theorem Function.typeCheckIn_funcShapeAgree (scope : Thunk (Std.HashSet String))
    (C : Expression.TyContext) (Env : Expression.TyEnv) (func renamed func' : Function)
    (h : Function.typeCheckIn scope C Env func = .ok (renamed, func')) :
    FuncShapeAgree renamed.toLFunc func'.toLFunc := by
  obtain ⟨-, EnvCore, h⟩ := Function.typeCheckIn_checked h
  obtain ⟨_, _, _, run⟩ := h.run
  obtain ⟨_, _, _, hb, hm, hp, ha⟩ := checkPositions_inv run.positionsOk.choose_spec
  have hbody : renamed.body.isSome = func'.body.isSome := by
    rw [run.stored]
    rcases checkBody_inv hb with ⟨hnone, hT, -⟩ | ⟨body, et, hsome, hT, -⟩
    · simp only [hnone, hT, Option.map_none]
    · simp only [hsome, hT, Option.map_some, Option.isSome_some]
  have hmeasure : renamed.measure.isSome = func'.measure.isSome := by
    rw [run.stored]
    rcases checkMeasure_inv hm with ⟨hnone, hT, -⟩ | ⟨m, et, hsome, hT, -⟩
    · simp only [hnone, hT, Option.map_none]
    · simp only [hsome, hT, Option.map_some, Option.isSome_some]
  have hax : renamed.axioms.length = func'.axioms.length := by
    rw [run.stored, List.length_map]
    exact ((checkAxioms_boolWalk _ _ _ _).records _ _ _ _ ha).length_eq
  have hmd := ((checkPreconditions_boolWalk _ _ _ _).records _ _ _ _ hp).map_eq
    (f := (·.md)) (g := (·.1)) fun _ _ ⟨_, hy⟩ => (congrArg Prod.fst hy).symm
  have hpre : renamed.preconditions.map (·.md) = func'.preconditions.map (·.md) := by
    rw [run.stored, hmd]
    simp only [List.map_map]
    rfl
  obtain ⟨-, hconstr, hrec, hattr⟩ := run.untouchedFields
  exact ⟨hconstr.symm, hrec.symm, hattr.symm, hbody, hmeasure, hax, hpre⟩

/-- The `LFunc` with the function's name and the renamed type parameters and signature that
    `Function.typeCheckIn` returns, and no body, is well formed. -/
theorem LFuncWF_stub {scope : Thunk (Std.HashSet String)} (C : Expression.TyContext)
    (Env : Expression.TyEnv) {f g f' : Function}
    (h : Function.typeCheckIn scope C Env f = .ok (g, f')) :
    LFuncWF (T := CoreLParams)
      { name := f.name, typeArgs := g.typeArgs, inputs := g.inputs, output := g.output } := by
  obtain ⟨-, EnvCore, h⟩ := Function.typeCheckIn_checked h
  obtain ⟨hta, hsig, hallow⟩ := Function.Checked.declared_guards C Env EnvCore g f' h
  obtain ⟨_, _, _, run⟩ := h.run
  have hnd : (ListMap.keys g.inputs).Nodup := run.inputsNodup
  exact
    { arg_nodup := nodup_names_of_nodup_keys g.inputs hnd
      typeArgs_nodup := hta
      inputs_typevars_in_typeArgs := by
        intro ty hty v hv
        exact hsig v (mem_freeVars_mkArrow'_input g.output v g.inputs.values ty hty hv)
      output_typevars_in_typeArgs := by
        intro v hv
        exact hsig v (mem_freeVars_mkArrow'_output g.output v g.inputs.values hv)
      body_freevars := by intro _ hb; exact absurd hb (by simp)
      precond_freevars := by intro _ hp; exact absurd hp (by simp)
      constr_no_eval := by simp
      typeArgs_no_gen_prefix := by
        intro ta hta'
        exact not_genTyPrefix_of_isAllowedName (hallow ta hta') }

/-! ## Transporting expression typing across deskolemization -/

/-- `DeskolemizesScope` gives the scope correspondence `Core.ScopeCorr` at the empty choice for the
    rigid parameters. -/
private theorem DeskolemizesScope.toScopeCorr (σ : RigidNames) (Γ Γ' : TContext Unit)
    (hsc : DeskolemizesScope σ Γ Γ') : Core.ScopeCorr σ [] Γ Γ' := by
  have hfun : (fun m => deskolemizeTy σ (LMonoTy.subst ([] : Subst) m)) = deskolemizeTy σ := by
    funext m; rw [LMonoTy.subst_nil]
  intro k
  rw [hfun]
  exact (hsc.2 k)

/-- Polymorphic typing carries over to a context with the same type arities that reports, under
    every name, each signature the original reports. -/
private theorem HasType_ambient_congr {C C' : LContext CoreLParams}
    (hk : ∀ x : String, C'.knownTypes[x]? = C.knownTypes[x]?)
    (hf : ∀ (nm : String) (f : LFunc CoreLParams) (fty : LTy),
      C.functions[nm]? = some f → f.type = .ok fty →
      ∃ f', C'.functions[nm]? = some f' ∧ f'.type = .ok fty)
    (Γ : TContext CoreLParams.IDMeta) (e : LExpr CoreLParams.mono) (ty : LTy)
    (h : Lambda.LExpr.HasType (T := CoreLParams) C Γ e ty) :
    Lambda.LExpr.HasType (T := CoreLParams) C' Γ e ty := by
  have hcontains : ∀ k, C.knownTypes.contains k = true → C'.knownTypes.contains k = true := by
    intro k hc
    simp only [KnownTypes.contains, Identifiers.contains, hk] at hc ⊢
    exact hc
  induction h with
  | tbool_const Δ m b hknown =>
    exact .tbool_const Δ m b (containsName_of_getElem?_agree hk "bool" hknown)
  | tint_const Δ m n hknown =>
    exact .tint_const Δ m n (containsName_of_getElem?_agree hk "int" hknown)
  | treal_const Δ m r hknown =>
    exact .treal_const Δ m r (containsName_of_getElem?_agree hk "real" hknown)
  | tstr_const Δ m s hknown =>
    exact .tstr_const Δ m s (containsName_of_getElem?_agree hk "string" hknown)
  | tbitvec_const Δ m n b hknown =>
    exact .tbitvec_const Δ m n b (containsName_of_getElem?_agree hk "bitvec" hknown)
  | tmap_const Δ m k v d es hknown hw =>
    exact .tmap_const Δ m k v d es (containsName_of_getElem?_agree hk "Map" hknown) hw
  | tseq_const Δ m a es hknown hw =>
    exact .tseq_const Δ m a es (containsName_of_getElem?_agree hk "Sequence" hknown) hw
  | tvar Δ m x tyx hfind => exact .tvar Δ m x tyx hfind
  | tvar_annotated Δ m x ty_o ty_s tys ann hfind hlen hopen hcompat =>
    exact .tvar_annotated Δ m x ty_o ty_s tys ann hfind hlen hopen hcompat
  | tabs Δ m name x x_ty eb e_ty o hfresh hx he hbody hann hvalid ih =>
    exact .tabs Δ m name x x_ty eb e_ty o hfresh hx he ih hann
      (fun t ht => (hvalid t ht).imp fun _ hr =>
        SourceTyWF.of_knownTypes_contains hcontains hr)
  | tapp Δ m e1 e2 t1 t2 h1 h2 hfn harg ih1 ih2 => exact .tapp Δ m e1 e2 t1 t2 h1 h2 ih1 ih2
  | tinst Δ eb tyb e_ty x x_ty hb heq ih => exact .tinst Δ eb tyb e_ty x x_ty ih heq
  | tgen Δ eb a tyb hb hfresh ih => exact .tgen Δ eb a tyb ih hfresh
  | tif Δ m c e1 e2 tyb hc h1 h2 ihc ih1 ih2 => exact .tif Δ m c e1 e2 tyb ihc ih1 ih2
  | teq Δ m e1 e2 tyb h1 h2 ih1 ih2 => exact .teq Δ m e1 e2 tyb ih1 ih2
  | tquant Δ m k name tr tr_ty x x_ty eb o hfresh hx hbody htr hann hvalid ihb ihtr =>
    exact .tquant Δ m k name tr tr_ty x x_ty eb o hfresh hx ihb ihtr hann
      (fun t ht => (hvalid t ht).imp fun _ hr =>
        SourceTyWF.of_knownTypes_contains hcontains hr)
  | top Δ m f op tyb hop hfty =>
    obtain ⟨f', hop', hfty'⟩ := hf op.name f tyb hop hfty
    exact .top Δ m f' op tyb hop' hfty'
  | top_annotated Δ m f op ty_o ty_s tys ann hop hfty hlen hopen hcompat =>
    obtain ⟨f', hop', hfty'⟩ := hf op.name f ty_o hop hfty
    exact .top_annotated Δ m f' op ty_o ty_s tys ann hop' hfty' hlen hopen hcompat
  | talias Δ eb mty mty' hae hb ih => exact .talias Δ eb mty mty' hae ih

/-- Well-typedness survives deskolemizing the expression, its type, its scope and its context,
    when the skolemized context is the rigid one skolemized by the renaming. -/
theorem TypeSpec.ExprWellTyped.deskolemize (σ : RigidNames) (hpfx : RigidNamesPrefixed σ)
    {Csk Crig : LContext CoreLParams} {Γ Γ' : TContext Unit}
    (hamb : AmbientDeskol σ Csk Crig) (hsc : DeskolemizesScope σ Γ Γ')
    (hwf : FactorySigWF (T := CoreLParams) Csk.functions)
    (hsafe : FactorySigDeskolSafe σ Csk.functions) {e : Expression.Expr} {mty : LMonoTy}
    (hc : ConstTysFixed σ e) (h : ExprWellTyped Csk Γ.types e mty) :
    ExprWellTyped Crig Γ'.types (mapExprTys (deskolemizeTy σ) e) (deskolemizeTy σ mty) := by
  obtain ⟨hA, hB, hagree⟩ := h
  have hD := Core.HasTypeA_replaceUserProvidedType_deskolemizeTy hpfx [] e mty hc hA
  refine ⟨?_, ?_, TypeSpec.ScopesAnnotAgree.deskolemize hamb hsc hwf hsafe hagree⟩
  · change LExpr.HasTypeA [] (mapExprTys (deskolemizeTy σ) e)
      (deskolemizeTy σ mty)
    simpa only [List.map_nil, mapExprTys] using hD
  · exact binderAnnotations_known_deskolemize
      (knownTypes_contains_of_getElem?_addSkolemTypes hamb.knownTypes_eq) e hB

/-- Polymorphic typing transports across deskolemization, given a factory whose signatures are
    well formed and deskolemize without capture, a monotype scope and no rigid-name clash. -/
theorem exprTyped_deskolemize_polymorphic
    (σ : RigidNames) (hpfx : RigidNamesPrefixed σ)
    (Csk Crig : LContext CoreLParams) (Γ Γ' : TContext Unit)
    (hamb : AmbientDeskol σ Csk Crig) (hsc : DeskolemizesScope σ Γ Γ')
    (e : Core.Expression.Expr) (mty : LMonoTy)
    (h_fwf : FactorySigWF (T := CoreLParams) Csk.functions)
    (h_fsafe : FactorySigDeskolSafe σ Csk.functions)
    (h_mono : Lambda.MonoScope Γ)
    (h_awf : Lambda.TContext.AliasesWF Γ)
    (h_adesk : AliasesNoSkolem σ Γ.aliases)
    (h_annot : allExprTys (annotNoRigidClash σ) e = true)
    (h_lits : ConstTysFixed σ e)
    (h : LExpr.HasType Csk Γ e (.forAll [] mty)) :
    LExpr.HasType Crig Γ' (mapExprTys (deskolemizeTy σ) e)
      (.forAll [] (deskolemizeTy σ mty)) := by
  obtain ⟨hknown, -, hfac⟩ := hamb
  have hbase : ∀ x : String,
      (addSkolemTypes { Csk with knownTypes := Crig.knownTypes } σ).knownTypes[x]?
        = Csk.knownTypes[x]? := by
    intro x
    rw [addSkolemTypes_getElem?_congr { Csk with knownTypes := Crig.knownTypes } Crig σ
      (fun _ => rfl) x, ← hknown x]
  have hfun : ∀ nm : String,
      (addSkolemTypes { Csk with knownTypes := Crig.knownTypes } σ).functions[nm]?
        = Csk.functions[nm]? := by
    intro nm; simp only [addSkolemTypes]
  have hsk : Lambda.LExpr.HasType (T := CoreLParams)
      (addSkolemTypes { Csk with knownTypes := Crig.knownTypes } σ) Γ e (LTy.forAll [] mty) :=
    HasType_ambient_congr hbase
      (fun nm f fty hf hfty => ⟨f, by rw [hfun nm]; exact hf, hfty⟩) Γ e _ h
  have hT := Core.skolemTransfer_gen_between
    (C := { Csk with knownTypes := Crig.knownTypes }) (σ := σ) Crig.functions
    hpfx h_fwf hfac h_fsafe hsk
    Γ' [] [] (DeskolemizesScope.toScopeCorr σ Γ Γ' hsc) h_mono
    (Core.BinderOnly_nil [] (LTy.boundVars (LTy.forAll [] mty))) hsc.1 h_awf h_adesk h_annot h_lits
  simp only [LTy.toMonoTypeUnsafe, List.append_nil, LMonoTy.subst_nil] at hT
  show Lambda.LExpr.HasType (T := CoreLParams) _ Γ' (mapExprTys (deskolemizeTy σ) e)
    (LTy.forAll [] (deskolemizeTy σ mty))
  exact HasType_ambient_congr
    (C := { { Csk with knownTypes := Crig.knownTypes } with functions := Crig.functions })
    (C' := Crig) (fun _ => rfl)
    (fun _ f fty hf hfty => ⟨f, hf, hfty⟩) Γ' _ _ hT

/-- What polymorphic typing needs of the ambient context and the type-scope to transport across
    deskolemization, with the factory satisfying `Q`. -/
structure DeskolAmbientScope (Q : Lambda.Factory CoreLParams → Prop) (σ : RigidNames)
    (C : LContext CoreLParams) (Γ : TContext Unit) : Prop where
  /-- The context's factory satisfies `Q`. -/
  factoryWF : Q C.functions
  /-- Every changed polymorphic signature avoids capture by the rigid parameter names. -/
  signaturesSafe : FactorySigDeskolSafe σ C.functions
  /-- Every scheme the type-scope stores is a monotype. -/
  monoScope : Lambda.MonoScope (IDMeta := Unit) Γ
  /-- Every alias in the type-scope is well formed. -/
  aliasesWF : Lambda.TContext.AliasesWF (IDMeta := Unit) Γ
  /-- Deskolemization treats every alias in the type-scope as an ordinary type constructor. -/
  aliasesNoSkolem : AliasesNoSkolem σ Γ.aliases

/-- Deskolemizing a type well kinded in the skolemized context gives one well kinded in the rigid
    context. -/
theorem WellKindedTy_deskolemizeTy {σ : RigidNames} {Csk Crig : LContext CoreLParams}
    (hamb : AmbientDeskol σ Csk Crig) (mty : LMonoTy) (h : Csk.WellKindedTy mty) :
    Crig.WellKindedTy (deskolemizeTy σ mty) := by
  intro ref n hmem
  obtain ⟨hmem₀, hnot⟩ := mem_getTypeConsArities_deskolemizeTy σ mty ref n hmem
  show Crig.knownTypes[ref]? = some n
  rw [← addSkolemTypes_getElem?_of_find?_none Crig σ ref hnot, ← hamb.knownTypes_eq ref]
  exact h ref n hmem₀

end Core

end -- public section
