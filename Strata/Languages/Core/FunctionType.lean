/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
import all Strata.DL.Lambda.LTyProps

public import Strata.Languages.Core.TypeSkolem
public import Strata.Languages.Core.Function
import Strata.DL.Lambda.LExprT
import Strata.Languages.Core.Procedure
import Strata.Languages.Core.WrittenTyVarScope
import Strata.DL.Lambda.LExprType
import Strata.Util.Name

---------------------------------------------------------------------

public section

namespace Core

open Lambda Imperative
open Std (ToFormat Format format)

/-- Rewrite each rigid constant of `σ` in a message to the type-variable name it stands for. -/
def deskolemizeStr (σ : RigidNames) (s : String) : String :=
  σ.foldl (fun acc p => acc.replace p.2 p.1) s

/-- Write each generated name in a rendered type as `_`: a name with a reserved prefix that
    `known` does not register. -/
def hideGeneratedNames (known : KnownTypes) (s : String) : String :=
  let isNameChar (c : Char) : Bool := c.isAlphanum || c == '_' || c == '$' || c == '\''
  let hide (tok : String) : String :=
    if isAllowedName tok || known.containsName tok then tok else "_"
  let (out, tok) := s.toList.foldl
    (fun (acc : String × String) c =>
      if isNameChar c then (acc.1, acc.2.push c) else ((acc.1 ++ hide acc.2).push c, ""))
    ("", "")
  out ++ hide tok

mutual
/-- Write each type constructor of `mty` that has a reserved prefix and that `known` does not
    register as `_`. -/
def hideGeneratedTyCons (known : KnownTypes) : LMonoTy → LMonoTy
  | .ftvar x => .ftvar x
  | .tcons n args =>
    .tcons (if isAllowedName n || known.containsName n then n else "_")
      (hideGeneratedTyConsList known args)
  | .bitvec n => .bitvec n

/-- `hideGeneratedTyCons` on each of `mtys`. -/
def hideGeneratedTyConsList (known : KnownTypes) : LMonoTys → LMonoTys
  | [] => []
  | ty :: rest => hideGeneratedTyCons known ty :: hideGeneratedTyConsList known rest
end

/-- `s` with `hideGeneratedNames` applied to the unifier's report, from
    "Impossible to unify " or "Failed occurs check: " on. The rest of `s`
    may show terms, whose names stay as written. -/
def hideUnifierGeneratedNames (known : KnownTypes) (s : String) : String :=
  let split? (mark : String) : Option (String × String) :=
    match s.splitOn mark with
    | pre :: rest@(_ :: _) => some (pre, mark ++ mark.intercalate rest)
    | _ => none
  match ["Impossible to unify ", "Failed occurs check: "].findSome? split? with
  | some (pre, report) => pre ++ hideGeneratedNames known report
  | none => s

/-- A "refined to" message if a unification-failure message reports a rigid type parameter
    unified with another type; else `none`. Generated names are hidden unless `known` registers
    them. -/
def refineErrorMsg? (known : KnownTypes) (typeArgs : List String) (s : String) :
    Option String :=
  let seg :=
    match (s.splitOn "First mismatch: ")[1]? with
    | some t => t
    | none =>
      match (s.splitOn "Impossible to unify ")[1]? with
      | some t => t
      | none => s
  let core := ((seg.splitOn ".").headD seg)
  match core.splitOn " with " with
  | [x, y] =>
    if typeArgs.contains x then
      some s!"Rigid type variable '{x}' was refined to '{hideGeneratedNames known y}'"
    else if typeArgs.contains y then
      some s!"Rigid type variable '{y}' was refined to '{hideGeneratedNames known x}'"
    else none
  | _ => none

/-- Deskolemize an error `Format`, rewriting a rigid-parameter refinement as a "refined to"
    message, against the registered types `known`. -/
def reformatError (known : KnownTypes) (σ : RigidNames) (raw : Format) : Format :=
  let s := deskolemizeStr σ (toString raw)
  match refineErrorMsg? known (σ.map Prod.fst) s with
  | some clean => Std.format clean
  | none => Std.format (hideUnifierGeneratedNames known s)

/-- A "refined to" message if `err` reports a rigid type parameter of `σ` unified with another
    type; else `none`. Generated type variables, and generated type constructors that `known`
    does not register, are hidden in the other type. -/
def refineUnifyError? (known : KnownTypes) (σ : RigidNames) (err : UnifyError) :
    Option String :=
  match err with
  | .ImpossibleToUnify (l, r) _ =>
    let refined (param other : LMonoTy) : Option String :=
      match param with
      | .ftvar x =>
        if σ.any (fun p => p.1 == x) then
          let shown := hideGeneratedTyCons known (displayTy Subst.empty other)
          some s!"Rigid type variable '{x}' was refined to '{format shown}'"
        else none
      | _ => none
    let l' := deskolemizeTy σ l
    let r' := deskolemizeTy σ r
    (refined l' r').orElse (fun _ => refined r' l')
  | .FailedOccursCheck .. => none

/-- Deskolemize a failure of `resolveWithType`, reporting a unification failure of a rigid
    type parameter from its types rather than its rendered text. -/
def reformatResolveError (known : KnownTypes) (σ : RigidNames) :
    ResolveWithTypeError → Format
  | .resolveFailed e => reformatError known σ e
  | .unifyFailed err _ =>
    match refineUnifyError? known σ err with
    | some clean => Std.format clean
    | none => reformatError known σ (format err)

/-- The message for `what`, a parameter or local variable, named like a
    function or a constant. -/
def nameClashMsg (what : String) : Format :=
  f!"{what} collides with a function or constant of the same name"

/-- Check a signature's names: distinct type parameters `typeArgs` that cover the signature's
    type variables `sigVars`, and parameters not named like a function, that is, a name
    satisfying `isFunction`. Messages start with `kind` and `name`. -/
def checkSignatureNames (isFunction : String → Prop) [DecidablePred isFunction]
    (kind name : String) (typeArgs sigVars : List String) (params : List CoreIdent) :
    Except Format Unit := do
  checkTypeArgsNodup s!"{kind} '{name}'" typeArgs
  let undeclared := (sigVars.filter (fun v => !typeArgs.contains v)).eraseDups
  if !undeclared.isEmpty then
    throw f!"{kind} '{name}': type variables {undeclared} appear in the signature but are not \
             declared in typeArgs {typeArgs}"
  for id in params do
    if isFunction id.name then
      throw f!"{kind} '{name}': {nameClashMsg s!"parameter '{id.name}'"}"

/-- A scope binding each `(id, mty)` at its skolemized monotype. -/
def skolemScope (σ : RigidNames) (sig : @LMonoTySignature Unit) :
    Strata.Util.HMap CoreIdent LTy :=
  Strata.Util.HMap.ofList (sig.map (fun (id, mty) => (id, LTy.forAll [] (skolemizeTy σ mty))))

/-- Resolve the aliases of each of `tys` in order, rejecting with `errf ty` a type `ty` that does
    not resolve to an instance of a registered type. -/
def resolveKnownTys (C : Core.Expression.TyContext) (errf : LMonoTy → Format) (tys : LMonoTys)
    (Env : Core.Expression.TyEnv) : Except Format (LMonoTys × Core.Expression.TyEnv) :=
  tys.foldlM
    (fun (acc : LMonoTys × Core.Expression.TyEnv) (ty : LMonoTy) => do
      let (ty', Env) ← LMonoTy.resolveAliases ty acc.2
      if !isInstanceOfKnownType ty' C then
        throw (errf ty)
      .ok (acc.1 ++ [ty'], Env))
    ([], Env)

namespace Function

open Lambda Imperative
open Std (ToFormat Format format)

/-- Report every free variable of the skolemized expression `eSk` that `Env` does not bind; the
    message shows `src`, the written expression. -/
def checkFreeVars (C : Core.Expression.TyContext) (Env : Core.Expression.TyEnv)
    (σ : RigidNames) (src : Format) (eSk : Core.Expression.Expr) : Except Format Unit :=
  (Env.freeVarCheck eSk (fun _ => f!"[{src}]")).mapError (reformatError C.knownTypes σ)

/-- Check that proposition `e` (shown in messages as `src`) has type `bool` and that every
    annotation type variable in it is in `rigid`, holding the type parameters of `σ` rigid;
    return it elaborated and deskolemized, with whether every stored annotation satisfies
    `ok`. -/
def checkBoolProp (C : Core.Expression.TyContext) (Env : Core.Expression.TyEnv)
    (rigid : List TyIdentifier) (σ : RigidNames) (src : Format) (ok : LMonoTy → Bool)
    (e : Core.Expression.Expr) :
    Except Format (Core.Expression.Expr × Bool × Core.Expression.TyEnv) := do
  if let some msg := WrittenTyVarScope.unboundAnnotMsg? false rigid [] [e] then
    throw msg
  let eSk := if σ.isEmpty then e else skolemizeBody none σ e
  let (et, EnvR) ← SourceExpr.orFreeVarError (fun _ => checkFreeVars C Env σ src eSk)
    ((resolveWithType C Env eSk LMonoTy.bool).mapError
      (reformatResolveError C.knownTypes σ))
  let (out, stored) := finishStored σ EnvR.stateSubstInfo.subst ok et
  .ok (out, stored, EnvR)

/-- The names of the free variables of `eT` that are not formals of `sig`. -/
def nonInputVars (sig : @LMonoTySignature Unit) (eT : LExprT CoreLParams.mono) : List String :=
  ((LExpr.LExpr.getVars eT).map (·.name)).filter (fun n => !(sig.map (·.1.name)).contains n)

/-- `Env` with a pushed scope binding each formal at its skolemized type. -/
def formalsEnv (Env : Core.Expression.TyEnv) (σ : RigidNames)
    (formals : @LMonoTySignature Unit) : Core.Expression.TyEnv :=
  (Env.pushEmptyContext).addInNewestContext (T := CoreLParams) (skolemScope σ formals)

/-- Close a formal scope: `resolved`'s inference state with `ambient`'s context. -/
private def closeFormals
    (ambient resolved : Core.Expression.TyEnv) : Core.Expression.TyEnv :=
  resolved.updateContext ambient.context

/-- The type names a function mentions, given the types `annot` it writes: those of its
    signature, the type constructor names of `annot`, and those of its literals' types. -/
def tyNames (func : Function) (annot : List LMonoTy) : List String :=
  sigTyNames func.output func.inputs.values ++ annot.flatMap getTypeRefs ++
    func.exprs.flatMap exprLitTyNames

/-- The rigid renaming chosen for the type parameters of function `func` checked in `C`: its
    constants avoid the registered types, the names of `scope`, and the type names
    `tyNames ()` of `func`. -/
def rigidNames (scope : Thunk (Std.HashSet String)) (C : Core.Expression.TyContext)
    (func : Function) (tyNames : Unit → List String) : RigidNames :=
  rigidNamesAvoiding C scope (Thunk.pure ∅) func.name.name tyNames func.typeArgs

/-- The type a measure is checked at: a bare formal of a datatype type at its own type, every
    other measure at `int`. -/
def measureTy (C : Core.Expression.TyContext) (sig : @LMonoTySignature Unit)
    (m : Core.Expression.Expr) : LMonoTy :=
  match m with
  | .fvar _ x _ =>
    match sig.find? x with
    | some (.tcons n args) => if (C.datatypes.getType n).isSome then .tcons n args else .int
    | _ => .int
  | _ => .int

/-- Elaborate expression `e` of function `name` in a fresh formal scope against `expected`. -/
private def resolvePosition
    (C : Core.Expression.TyContext) (Env : Core.Expression.TyEnv) (name : String)
    (sk : RigidNames) (sig : @LMonoTySignature Unit) (e : Core.Expression.Expr)
    (expected : LMonoTy) (typeErr : ResolveWithTypeError → Format) :
    Except Format (LExprT CoreLParams.mono × Core.Expression.TyEnv) := do
  let eSk := if sk.isEmpty then e else skolemizeBody (some name) sk e
  let mkBodyEnv := formalsEnv Env sk sig
  let (eT, eEnv) ←
    SourceExpr.orFreeVarError (fun _ => checkFreeVars C mkBodyEnv sk (format e) eSk)
      ((resolveWithType C mkBodyEnv eSk expected).mapError typeErr)
  .ok (eT, closeFormals Env eEnv)

/-- Check expression `e` of function `name` in a fresh formal scope against `expected`,
    rejecting any non-formal it reads. -/
private def checkPosition
    (C : Core.Expression.TyContext) (Env : Core.Expression.TyEnv) (name : String)
    (sk : RigidNames) (sig : @LMonoTySignature Unit) (e : Core.Expression.Expr)
    (expected : LMonoTy) (typeErr : ResolveWithTypeError → Format)
    (extraErr : List String → Format) :
    Except Format (LExprT CoreLParams.mono × Core.Expression.TyEnv) := do
  let (eT, Env') ← resolvePosition C Env name sk sig e expected typeErr
  let extra := nonInputVars sig eT
  if !extra.isEmpty then
    throw (extraErr extra)
  .ok (eT, Env')

/-- Check preconditions in order, threading the inference state. -/
private def checkPreconditions
    (C : Core.Expression.TyContext) (Env : Core.Expression.TyEnv) (name : String)
    (sk : RigidNames) (sig : @LMonoTySignature Unit) :
    List (Strata.DL.Util.FuncPrecondition Core.Expression.Expr Core.Expression.ExprMetadata) →
      Except Format
        (List (Core.Expression.ExprMetadata × LExprT CoreLParams.mono) × Core.Expression.TyEnv)
  | [] => .ok ([], Env)
  | p :: ps => do
    let (pT, Env') ← checkPosition C Env name sk sig p.expr LMonoTy.bool
      (reformatResolveError C.knownTypes sk)
      (fun extra => f!"Function '{name}': precondition uses variables {extra} that are not inputs")
    let (psT, Env'') ← checkPreconditions C Env' name sk sig ps
    .ok ((p.md, pT) :: psT, Env'')

/-- Check axioms in order, threading the inference state. -/
private def checkAxioms
    (C : Core.Expression.TyContext) (Env : Core.Expression.TyEnv) (name : String)
    (sk : RigidNames) (sig : @LMonoTySignature Unit) :
    List Core.Expression.Expr →
      Except Format (List (LExprT CoreLParams.mono) × Core.Expression.TyEnv)
  | [] => .ok ([], Env)
  | ax :: axs => do
    let (axT, Env') ← resolvePosition C Env name sk sig ax LMonoTy.bool
      (reformatResolveError C.knownTypes sk)
    let (axsT, Env'') ← checkAxioms C Env' name sk sig axs
    .ok (axT :: axsT, Env'')

/-- Check the optional function body in a fresh formal scope. -/
private def checkBody
    (C : Core.Expression.TyContext) (Env : Core.Expression.TyEnv) (func : Function)
    (outR : LMonoTy) (sk : RigidNames) (sig : @LMonoTySignature Unit) :
    Except Format (Option (LExprT CoreLParams.mono) × Core.Expression.TyEnv) :=
  match func.body with
  | none => .ok (none, Env)
  | some body => do
    let (bodyT, Env') ← checkPosition C Env func.name.name sk sig body (skolemizeTy sk outR)
      (reformatResolveError C.knownTypes sk)
      (fun extra => f!"Function '{func.name.name}': body uses variables {extra} \
                       that are not inputs")
    .ok (some bodyT, Env')

/-- Check the optional measure in a fresh formal scope. -/
private def checkMeasure
    (C : Core.Expression.TyContext) (Env : Core.Expression.TyEnv) (func : Function)
    (sk : RigidNames) (sig : @LMonoTySignature Unit) :
    Except Format (Option (LExprT CoreLParams.mono) × Core.Expression.TyEnv) :=
  match func.measure with
  | none => pure (none, Env)
  | some m => do
    let typeErr : ResolveWithTypeError → Format
      | .resolveFailed e => reformatError C.knownTypes sk e
      | .unifyFailed _ resolvedTy =>
        let gotTy := deskolemizeTy sk resolvedTy
        f!"recursive function '{func.name.name}': decreases expression must have type int \
           or be a parameter of a datatype type, got '{gotTy}'"
    let (mT, Env') ← checkPosition C Env func.name.name sk sig m
      (skolemizeTy sk (measureTy C sig m)) typeErr
      (fun extra => f!"recursive function '{func.name.name}': decreases expression uses \
                       variables {extra} that are not parameters")
    pure (some mT, Env')

/-- The elaborated expression positions, kept until the final substitution is known. -/
private structure CheckedPositions where
  body : Option (LExprT CoreLParams.mono)
  measure : Option (LExprT CoreLParams.mono)
  preconditions : List (Core.Expression.ExprMetadata × LExprT CoreLParams.mono)
  axioms : List (LExprT CoreLParams.mono)
  env : Core.Expression.TyEnv

/-- Check the body, measure, preconditions and axioms in order, threading the inference
    state. -/
private def checkPositions
    (C : Core.Expression.TyContext) (Env : Core.Expression.TyEnv) (func : Function)
    (outR : LMonoTy) (insR : LMonoTys) (sk : RigidNames) :
    Except Format CheckedPositions := do
  let name := func.name.name
  let sig := func.inputs.keys.zip insR
  let (bodyT, Env) ← checkBody C Env func outR sk sig
  let (measureT, Env) ← checkMeasure C Env func sk sig
  let (preconditionsT, Env) ← checkPreconditions C Env name sk sig func.preconditions
  let (axiomsT, Env) ← checkAxioms C Env name sk sig func.axioms
  .ok {
    body := bodyT
    measure := measureT
    preconditions := preconditionsT
    axioms := axiomsT
    env := Env
  }

/-- The rejection of function `name` for an expression annotated at an undeclared type
    variable. -/
def storedTyVarMsg (name : String) : Format :=
  f!"Function '{name}': the body, the decreases expression, a precondition or an \
     axiom is typed at a generated type variable that is not declared. Nothing fixes \
     the type of a polymorphic instance there; annotate it, or use a type parameter the \
     signature mentions"

/-- Rename each type parameter of `func` that starts with a reserved prefix to a fresh name,
    throughout the function, and keep the others. The new names avoid the type variables of the
    signature, those of `annot ()` and the type variables in scope in `C` and
    `Env` (`scopeTyVars`). When `annot ()` lists the types the function writes,
    the renamed function means the same. -/
def renameReservedTypeArgs (C : Core.Expression.TyContext) (Env : Core.Expression.TyEnv)
    (func : Function) (annot : Unit → List LMonoTy) : Function :=
  renameReservedWith func.typeArgs
    (fun u => func.mentionedTyVarsIn (annot u) ++ scopeTyVars C Env)
    func.renameTypeArgs func

/-- Check the names of a function signature (`checkSignatureNames`), with `isFunction` the
    names of the functions in scope. -/
def checkHeaderNames (isFunction : String → Prop) [DecidablePred isFunction] (func : Function) :
    Except Format Unit :=
  checkSignatureNames isFunction "Function" func.name.name func.typeArgs
    (LMonoTy.mkArrow' func.output func.inputs.values).freeVars func.inputs.keys

/-- Reject `func` when the context `C` already has a function of its name. -/
def checkNameFresh (C : Core.Expression.TyContext) (func : Function) : Except Format Unit := do
  if func.name.name ∈ C.functions then
    throw f!"Error in function {func.name}: a function of this name already exists."

/-- Check the signature of a `Function` whose signature names passed `checkHeaderNames`: the
    parameter names are distinct, the output and input types resolve to registered types, and
    every type parameter occurs in the resolved signature. Return the resolved output and input
    types. -/
def resolveSignature (C : Core.Expression.TyContext) (Env : Core.Expression.TyEnv)
    (func : Function) : Except Format (LMonoTy × LMonoTys) := do
  let name := func.name.name
  if !(decide func.inputs.keys.Nodup) then
    throw f!"Function '{name}': duplicate parameter names {func.inputs.keys}"
  let (outR, Env) ← LMonoTy.resolveAliases func.output Env
  if !isInstanceOfKnownType outR C then
    throw f!"Function '{name}': signature type {func.output} is not a registered type"
  let (insR, _) ← resolveKnownTys C
    (fun ty => f!"Function '{name}': signature type {ty} is not a registered type")
    func.inputs.values Env
  let sigVars := (LMonoTy.mkArrow' outR insR).freeVars
  let phantomArgs := func.typeArgs.filter (fun a => !sigVars.contains a)
  if !phantomArgs.isEmpty then
    throw f!"Function '{name}': type parameters {phantomArgs} occur in neither an input type \
             nor the output type, so a call could not determine them"
  .ok (outR, insR)

end Function

/-- A function whose signature is checked: the function with its reserved type parameters
    renamed, its resolved output and input types, and the types the function writes, collected
    once, on demand, for both the renaming and the rigid constants of its body check. -/
structure CheckedSignature where
  func : Function
  output : LMonoTy
  inputs : LMonoTys
  annot : Thunk (List LMonoTy)

/-- The type names the renamed function of `sig` mentions. -/
def CheckedSignature.tyNames (sig : CheckedSignature) : Unit → List String :=
  fun _ => sig.func.tyNames sig.annot.get

namespace Function

/-- Rename the reserved type parameters of `func` (`renameReservedTypeArgs`) and resolve the
    signature of the renamed function (`resolveSignature`). -/
def renameAndResolve (C : Core.Expression.TyContext) (Env : Core.Expression.TyEnv)
    (func : Function) : Except Format CheckedSignature := do
  let annot := Thunk.mk fun _ => func.annotTys
  let renamed := renameReservedTypeArgs C Env func fun _ => annot.get
  let (output, inputs) ← resolveSignature C Env renamed
  pure { func := renamed, output, inputs, annot }

/-- Type check the expressions of a `Function` whose signature `resolveSignature` resolved to
    output `outR` and inputs `insR`, with its type parameters as rigid constants that avoid the
    names of `scope` and the type names `tyNames ()` of `func`. Return the definition with the
    resolved signature and the deskolemized expressions, and the final environment. -/
def checkDefinition (scope : Thunk (Std.HashSet String)) (C : Core.Expression.TyContext)
    (Env : Core.Expression.TyEnv) (func : Function) (outR : LMonoTy) (insR : LMonoTys)
    (tyNames : Unit → List String) : Except Format (Function × Core.Expression.TyEnv) := do
  let name := func.name.name
  if func.isConstr && func.body.isSome then
    throw f!"Function '{name}': a constructor must not have a body"
  if !func.isRecursive && func.measure.isSome then
    throw f!"Function '{name}': a decreases expression is only allowed on a recursive function"
  if let some msg := WrittenTyVarScope.unboundAnnotMsg? false func.typeArgs [] func.exprs then
    throw f!"Function '{name}': {msg}"
  -- Skolemize the type parameters to constants that name no registered type.
  let sk := Function.rigidNames scope C func tyNames
  let C' := addSkolemTypes C sk
  let positions ← checkPositions C' Env func outR insR sk
  let S := positions.env.stateSubstInfo.subst
  -- Every position is stored under the final substitution, annotated only at declared type
  -- parameters.
  let finishExpr := finishStored sk S (tyVarsIn func.typeArgs)
  let bodyF := positions.body.map finishExpr
  let measureF := positions.measure.map finishExpr
  let preconditionsF := positions.preconditions.map fun (md, pT) => (md, finishExpr pT)
  let axiomsF := positions.axioms.map finishExpr
  if !(bodyF.all (·.2) && measureF.all (·.2) && preconditionsF.all (·.2.2) &&
      axiomsF.all (·.2)) then
    throw (storedTyVarMsg name)
  let inputsR := func.inputs.keys.zip insR
  let out := { func with inputs := inputsR, output := outR, body := bodyF.map (·.1),
                         preconditions := preconditionsF.map fun (md, e) =>
                           { expr := e.1, md := md },
                         axioms := axiomsF.map (·.1), measure := measureF.map (·.1) }
  .ok (out, positions.env)

/-- Type check a `Function` after renaming its reserved type parameters, with rigid constants
    that avoid the names of `scope`; return the renamed function and the checked one. The set
    `scope` is evaluated only for a polymorphic function. The signature names are first checked
    as written, so that a message shows the names the user wrote. -/
def typeCheckIn (scope : Thunk (Std.HashSet String)) (C : Core.Expression.TyContext)
    (Env : Core.Expression.TyEnv) (func : Function) : Except Format (Function × Function) := do
  checkHeaderNames (· ∈ C.functions) func
  let sig ← renameAndResolve C Env func
  let (func', _) ← checkDefinition scope C Env sig.func sig.output sig.inputs sig.tyNames
  .ok (sig.func, func')

/-- Type check a `Function` (`typeCheckIn`) with rigid constants that avoid the type names in
    scope in `C` and `Env`, returning the input environment unchanged. -/
def typeCheck (C: Core.Expression.TyContext) (Env : Core.Expression.TyEnv) (func : Function) :
    Except Format (Function × Core.Expression.TyEnv) := do
  let (_, func') ← typeCheckIn (scopeTyNameThunk C Env) C Env func
  .ok (func', Env)

end Function

namespace PureFunc

open Lambda Imperative
open Std (ToFormat Format format)

/--
Type check a `PureFunc Expression` with `Function.typeCheck`. Return `decl` with the checked
type parameters, signature and expressions of the type-checked `Function` (aliases resolved,
reserved type parameters renamed), that `Function`, and the environment. Every other field of
`decl` is kept.
-/
def typeCheck (C: Core.Expression.TyContext) (Env : Core.Expression.TyEnv)
    (decl : PureFunc Expression) :
    Except Format (PureFunc Expression × Function × Core.Expression.TyEnv) := do
  let funcData ← Function.ofPureFunc decl
  let (func', Env') ← Function.typeCheck C Env funcData
  let decl' : PureFunc Expression :=
    { decl with
      typeArgs := func'.typeArgs
      inputs := func'.inputs.map fun (id, mty) => (id, .forAll [] mty)
      output := .forAll [] func'.output
      body := func'.body
      axioms := func'.axioms
      preconditions := func'.preconditions
      measure := func'.measure }
  .ok (decl', func', Env')

end PureFunc

---------------------------------------------------------------------

end Core

end -- public section
