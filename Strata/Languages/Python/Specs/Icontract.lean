/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Python.Specs.Decls
public import Strata.Languages.Python.Specs.Error
public import Strata.Languages.Python.ReadPython

/-! # icontract decorator surface for PySpec

Recognizes `@icontract.{require,ensure,invariant,snapshot}` decorators
on PySpec functions and classes; `OLD.<name>` inside `@ensure` lambdas
resolves against `@snapshot` captures.

Recognition produces lightweight bundles whose Python AST bodies are
translated later by `Specs.lean` under the right `SpecAssertionM`
context. Diagnostics flow through `warn` / `err` callbacks so this
module avoids a cyclic import on `PySpecMClass`.
-/

namespace Strata.Python.Specs.Icontract

open Strata.Python.Specs

public structure MethodBundle where
  requires  : Array (expr SourceRange) := #[]
  ensures   : Array (expr SourceRange) := #[]
  snapshots : Array (String × expr SourceRange × SourceRange) := #[]
deriving Inhabited

public def MethodBundle.snapshotNameSet (b : MethodBundle) : Std.HashSet String :=
  b.snapshots.foldl (init := {}) fun s (n, _, _) => s.insert n

public structure ClassBundle where
  invariants : Array (expr SourceRange) := #[]
deriving Inhabited

private def lambdaParamNames (lamArgs : arguments SourceRange) : Array String :=
  let .mk_arguments _ _ ⟨_, lamPos⟩ _ ⟨_, lamKwonly⟩ _ _ _ := lamArgs
  (lamPos ++ lamKwonly).map fun a => let .mk_arg _ ⟨_, n⟩ _ _ := a; n

private def asIcontractCall? (attr : String) (pyd : expr SourceRange)
    : Option (SourceRange × Array (expr SourceRange) × Array (keyword SourceRange)) :=
  match pyd with
  | .Call loc (.Attribute _ (.Name _ ⟨_, "icontract"⟩ (.Load _)) ⟨_, a⟩ (.Load _))
      ⟨_, args⟩ ⟨_, kwargs⟩ =>
    if a == attr then some (loc, args, kwargs) else none
  | _ => none

/-- Pull the lambda body + binder names from `args[0]`. On a missing or
    wrong-shape arg, report the failure (severity chosen by caller) and
    return `none`. -/
private def expectLambda? {m : Type → Type} [Monad m]
    (report : SourceRange → String → m Unit)
    (deco : String) (loc : SourceRange) (args : Array (expr SourceRange))
    : m (Option (expr SourceRange × Array String)) := do
  if h : args.size ≥ 1 then
    match args[0] with
    | .Lambda _ lamArgs lamBody => return some (lamBody, lambdaParamNames lamArgs)
    | _ => report loc s!"icontract.{deco} expects a lambda argument"; return none
  else
    report loc s!"icontract.{deco} requires at least one argument"
    return none

private def warnUnknownBinders {m : Type → Type} [Monad m]
    (warn : SourceRange → String → m Unit)
    (loc : SourceRange) (binders allowed : Array String)
    (msg : String → String) : m Unit := do
  for n in binders do
    unless allowed.contains n do warn loc (msg n)

/-- Pull the `name="..."` kwarg out of a `@snapshot` call. Reports
    duplicate `name=`, non-literal values, and unexpected kwargs. -/
private def parseSnapshotName? {m : Type → Type} [Monad m]
    (err : SourceRange → String → m Unit)
    (kwargs : Array (keyword SourceRange)) : m (Option String) := do
  let mut name : Option String := none
  let mut sawNameKw := false
  for kw in kwargs do
    match kw.arg with
    | ⟨_, some ⟨_, "name"⟩⟩ =>
      if sawNameKw then
        err kw.value.ann "icontract.snapshot: duplicate name= kwarg on a single @snapshot"
      sawNameKw := true
      match kw.value with
      | .Constant _ (.ConString _ ⟨_, n⟩) _ => name := some n
      | _ => err kw.value.ann "icontract.snapshot: name= must be a string literal"
    | ⟨_, some ⟨_, kwName⟩⟩ =>
      err kw.value.ann s!"icontract.snapshot: unexpected keyword '{kwName}'"
    | _ => pure ()
  return name

public def absorbMethodDecorator {m : Type → Type} [Monad m]
    (warn : SourceRange → String → m Unit)
    (err  : SourceRange → String → m Unit)
    (validParams : Array String)
    (bundle : MethodBundle) (pyd : expr SourceRange)
    : m (Bool × MethodBundle) := do
  if let some (loc, args, _) := asIcontractCall? "require" pyd then
    let some (body, binders) ← expectLambda? warn "require" loc args
      | return (true, bundle)
    warnUnknownBinders warn loc binders validParams fun n =>
      s!"icontract.require: lambda parameter '{n}' does not match any function parameter; predicate will be vacuous"
    return (true, { bundle with requires := bundle.requires.push body })
  if let some (loc, args, _) := asIcontractCall? "ensure" pyd then
    let some (body, binders) ← expectLambda? warn "ensure" loc args
      | return (true, bundle)
    warnUnknownBinders warn loc binders (validParams ++ #["result", "OLD"]) fun n =>
      s!"icontract.ensure: lambda parameter '{n}' does not match any function parameter (or 'result'/'OLD'); predicate will be vacuous"
    return (true, { bundle with ensures := bundle.ensures.push body })
  if let some (loc, args, kwargs) := asIcontractCall? "snapshot" pyd then
    let name? ← parseSnapshotName? err kwargs
    let some (body, binders) ← expectLambda? err "snapshot" loc args
      | return (true, bundle)
    let some name := name?
      | err loc "icontract.snapshot requires a name= keyword argument"
        return (true, bundle)
    warnUnknownBinders warn loc binders validParams fun n =>
      s!"icontract.snapshot: lambda parameter '{n}' does not match any function parameter; capture will be vacuous"
    if bundle.snapshots.any (·.1 == name) then
      err loc s!"icontract.snapshot: duplicate name=\"{name}\" — snapshot names must be unique within a method"
      return (true, bundle)
    return (true, { bundle with snapshots := bundle.snapshots.push (name, body, loc) })
  return (false, bundle)

public def resolveOldRef {m : Type → Type} [Monad m]
    (warn : SourceRange → String → m Unit)
    (snapshotNames : Std.HashSet String)
    (snapName : String) (loc : SourceRange) (anyType : SpecType)
    (placeholder : SpecExpr × SpecType) : m (SpecExpr × SpecType) := do
  if snapshotNames.contains snapName then
    return (.snapshotRef snapName (loc := loc), anyType)
  warn loc s!"OLD.{snapName}: no @icontract.snapshot named '{snapName}' on this method"
  return placeholder

public def absorbClassDecorator {m : Type → Type} [Monad m]
    (warn : SourceRange → String → m Unit)
    (bundle : ClassBundle) (pyd : expr SourceRange)
    : m (Bool × ClassBundle) := do
  let some (loc, args, _) := asIcontractCall? "invariant" pyd
    | return (false, bundle)
  let some (body, binders) ← expectLambda? warn "invariant" loc args
    | return (true, bundle)
  match binders with
  | #["self"] => return (true, { bundle with invariants := bundle.invariants.push body })
  | #[other] =>
    warn loc s!"icontract.invariant: lambda binder must be 'self', got '{other}'; invariant skipped"
    return (true, bundle)
  | _ =>
    warn loc "icontract.invariant: lambda must take exactly one 'self' parameter; invariant skipped"
    return (true, bundle)

end Strata.Python.Specs.Icontract
