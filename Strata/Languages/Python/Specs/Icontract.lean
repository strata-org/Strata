/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Python.Specs.Decls
public import Strata.Languages.Python.Specs.Error
public import Strata.Languages.Python.ReadPython

/-! # icontract decorator surface for PySpec

This module owns the recognition of the [icontract](https://github.com/Parquery/icontract)
library decorators when they appear on PySpec function/class definitions:

  * `@icontract.require`   — caller-side precondition
  * `@icontract.ensure`    — postcondition
  * `@icontract.invariant` — class-level invariant
  * `@icontract.snapshot`  — pre-state value capture (referenced as
                             `OLD.<name>` inside `@ensure`)

`Specs.lean` calls into this module to absorb decorator lists into
bundle structs; translation of the bundle bodies happens later in
`Specs.lean` under the right `SpecAssertionM` context (so the
recursive `transExpr` is in scope).

The public API takes diagnostic callbacks (`warn`, `err`) so this
module doesn't need to depend on `PySpecMClass` (which is defined in
`Specs.lean` and would create a cyclic import).
-/

namespace Strata.Python.Specs.Icontract

open Strata.Python.Specs

/-! ## Method-level bundle -/

/-- Lambda bodies extracted from method-level icontract decorators.
    Bodies are kept as Python AST so the caller can translate them
    later under the right `SpecAssertionM` context. -/
public structure MethodBundle where
  requires : Array (expr SourceRange) := #[]
deriving Inhabited

/-! ## Recognition helpers -/

/-- Extract the lambda parameter names from a Python `Lambda` arguments
    record. Used to validate icontract lambda binders against the
    enclosing function's parameter list. -/
private def lambdaParamNames (lamArgs : arguments SourceRange) : Array String :=
  let .mk_arguments _ _ ⟨_, lamPos⟩ _ ⟨_, lamKwonly⟩ _ _ _ := lamArgs
  (lamPos ++ lamKwonly).map fun a =>
    let .mk_arg _ ⟨_, n⟩ _ _ := a; n

/-- Match the AST shape `@icontract.<attr>(...)` with a non-empty
    argument list; on success return the call's args, kwargs, and
    overall location. -/
private def asIcontractCall? (attr : String) (pyd : expr SourceRange)
    : Option (SourceRange × Array (expr SourceRange) × Array (keyword SourceRange)) :=
  match pyd with
  | .Call loc (.Attribute _ (.Name _ ⟨_, "icontract"⟩ (.Load _)) ⟨_, a⟩ (.Load _))
      ⟨_, args⟩ ⟨_, kwargs⟩ =>
    if a == attr then some (loc, args, kwargs) else none
  | _ => none

/-! ## Method-level absorption -/

/-- Try to absorb a single decorator into the method-level bundle.
    Returns `(absorbed, bundle')`: `absorbed = true` means the
    decorator was an icontract one and the bundle has been updated.
    `validParams` is the enclosing function's parameter names; binders
    that don't match warn (but the predicate is still kept).

    `warn` and `err` are diagnostic callbacks; the caller threads in
    its monadic warning / error reporting (e.g., `specWarning`,
    `specError`). -/
public def absorbMethodDecorator
    {m : Type → Type} [Monad m]
    (warn : SourceRange → String → m Unit)
    (_err : SourceRange → String → m Unit)
    (validParams : Array String)
    (bundle : MethodBundle) (pyd : expr SourceRange)
    : m (Bool × MethodBundle) := do
  -- @icontract.require(lambda <params>: <pred>)
  if let some (_, args, _) := asIcontractCall? "require" pyd then
    if h : args.size ≥ 1 then
      match args[0] with
      | .Lambda _ lamArgs lamBody =>
        for lamName in lambdaParamNames lamArgs do
          unless validParams.contains lamName do
            warn pyd.ann
              s!"icontract.require: lambda parameter '{lamName}' does not match any function parameter; predicate will be vacuous"
        return (true, { bundle with requires := bundle.requires.push lamBody })
      | _ =>
        warn pyd.ann "icontract.require expects a lambda argument"
        return (true, bundle)
    else
      warn pyd.ann "icontract.require requires at least one argument"
      return (true, bundle)
  return (false, bundle)

end Strata.Python.Specs.Icontract
