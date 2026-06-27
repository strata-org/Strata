/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataPython.Specs.Decls
public import StrataPython.Specs.Decorators

/-! # Native PySpec contract decorators

Recognizes PySpec's own first-class contract decorators on stub declarations:

- `@requires(lambda <params>: <predicate>)` — a precondition.
- `@ensures(lambda <params>: <predicate>)` — a postcondition (the binder
  `result` denotes the return value).
- `@modifies(lambda <params>: <target>)` — a frame target (an lvalue expression).
- `@snapshot(lambda <params>: <capture>, name="n")` — a pre-state capture,
  referenced inside `@ensures` as `OLD.n`.
- `@ghost(name="g", type=…, init=…)` — a spec-only ghost variable.

`@invariant(lambda self: <predicate>)` lives on the class scheme (`classScheme`)
rather than the per-method scheme.

These are *native* markers: unqualified decorator names (no `icontract.`
qualifier). Recognition derives from the generic `Specs/Decorators.lean`
framework — this module builds `DecoratorScheme` values that pattern-match the
decorator forms and collect the raw Python lambda bodies into a bundle. The spec
parser (`Specs.lean`) then translates those bodies into `SpecExpr`/`Assertion`
via the same `transExpr` machinery used for `assert` statements, and routes them
into the appropriate function fields — `preconditions` (`@requires`),
`postconditions` (`@ensures`), `modifies`, `snapshots`, and `ghosts` — or, for
`@invariant`, into the class's `invariants`.

Depending only on the framework and the `PySpecMClass` diagnostic interface
keeps recognition decoupled from the full pipeline. -/

namespace StrataPython.Specs.Native

open StrataDDM (SourceRange)
open PySpecMClass (specError specWarning)
open Decorators (DecoratorForm DecoratorScheme expectLambda? warnUnknownBinders
  stringKeyword? exprKeyword? hasKeyword reportUnexpectedKeywords)

/-! ## Bundles produced by recognition -/

/-- A `@snapshot` capture before its body is translated: the declared name, the
    raw Python capture expression, and the decorator's source location. -/
public structure RawSnapshot where
  name : String
  capture : expr SourceRange
  loc : SourceRange
deriving Inhabited

/-- A `@ghost(name="g", type=…, init=…)` declaration before its `type`/`init`
    expressions are resolved: the declared name, the raw (optional) Python type
    annotation and initializer expressions, and the decorator's source range. -/
public structure RawGhost where
  name : String
  type : Option (expr SourceRange) := none
  init : Option (expr SourceRange) := none
  loc : SourceRange
deriving Inhabited

/-- Native contract decorators recognized on a single function/method, with
    lambda bodies still as raw Python expressions (translated later, in the spec
    parser, under the assertion-building monad). -/
public structure MethodBundle where
  /-- `@requires` lambda bodies (preconditions). -/
  requires : Array (expr SourceRange) := #[]
  /-- `@ensures` lambda bodies (postconditions). -/
  ensures : Array (expr SourceRange) := #[]
  /-- `@modifies` lambda bodies (frame targets — lvalue expressions). -/
  modifies : Array (expr SourceRange) := #[]
  /-- `@snapshot(lambda …: capture, name="n")` pre-state captures. -/
  snapshots : Array RawSnapshot := #[]
  /-- `@ghost(name="g", …)` declarations. -/
  ghosts : Array RawGhost := #[]
deriving Inhabited

/-! ## Recognition scheme -/

/-- Binder naming the procedure's return value inside an `@ensures` lambda. -/
public def resultBinder : String := "result"

/-- The `DecoratorScheme` for native contract decorators on a function/method.
    `validParams` is the function's parameter list, captured to flag lambda
    binders that bind nothing at the use site (a vacuous predicate).

    Only unqualified *call* decorators are considered here; bare markers such as
    `@overload` are declined (the framework's no-op-on-decline contract leaves
    them for the existing overload handling). -/
public def methodScheme {m : Type → Type} [Monad m] [PySpecMClass m]
    (validParams : Array String) : DecoratorScheme m MethodBundle where
  init := {}
  absorb form bundle := do
    unless form.qualifier == none && form.isCall do return (false, bundle)
    match form.name with
    | "requires" =>
      let some (body, binders) ← expectLambda? specError "@requires" form.loc form.args
        | return (true, bundle)
      reportUnexpectedKeywords specError "@requires" #[] form.kwargs
      warnUnknownBinders form.loc binders validParams fun n =>
        s!"@requires: lambda parameter '{n}' matches no function parameter; it is unbound at the use site"
      return (true, { bundle with requires := bundle.requires.push body })
    | "ensures" =>
      let some (body, binders) ← expectLambda? specError "@ensures" form.loc form.args
        | return (true, bundle)
      reportUnexpectedKeywords specError "@ensures" #[] form.kwargs
      warnUnknownBinders form.loc binders (validParams.push resultBinder) fun n =>
        s!"@ensures: lambda parameter '{n}' matches no function parameter or '{resultBinder}'; it is unbound at the use site"
      return (true, { bundle with ensures := bundle.ensures.push body })
    | "modifies" =>
      -- `@modifies(lambda <params>: <target>)`: a frame target the procedure
      -- may modify. The lambda body is the lvalue expression (e.g. a parameter
      -- name, or `self.x`); translated to a `SpecExpr` by the spec parser.
      let some (body, binders) ← expectLambda? specError "@modifies" form.loc form.args
        | return (true, bundle)
      reportUnexpectedKeywords specError "@modifies" #[] form.kwargs
      warnUnknownBinders form.loc binders validParams fun n =>
        s!"@modifies: lambda parameter '{n}' matches no function parameter; it is unbound at the use site"
      return (true, { bundle with modifies := bundle.modifies.push body })
    | "snapshot" =>
      -- `@snapshot(lambda <params>: capture, name="n")`: a pre-state capture,
      -- referenced inside `@ensures` as `OLD.n`. Requires a string-literal
      -- `name=` and a capture lambda.
      let name? ← stringKeyword? "@snapshot" "name" form.kwargs
      reportUnexpectedKeywords specError "@snapshot" #["name"] form.kwargs
      let some (body, binders) ← expectLambda? specError "@snapshot" form.loc form.args
        | return (true, bundle)
      let some name := name?
        | -- `stringKeyword?` already reported a non-string `name=`; only flag a
          -- genuinely absent one here, to avoid a duplicate diagnostic.
          unless hasKeyword "name" form.kwargs do
            specError form.loc "@snapshot requires a name= keyword argument"
          return (true, bundle)
      warnUnknownBinders form.loc binders validParams fun n =>
        s!"@snapshot: lambda parameter '{n}' matches no function parameter; it is unbound at the use site"
      if bundle.snapshots.any (·.name == name) then
        specError form.loc s!"@snapshot: duplicate name=\"{name}\"; snapshot names must be unique within a method"
        return (true, bundle)
      return (true, { bundle with snapshots := bundle.snapshots.push { name, capture := body, loc := form.loc } })
    | "ghost" =>
      -- `@ghost(name="g", type=…, init=…)`: a spec-only ghost variable. The name
      -- is a required string-literal keyword; `type=`/`init=` are optional raw
      -- expressions (a type annotation and an initializer) resolved later by the
      -- spec parser.
      let name? ← stringKeyword? "@ghost" "name" form.kwargs
      let type? ← exprKeyword? "@ghost" "type" form.kwargs
      let init? ← exprKeyword? "@ghost" "init" form.kwargs
      reportUnexpectedKeywords specError "@ghost" #["name", "type", "init"] form.kwargs
      unless form.args.isEmpty do
        specError form.loc "@ghost takes no positional arguments (use name=, type=, init=)"
      let some name := name?
        | unless hasKeyword "name" form.kwargs do
            specError form.loc "@ghost requires a name= keyword argument"
          return (true, bundle)
      if bundle.ghosts.any (·.name == name) then
        specError form.loc s!"@ghost: duplicate name=\"{name}\"; ghost names must be unique within a declaration"
        return (true, bundle)
      let g : RawGhost := { name, type := type?, init := init?, loc := form.loc }
      return (true, { bundle with ghosts := bundle.ghosts.push g })
    | _ =>
      return (false, bundle)

/-- The sole binder permitted on an `@invariant` lambda. -/
public def selfBinder : String := "self"

/-- Native contract decorators recognized on a class (currently invariants),
    with predicate lambda bodies still as raw Python expressions. -/
public structure ClassBundle where
  /-- `@invariant(lambda self: pred)` lambda bodies. -/
  invariants : Array (expr SourceRange) := #[]
deriving Inhabited

/-- The `DecoratorScheme` for `@invariant(lambda self: …)` on a class. The lambda
    must take exactly one `self` binder. Declines anything else (e.g.
    `@exhaustive`) so the caller's existing handling applies. -/
public def classScheme {m : Type → Type} [Monad m] [PySpecMClass m]
    : DecoratorScheme m ClassBundle where
  init := {}
  absorb form bundle := do
    unless form.qualifier == none && form.isCall && form.name == "invariant" do
      return (false, bundle)
    let some (body, binders) ← expectLambda? specError "@invariant" form.loc form.args
      | return (true, bundle)
    reportUnexpectedKeywords specError "@invariant" #[] form.kwargs
    match binders with
    | #[b] =>
      if b == selfBinder then
        return (true, { bundle with invariants := bundle.invariants.push body })
      specWarning form.loc s!"@invariant: lambda binder must be '{selfBinder}', got '{b}'; invariant skipped"
      return (true, bundle)
    | _ =>
      specWarning form.loc s!"@invariant: lambda must take exactly one '{selfBinder}' parameter; invariant skipped"
      return (true, bundle)

end StrataPython.Specs.Native
