/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataPython.Specs.Diagnostics
public import StrataPython.ReadPython

/-! # Generic decorator-recognition framework for PySpec

Shared gearing for recognizing PySpec decorator surfaces (`@requires`,
`@ensures`, `@overload`, …): `DecoratorForm` normalizes a decorator expression,
the lambda/keyword helpers parse predicate-bearing calls, and `DecoratorScheme`
is a composable recognizer. Depends only on `PySpecMClass` and the Python AST,
not the spec pipeline. -/

namespace StrataPython.Specs.Decorators

open StrataDDM (SourceRange)
open PySpecMClass (specError specWarning)

/-- A decorator expression normalized across the four surface shapes
    (`@name`, `@mod.name`, `@name(...)`, `@mod.name(...)`). -/
public structure DecoratorForm where
  /-- Qualifier of `@qualifier.name`; `none` for a bare `@name`. -/
  qualifier : Option String
  name : String
  /-- Whether applied as a call (`@name(...)`) or bare (`@name`). -/
  isCall : Bool
  /-- Positional/keyword call args (empty unless `isCall`). -/
  args : Array (expr SourceRange) := #[]
  kwargs : Array (keyword SourceRange) := #[]
  loc : SourceRange
deriving Inhabited

/-- Normalize a decorator expression into a `DecoratorForm`, or `none` if it is
    not a recognized surface shape. -/
public def DecoratorForm.ofExpr? (pyd : expr SourceRange) : Option DecoratorForm :=
  match pyd with
  | .Name loc ⟨_, name⟩ (.Load _) =>
    some { qualifier := none, name, isCall := false, loc }
  | .Attribute loc (.Name _ ⟨_, qual⟩ (.Load _)) ⟨_, attr⟩ (.Load _) =>
    some { qualifier := some qual, name := attr, isCall := false, loc }
  | .Call loc (.Name _ ⟨_, name⟩ (.Load _)) ⟨_, args⟩ ⟨_, kwargs⟩ =>
    some { qualifier := none, name, isCall := true, args, kwargs, loc }
  | .Call loc (.Attribute _ (.Name _ ⟨_, qual⟩ (.Load _)) ⟨_, attr⟩ (.Load _))
      ⟨_, args⟩ ⟨_, kwargs⟩ =>
    some { qualifier := some qual, name := attr, isCall := true, args, kwargs, loc }
  | _ => none

/-- True when this form is `@qualifier.name` (qualified, either call or bare). -/
public def DecoratorForm.isQualified (f : DecoratorForm) (qualifier : String) : Bool :=
  f.qualifier == some qualifier

/-- The positional-only + positional + keyword-only binder names of a lambda's
    argument list. -/
public def lambdaBinderNames (lamArgs : arguments SourceRange) : Array String :=
  let .mk_arguments _ ⟨_, posonly⟩ ⟨_, pos⟩ _ ⟨_, kwonly⟩ _ _ _ := lamArgs
  (posonly ++ pos ++ kwonly).map fun a => let .mk_arg _ ⟨_, n⟩ _ _ := a; n

/-- All parameter names of a function's argument list, including the `*args`
    (vararg) and `**kwargs` (kwarg) names. Used to compute the set of valid
    contract-lambda binders, so a binder matching the function's `**kwargs`
    parameter is not flagged as unbound. -/
public def functionParamNames (a : arguments SourceRange) : Array String :=
  let .mk_arguments _ ⟨_, posonly⟩ ⟨_, pos⟩ ⟨_, vararg⟩ ⟨_, kwonly⟩ _ ⟨_, kwarg⟩ _ := a
  let names := (posonly ++ pos ++ kwonly).map fun arg => let .mk_arg _ ⟨_, n⟩ _ _ := arg; n
  let names := match vararg with
    | some (.mk_arg _ ⟨_, n⟩ _ _) => names.push n
    | none => names
  match kwarg with
    | some (.mk_arg _ ⟨_, n⟩ _ _) => names.push n
    | none => names

/-- Pull the lambda body and its binder names from `args[0]` of a decorator
    call. Reports a failure (severity chosen by the caller via `report`) and
    returns `none` when the argument is missing or is not a lambda. Warns (but
    still succeeds) when there are extra positional arguments after the lambda. -/
public def expectLambda? {m : Type → Type} [Monad m] [PySpecMClass m]
    (report : SourceRange → String → m Unit)
    (what : String) (loc : SourceRange) (args : Array (expr SourceRange))
    : m (Option (expr SourceRange × Array String)) := do
  if h : args.size ≥ 1 then
    match args[0] with
    | .Lambda _ lamArgs lamBody =>
      if args.size > 1 then
        specWarning loc s!"{what} ignores extra positional arguments after the lambda"
      return some (lamBody, lambdaBinderNames lamArgs)
    | _ => report loc s!"{what} expects a lambda as its first argument"; return none
  else
    report loc s!"{what} requires at least one argument"
    return none

/-- Warn about each lambda binder not present in `allowed`; such binders make the
    predicate vacuous because nothing binds them at the use site. -/
public def warnUnknownBinders {m : Type → Type} [Monad m] [PySpecMClass m]
    (loc : SourceRange) (binders allowed : Array String)
    (describe : String → String) : m Unit := do
  for n in binders do
    unless allowed.contains n do specWarning loc (describe n)

/-- Read a required string-literal keyword `name=...` from a decorator call's
    keyword arguments. Reports (via `what`-prefixed errors) a duplicate, a
    non-string-literal value, and returns `none` if absent. -/
public def stringKeyword? {m : Type → Type} [Monad m] [PySpecMClass m]
    (what : String) (key : String) (kwargs : Array (keyword SourceRange))
    : m (Option String) := do
  let mut value : Option String := none
  for kw in kwargs do
    match kw.arg with
    | ⟨_, some ⟨_, k⟩⟩ =>
      if k == key then
        if value.isSome then
          specError kw.value.ann s!"{what}: duplicate {key}= keyword"
        match kw.value with
        | .Constant _ (.ConString _ ⟨_, s⟩) _ => value := some s
        | _ => specError kw.value.ann s!"{what}: {key}= must be a string literal"
    | _ => pure ()
  return value

/-- Read an optional keyword `key=<expr>` whose value may be any expression (used
    for `@ghost(type=…, init=…)`, whose values are resolved later). Reports a
    duplicate via a `what`-prefixed error; returns `none` when the keyword is
    absent. -/
public def exprKeyword? {m : Type → Type} [Monad m] [PySpecMClass m]
    (what : String) (key : String) (kwargs : Array (keyword SourceRange))
    : m (Option (expr SourceRange)) := do
  let mut value : Option (expr SourceRange) := none
  for kw in kwargs do
    match kw.arg with
    | ⟨_, some ⟨_, k⟩⟩ =>
      if k == key then
        if value.isSome then
          specError kw.value.ann s!"{what}: duplicate {key}= keyword"
        value := some kw.value
    | _ => pure ()
  return value

/-- True when a keyword argument named `key` is present (regardless of its
    value). Used to distinguish an absent keyword from one present with an
    invalid value, so the two cases are not double-reported. -/
public def hasKeyword (key : String) (kwargs : Array (keyword SourceRange)) : Bool :=
  kwargs.any fun kw =>
    match kw.arg with
    | ⟨_, some ⟨_, k⟩⟩ => k == key
    | _ => false

/-- Report each keyword argument whose name is not in `allowed`, at a severity
    chosen by the caller via `report`. -/
public def reportUnexpectedKeywords {m : Type → Type} [Monad m]
    (report : SourceRange → String → m Unit)
    (what : String) (allowed : Array String) (kwargs : Array (keyword SourceRange))
    : m Unit := do
  for kw in kwargs do
    match kw.arg with
    | ⟨_, some ⟨_, k⟩⟩ =>
      unless allowed.contains k do
        report kw.value.ann s!"{what}: unexpected keyword '{k}'"
    | _ => pure ()

/-- A first-class decorator recognizer over an accumulator `σ`: an `init` value
    plus an `absorb` step returning `(absorbed, σ')`. Contract: a decline
    (`absorbed = false`) must be a no-op (accumulator unchanged, no diagnostics)
    since `prod`/`run` may offer the form to another scheme; a successful absorb
    owns the form. -/
public structure DecoratorScheme (m : Type → Type) (σ : Type) where
  /-- The empty accumulator before any decorator is seen. -/
  init : σ
  /-- Try to absorb one normalized decorator form (see the type docstring for
      the decline-is-a-no-op contract). -/
  absorb : DecoratorForm → σ → m (Bool × σ)

/-- Compose two schemes over the product accumulator: a form is offered to `a`
    first, and to `b` only if `a` declines. -/
public def DecoratorScheme.prod {m : Type → Type} [Monad m] {σ₁ σ₂ : Type}
    (a : DecoratorScheme m σ₁) (b : DecoratorScheme m σ₂)
    : DecoratorScheme m (σ₁ × σ₂) where
  init := (a.init, b.init)
  absorb form := fun (s₁, s₂) => do
    let (ok₁, s₁') ← a.absorb form s₁
    if ok₁ then return (true, (s₁', s₂))
    let (ok₂, s₂') ← b.absorb form s₂
    return (ok₂, (s₁', s₂'))

/-- Fold a scheme over a decorator list, normalizing each and offering it to the
    scheme; anything not absorbed (or not a recognized shape) goes to
    `onUnknown`. Returns the accumulator. -/
public def DecoratorScheme.run {m : Type → Type} [Monad m] {σ : Type}
    (scheme : DecoratorScheme m σ)
    (decorators : Array (expr SourceRange))
    (onUnknown : expr SourceRange → m Unit) : m σ := do
  let mut acc := scheme.init
  for pyd in decorators do
    match DecoratorForm.ofExpr? pyd with
    | none => onUnknown pyd
    | some form =>
      let (absorbed, acc') ← scheme.absorb form acc
      acc := acc'
      unless absorbed do onUnknown pyd
  return acc

end StrataPython.Specs.Decorators
