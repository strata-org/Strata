# Type-variable handling for local functions: levels + rigidity

## Context

Adding local function declarations (`funcDecl` inside a procedure body) surfaced two
related type-soundness bugs:

- **#1395 / #1397 (refinement):** a nested function body *refines* an enclosing
  procedure's type parameter, e.g. `procedure proc<t>(y:t) { function f():int { y } }`
  silently solves `t := int`. Fixed by the rigid-typevar check in `Function.typeCheck`
  (reject if the body's unifier refines any `v ∈ C.rigidTypeVars`).

- **#1399 (generalization):** a nested function *generalizes over* a type variable that
  is free in the ambient context. Concrete witness (abstract syntax; cannot be written in
  concrete syntax because the parser rejects a free tyvar in a `var` annotation):

  ```
  procedure proc() {
    var x : forall a. a;        // preprocess instantiates ∀a away → stores  x : $__ty0
    function f<b>() : b { x }    // body is the ambient x : $__ty0
    var i  : int  := f();        // f recorded as ∀b. b — accepted at int
    var bo : bool := f();        // ...and at bool: one fixed value, two types
  }
  ```

  `f` is recorded as `∀b. b` even though its body is the single fixed value `x : $__ty0`.
  Both calls type-check. Root cause: `Function.typeCheck` generalizes over **every** free
  tyvar of the signature (`typeArgs := monoty.freeVars.eraseDups`, `FunctionType.lean:48`),
  omitting the standard side condition `gen(Γ, τ) = ∀ᾱ. τ` with `ᾱ = ftv(τ) \ ftv(Γ)`.

These are duals: #1395 refines an ambient (rigid) var; #1399 generalizes over an ambient
(non-rigid) var.

## Levels (OCaml-style ranks)

The principled, scalable mechanism for generalization under nested binding scopes is to
associate a **level** (nesting depth) with each type variable:

- `genTyVar` stamps the current level on each fresh var. `$__ty0` from the procedure body
  is level 0; `b`'s var `$__ty1` from inside `function f` is level 1.
- **Unification** of two variables lowers the survivor's level to the `min` of the two
  (a var unified with an outer-scope var is *demoted*). A var may unify with vars at a
  level `<= ` its own; demotion is the normal, sound outcome.
- **Generalization** at a scope boundary of level `n` quantifies exactly the vars with
  level `> n` (introduced *inside* the scope); vars at level `<= n` belong to an enclosing
  scope and are left free.

This is an efficient incremental implementation of `ftv(τ) \ ftv(Γ)`: instead of
recomputing `ftv(Γ)` (expensive), levels track it in O(1).

Applied to #1399: unifying `$__ty1` (level 1) with `$__ty0` (level 0) demotes the survivor
to level 0. At `f`'s generalization boundary only level-`>0` vars generalize, so `b` is not
generalized — `f` becomes monomorphic with output `$__ty0`.

## Levels and rigidity are orthogonal — we need BOTH

| direction | bug | mechanism | action |
|---|---|---|---|
| generalize over ambient var | #1399 | **levels** | exclude from generalization (demote on unify) |
| refine a rigid procedure param | #1395/#1397 | **rigidity** (`C.rigidTypeVars`) | reject the unification |

Levels decide *what may be generalized*; rigidity decides *what may be refined*. A level-0
var is freely solvable by unification — levels only stop it from being *generalized*. A
rigid `t` must *reject* being solved at all. Levels cannot express "this var is a fixed
unknown that may never be solved," so rigidity does not become redundant. (This matches the
reviewer's clarification: levels + the free/rigid distinction, not levels alone.)

## Design decision: signature-violating bodies are an ERROR (not silently monomorphic)

There is a behavioral fork for `f<b>():b { x }` where the body forces `b` to an ambient
type:

- **Pure levels (OCaml-like):** accept it, silently treated as the monomorphic
  `f():$__ty0 { x }` — the `<b>` annotation is redundant, not wrong.
- **Strata's choice: reject it as a type error.**

Rationale: Strata does **not** treat a function signature the way OCaml treats an inferred
type. The declared (polymorphic) signature is taken as **truth** and the body is *required*
to meet it — we do not specialize the signature to fit the body. This is exactly why rigid
type variables exist. So if a body cannot honor the declared polymorphism (because it pins a
declared type parameter to an ambient/concrete type), that is a violation of the signature
contract and must be reported, not silently weakened. This is consistent with the existing
`alphaEquivMap` check, which already rejects a body forcing `f<a>(x:a):a` to `a = int`.

Concretely: a function's own declared type parameters must remain abstract and distinct from
every ambient-free type variable, in either unification direction. If a declared `typeArg`'s
unification variable is identified with (demoted to) an ambient-level var, reject with a
message in the spirit of the existing one, e.g.:

> Function 'f': body constrains type variable 'b' to the ambient type '$__ty0';
> it cannot be generalized as declared.

## Chosen near-term fix: remove polymorphic var-init + check annotation free vars

The team's preferred concrete fix is to forbid polymorphic local bindings and reject free
type variables in var annotations that are not in scope (procedure type parameters). This
closes both routes by which a non-rigid free type variable reaches an ambient binding, and
notably makes the `init` typing rules *simpler* (the `tys`/`boundVars`/`openFull`/
`RigidAnnotCompat` apparatus collapses to a plain `AliasEquiv`, since every var is now a
monotype). Full specification — the two routes, the `CmdType` changes, and the resulting
`CmdTypeSpec` / `CmdTypeSpecProps` simplifications — is in
[`REMOVE_POLY_VAR_INIT.md`](./REMOVE_POLY_VAR_INIT.md).

The levels analysis below remains the principled, longer-term mechanism for generalization
under nested scopes if local functions stay.

## Implementation sketch

Two tiers:

1. **Immediate fix for #1399 (small, unblocks soundness).** Implement the side condition
   locally: in `Function.typeCheck`, after unifying the body against the return type,
   reject if any declared `typeArg`'s instantiation var is unified with a variable in
   `ftv(Env.context.types)`. Equivalently, treat `ftv(Γ)` as rigid-during-body (in addition
   to `C.rigidTypeVars`) and require declared params to stay abstract and disjoint from it.
   This subsumes #1395 for nested decls and keeps genuine polymorphism (`id<a>(x:a):a { x }`,
   whose `a` only touches its own parameter) accepted. Top-level functions unaffected
   (`Env.context.types = []`).

2. **Levels (larger, principled, do if local functions are permanent).** Add a level field
   to type variables (`TState`/tyvar representation), stamp it in `genTyVar`, demote on the
   var-var case in `Constraints.unify`/`unifyOne`, and generalize-by-level at the function /
   procedure / program boundaries. Keep `rigidTypeVars` for the refinement direction. Under
   Strata's "signature-as-truth" decision, the generalization boundary additionally *errors*
   (rather than silently demoting) when a declared param's var was demoted below the
   function's level.

## Soundness-proof impact

`Function.typeCheck_sound` as currently stated is **false** until #1399 is fixed (the spec
accepts the unsound program). The spec had assumed every ambient free tyvar is rigid
(`h_ambient_rigid`), which #1399 disproves. After the fix, the body can no longer pin a
declared param to an ambient var, restoring the property the proof needs (and removing the
need for the false `h_ambient_rigid` hypothesis; ambient bindings are monomorphic
(`ContextMono`) and the substituted-context formulation handles the rest).

## Witnesses / tests

- `StrataTest/Languages/Core/Examples/AmbientTyvarGenProbe.lean` — the #1399 exploit (nested
  fn generalized to `∀b. b`, callable at both `int` and `bool`).
- `StrataTest/Languages/Core/Examples/MonoLocalBindingTest.lean` — confirms local `var`
  bindings are monomorphic by design: `var x : ∀a. a→a := \y.y` cannot be applied at two
  different types (`int` then `bool` fails to unify).
- `StrataTest/Languages/Core/Examples/NestedFuncDeclTyvarBug.lean` — the #1395 refinement
  cases (rejected) plus a monomorphic nested fn (accepted).
