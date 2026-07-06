# Design: remove polymorphic variable initialization + check annotation free vars

Companion to [`LOCAL_FUNCTION_TYPEVAR_LEVELS.md`](./LOCAL_FUNCTION_TYPEVAR_LEVELS.md),
which analyzes the local-function type-variable bugs (#1395 refinement, #1399
generalization). This doc specifies the concrete fix the team settled on: forbid
polymorphic local bindings and reject free type variables in var annotations.

## The two routes a free type variable enters the ambient context

A nested function can generalize over an ambient type variable (#1399) only because a
free, non-rigid type variable can appear in an ambient binding `Env.context.types`. There
are exactly two routes (both verified empirically with `Statement.typeCheck`):

| route | annotation | mechanism | stored binding |
|---|---|---|---|
| 1 | `var x : ∀a. a` (non-empty binder) | `CmdType.preprocess` instantiates `∀a` to a fresh `$__ty0` | `x : $__ty0` |
| 2 | `var x : a` (`.forAll [] (ftvar "a")`, empty binder, bare free var) | stored verbatim | `x : a` |

(Route 3, inference: `var x : ∀a.a := \y.y` stores `x : ($__ty1 → $__ty1)`. The lambda
binder's inferred type is a fresh var regardless of annotation — but it is bound at the
same scope, so it is not an *ambient-from-an-enclosing-scope* var; closing routes 1 and 2
is what removes the cross-scope hazard.)

**Removing polymorphic var-init closes only route 1.** Route 2 has an empty binder already,
so a "no non-empty binders" rule does nothing to it. Both fixes are required and neither
subsumes the other: route 1 is a *bound*-var problem (instantiation manufactures a fresh
free var); route 2 is a *free*-var problem (the annotation already has one).

## The fix (two parts, in `CmdType`)

### Part A — forbid polymorphic var annotations

`var` annotations must be monomorphic: the declared `LTy` must have an empty binder list.
Reject `var x : ∀a. …` (`xty.boundVars ≠ []`). This removes route 1: `preprocess` no longer
manufactures fresh instantiation vars for local bindings.

### Part B — annotation free vars must be in scope

Mirror the check `Function.typeCheck` already performs on signatures
(`FunctionType.lean:29-32`, rejecting undeclared signature tyvars). In `CmdType.preprocess`
(or `Cmd.init` before `update`), reject if the declared type has any free type variable that
is **not in scope** — i.e. not in `C.rigidTypeVars` (the enclosing procedure's type
parameters; empty at top level):

```
let stray := (LTy.freeVars ty).filter (· ∉ C.rigidTypeVars)
if stray ≠ [] then .error "variable annotation references type variables {stray} that are
                           not procedure type parameters"
```

This removes route 2: a bare free non-rigid tyvar (`var x : a` with no enclosing `proc<a>`)
is rejected. The only free tyvars that survive in an annotation are rigid procedure
parameters (`var x : t` under `proc<t>`), which are already handled by the #1395 rigid
check.

### Resulting invariant

Together A + B guarantee, for every ambient binding `x ↦ ty` in `Env.context.types`:

- **`ty = .forAll [] mty`** (monomorphic — `ContextMono`), and
- **every free var of `mty` is rigid** (`∈ C.rigidTypeVars`).

This is exactly the invariant the function-soundness proof needs — and unlike the discredited
`h_ambient_rigid`, it is now *true* because the typechecker enforces it. #1399 is then
blocked: a nested function cannot generalize over an ambient var, because every ambient free
var is rigid and the #1395 check rejects refining/identifying a declared parameter with one.

## Spec changes (`CmdTypeSpec.lean`) — the spec gets SIMPLER

This is the key payoff: with monomorphic annotations, the polymorphic-instantiation
apparatus in the `init` rules collapses.

Current `init_det` / `init_nondet` (`CmdTypeSpec.lean:53-69`) carry, to model `preprocess`
opening a polymorphic annotation:

```
| init_det : ∀ Γ x (xty : LTy) e mty tys md,
    Γ.types.find? x = none →
    x ∉ HasVarsPure.getVars e →
    tys.length = xty.boundVars.length →
    RigidAnnotCompat Γ.aliases C.rigidTypeVars (LTy.openFull xty tys) mty →
    S.exprTyped C Γ e (S.embed mty) →
    CmdHasType' C Γ (.init x xty (.det e) md)
      { Γ with types := Γ.types.insert x (.forAll [] mty) }
```

With Part A, `xty` is monomorphic — write `xty = .forAll [] ann`. Then:

- `xty.boundVars = []`, so the only valid `tys` is `[]`, and `tys.length = …` is trivial.
- `LTy.openFull xty [] = ann` (opening nothing).
- `RigidAnnotCompat Γ.aliases C.rigidTypeVars ann mty` with **all free vars of `ann` rigid**
  (Part B) forces `AliasEquiv Γ.aliases ann mty` directly — the existential `σ` in
  `RigidAnnotCompat` is identity on every free var of `ann`, so `subst [σ] ann = ann`
  (this is exactly the case the `RigidAnnotCompat` doc-comment at `LExprTypeSpec.lean:81-82`
  calls out).

So the rules simplify to (sketch):

```
| init_det : ∀ Γ x ann e mty md,
    Γ.types.find? x = none →
    x ∉ HasVarsPure.getVars e →
    AliasEquiv Γ.aliases ann mty →            -- was RigidAnnotCompat + tys + boundVars
    S.exprTyped C Γ e (S.embed mty) →
    CmdHasType' C Γ (.init x (.forAll [] ann) (.det e) md)
      { Γ with types := Γ.types.insert x (.forAll [] mty) }
```

Dropped: the `tys` existential, the `boundVars`-length premise, and the `RigidAnnotCompat`
wrapper (reduced to plain `AliasEquiv`). `LTy.openFull` disappears from these rules. The
`mty` is still distinct from `ann` only up to alias-equivalence (a `MyInt`-vs-`int`
annotation), so `AliasEquiv` stays.

Decision point to confirm: whether to keep `xty : LTy` in the `Cmd.init` AST (with a
well-formedness side condition that its binder is empty) or change the field to `LMonoTy`.
Keeping `LTy` is the smaller change (the AST is shared with the Imperative layer); the spec
just pattern-matches `.forAll [] ann`.

## Proof changes (`CmdTypeSpecProps.lean`, `CmdTypeProps.lean`)

- **`Cmd.typeCheck_sound`** (`CmdTypeSpecProps.lean:277`): the `init` cases currently build
  the `RigidAnnotCompat`/`tys`/`openFull` witness via `preprocess_isInstance_rigidAnnotCompat`
  (`CmdTypeProps.lean:127`). With the simplified rule these reduce to producing a single
  `AliasEquiv ann mty`. `preprocess_isInstance` (`:100`) and
  `preprocess_isInstance_rigidAnnotCompat` (`:127`) can be simplified or replaced by a direct
  `AliasEquiv` lemma (the `tys = []` / `boundVars = []` specialization). `preprocess_mono`
  (`:75`) is unchanged and still gives the `.forAll []` shape.
- **New `preprocess` obligations** for Parts A and B: a lemma that `preprocess` succeeds only
  on monomorphic annotations (Part A) and that the resulting monotype's free vars are rigid
  (Part B). These feed the simplified `init` rule's premises and re-establish `ContextMono`
  plus the "ambient free vars are rigid" invariant as *proved* properties of the typechecker
  rather than assumed hypotheses.
- **`ContextMono`** (`CmdTypeSpecProps.lean:45`) stays as the monomorphism invariant; Part B
  adds the companion "ambient free vars ⊆ rigid" invariant. Both are preserved by `init`
  (the inserted binding satisfies them by construction) and unaffected by the other commands.

## Function-soundness impact (the original motivation)

In `Function.typeCheck_sound` / `typeCheck_bodyTyped_instantiated`
(`FunctionTypeSpecProps.lean`): the false `h_ambient_rigid` hypothesis is *replaced* by the
now-true invariant from Part B, and `ContextMono` (Part A) gives the monomorphism that
`TContextAliasEquiv`'s Region B requires. The substituted-context formulation
(mirroring `Cmd.typeCheck_sound`'s conclusion over `TContext.subst Env.context …`) plus this
invariant discharges Region B without any rigidity assumption that isn't enforced by the
typechecker. See `ALPHAEQUIV_RENAMESUBST_PLAN.md` §5 (Region B) and §10j.

## Tests

- `StrataTest/Languages/Core/Examples/MonoLocalBindingTest.lean` — local bindings are
  monomorphic (a `∀a.a→a := \y.y` binding cannot be used at two types). After Part A, the
  polymorphic *annotation* itself should be rejected; update this test accordingly.
- `StrataTest/Languages/Core/Examples/AmbientTyvarGenProbe.lean` — #1399 exploit; after the
  fix the program must be rejected (Part B rejects `var x : a`; route 1 is gone).
- A new test for Part B: `var x : a` with no enclosing `proc<a>` is rejected; `var x : t`
  under `proc<t>` is accepted (rigid) and a nested fn refining/generalizing `t` is rejected
  by #1395.
