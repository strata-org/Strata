# Plan: Rigid type-variable checking for `var`/`set` (and a suspected `funcDecl` gap)

## Problem being fixed

Strata treats a type variable bound by an enclosing `procedure⟨a⟩` as a
**refinable unification variable** inside the body, rather than a **rigid**
(skolemized) parameter. This is unsound.

Minimal reproduction (`StrataTest/Languages/Core/Tests/PolyProcBodyRefinementBug.lean`,
`refineThenCallBool`):

```
procedure Foo<a>(out x : a) spec { ensures true; } { x := 0; }
procedure Test() spec { ensures true; } {
  var y : bool := true;
  call Foo(out y);
}
```

The body `x := 0` refines `a := int`. The call instantiates `a := bool`. Both
**typecheck and verify successfully today** — so a `bool` variable `y` ends up
holding the value `0 : int`. Soundness violation.

### Root cause

`Imperative.Cmd.typeCheck` (`Strata/DL/Imperative/CmdType.lean`):

- `init` det branch, line 39: `let τ ← TC.unifyTypes τ [(xty, ety)]`
- `set` det branch, line 60: `let τ ← TC.unifyTypes τ [(xty, ety)]`

`unifyTypes` freely refines any type variable in `xty`, including rigid ones
inherited from an enclosing `procedure⟨a⟩`. Nothing forces the declared type to
remain as general as written.

### Abstract syntax is the contract — concrete syntax is only one source

`Imperative.Cmd.typeCheck`, the `CmdHasType'` spec, and the soundness proofs all
operate on **abstract syntax**, where the declared type `xty : LTy` is an
**arbitrary scheme**. The fix and the spec must be correct for any `xty`, NOT just
the shapes the concrete-syntax translator happens to emit.

Two distinct things live in an abstract `xty`:
- **∀-bound variables** — `xty = forAll [a] (a → a)`. The `init` checker
  `preprocess`es these (instantiates them to fresh unification vars), so a
  declared `∀a.…` is *supposed* to be refinable per use. `StatementTypeTests.lean`
  exercises exactly this (line 35 `.init "y" t[∀α. %α] …`, line 139
  `var x : ∀a.a := 1; x := 2`) — these must keep working.
- **Free type variables** — `xty` mentions `a` free, where `a` is a rigid
  parameter bound by an enclosing `procedure⟨a⟩` and recorded in `Γ`. These must
  **not** be refinable; refining one is the soundness bug.

So the rule cannot be "reject any refinement of a variable in `xty`" (that would
break legitimate ∀-instantiation), nor "allow any" (the current bug). It must
distinguish **∀-bound (instantiable)** from **free-and-context-bound (rigid)**.
The concrete translator currently only emits `forAll [] mty` for `var`
(`Translate.lean:1278`), but that is an incidental property of one front-end, not
a constraint the abstract-syntax checker/spec may rely on. Any design or proof
that is only correct because "`xty` has no ∀-binders in practice" is wrong.

The alpha-equivalence approach (à la `FunctionType`) is the intended design. It
adapts cleanly once we separate the two kinds of variable: `preprocess` already
instantiates the ∀-bound ones; the alpha check then protects the free/rigid ones.
See the design section for exactly how.

## Design — alpha-equivalence, worked through all three layers

The alpha-equivalence approach IS the design. The key enabling fact, confirmed in
the code:

> **`AliasEquiv` is already rigid on free type variables.** Its constructors
> (`LExprTypeEnv.lean:98-112`) are `refl`, `expand`, `collapse`, `cong_tcons`,
> `trans` — there is **no ftvar-renaming rule**. So `AliasEquiv as (ftvar a) (ftvar b)`
> holds only when `a = b` (via `refl`). `AliasEquiv as (ftvar a) int` is **false**.

This means the soundness bug lives entirely in the **`∃ σ`** of the current
premise `AnnotCompat aliases ann mty := ∃ σ, AliasEquiv aliases (subst σ ann) mty`
(`LExprTypeSpec.lean:71`). That existential `σ` is precisely the unrestricted
refinement: it lets a free rigid `a` be mapped to `int` before the equivalence
check. **Delete the existential and the rigidity falls out for free.**

So the design across the three layers is a single coherent move, not three guesses:

### Layer 1 — Spec (`CmdTypeSpec.lean`): drop the `∃ σ`

Replace the premise on `init_det`/`init_nondet`:

```
- AnnotCompat Γ.aliases (LTy.openFull xty tys) mty            -- ∃ σ, AliasEquiv … (subst σ …) …
+ AliasEquiv  Γ.aliases (LTy.openFull xty tys) mty            -- rigid: no σ
```

`openFull xty tys` still instantiates the **∀-bound** variables of `xty` (that is
the legitimate per-use polymorphism — `tys` are the chosen instantiations, exactly
what `preprocess` produces with fresh unification vars). What changes is that the
*result* must be `AliasEquiv` to `mty` **without** a further refining substitution.
Outcome on the three abstract-syntax shapes:

- `xty = ∀a. a`, `var x := 1`: `tys = [int]`, `openFull = int`, `AliasEquiv int int` ✓ — still accepted (legitimate ∀-instantiation, B5).
- `xty = int`, `var x := true`: `openFull = int`, need `AliasEquiv int bool` — false ✗ — rejected (C6).
- `xty = a` free/rigid, `var x := 0`: `tys = []`, `openFull = a`, need `AliasEquiv a int` — false (no ftvar rule) ✗ — **rejected**: this is the bug fix (A2).

**Freshness — CORRECTION (the plan was wrong here):** The checker DOES need to
distinguish **rigid** type variables from **free** ones. The spec-level `AliasEquiv`
is rigid on ALL free type variables, but the checker operates in a world where some
free vars are legitimately unifiable:

> **Why rigid vs. free matters — concrete example:**
>
> After CallElim transforms `call Id(true, out b)` inside `procedure Test()`,
> the program contains `var tmp_arg_0 : a := true` where `a` comes from `Id`'s
> header. `Test` has no type params — `a` is just a free variable here. The
> typechecker must be free to unify `a` with `bool`. If the checker rejects ALL
> free-var refinements, this legitimate code fails.
>
> Contrast with `procedure Foo<a>(out x : a) { x := 0; }` — here `a` IS a rigid
> type parameter of `Foo`. The body refining `a → int` is unsound because a
> caller can instantiate `a = bool`.
>
> The distinguishing property: `a` is **rigid** in `Foo` because it appears in
> `Foo`'s `typeArgs`. It is **free** (unifiable) in `Test` because `Test`'s
> `typeArgs` is empty.

The checker must therefore track which type variables are rigid for the current
procedure. Only refinement of rigid variables is rejected. Free variables (whether
from CallElim temporaries, or from other sources) remain unifiable as before.

### Layer 2 — Checker (`Imperative/CmdType.lean`): add the alpha gate

`init` det (after line 39) and `set` det (after line 60), once `unifyTypes` gives
subst `S`: compute the substituted declared type and require it alpha-equivalent to
the pre-substitution declared monotype, mirroring `FunctionType.lean:83-90`:

```
let inferredXty := LMonoTy.subst S.subst xtyMono
unless (LMonoTy.alphaEquivMap xtyMono inferredXty).isSome do
  .error "declared type {xty} is more general than its initializer"
```

Here `xtyMono` is the post-`preprocess` monotype (∀-binders already instantiated to
fresh unification vars). `alphaEquivMap` permits only a bijective *renaming* of
those fresh vars; it returns `none` if `S` *refined* a variable to a constructor
(`a ↦ int`) — which is exactly the rigid-violation case. This is the executable
mirror of the spec's rigid `AliasEquiv`.

- `set` reads `xty` from `Γ` (`CmdType.lean:56`); the rigid var to protect is
  whatever type is recorded there. Same `alphaEquivMap` gate applies to that type.

### Layer 3 — Proofs

**What gets retired:** `AnnotCompat`-specific glue added this session —
`preprocess_isInstance_annotCompat` and `annotCompat_of_aliasEquiv`
(`CmdTypeProps.lean`). The premise no longer mentions `AnnotCompat`.

**What gets reused unchanged:** `LTy_instantiate_eq_openFull` and
`LTy_instantiateWithCheck_isInstance` (`LExprTypeSpec.lean`) — these already produce
`AliasEquiv Env.context.aliases (openFull xty tys) mty_pre` directly (that was the
*inner* lemma; we previously weakened it to `AnnotCompat` via
`annotCompat_of_aliasEquiv`). The rigid spec premise wants exactly the `AliasEquiv`
they already give, so the proofs get *shorter*: the `AnnotCompat_subst` transport
step is replaced by... nothing — but see the obligation below.

**The one real new obligation (state it, then prove it):** in the soundness proof,
the stored `mty` is `subst S mty_pre`, while `LTy_instantiateWithCheck_isInstance`
gives `AliasEquiv aliases (openFull xty tys) mty_pre` (pre-substitution). Under the
old `AnnotCompat`, the `∃ σ` absorbed `S` via `AnnotCompat_subst`. With rigid
`AliasEquiv` we instead need:

> **`AliasEquiv aliases (openFull xty tys) mty_pre` and the checker's `alphaEquivMap`
> success ⇒ `AliasEquiv aliases (openFull xty tys') (subst S mty_pre)`** for the
> substituted `tys'`.

Intuition: `S` only *renames* the openFull variables (that is precisely what the
checker's `alphaEquivMap` gate guarantees), so applying `S` keeps the equivalence,
with `tys' = tys.map (subst S)`. This is the proof analogue of the checker gate —
i.e. **the `alphaEquivMap` success is the hypothesis that makes the proof go
through**, which is why the gate must be added to the checker for the soundness
theorem to even be true. This is the load-bearing lemma; prove it hardest-first.

**New `alphaEquivMap` lemmas (none exist today — built from scratch):** the bridge
from the executable `alphaEquivMap = some` to the propositional "`S` acts as a
renaming on these vars" fact above. Prove in `LTy.lean` (where `alphaEquivMap` is
transparent) or `LExprTypeSpec.lean`. Inventory confirms zero existing lemmas, so
budget for: `alphaEquivMap` is symmetric/total-on-renamings, and
`alphaEquivMap a b = some ⇒ b = rename a` for a bijection on ftvars.

**Why no explicit freshness side-condition is needed (proof-level argument):**

The concern: could `S` map a fresh preprocess var `$__ty0` to a rigid var `a`,
thereby "limiting" `a`? Answer: no, because of how the layers interact:

1. `alphaEquivMap xtyMono (subst S xtyMono) = some` guarantees `S` restricted to
   `ftvars(xtyMono)` is a **bijective renaming** — every var maps to a distinct var.
2. The unifier (`unifyTypes`) only assigns to **unification variables** — the fresh
   `$__ty`-prefixed vars generated by `preprocess`. It never writes `a ↦ ...` for a
   rigid `a` already in `Γ`, because rigid vars are not in its assignment domain.
3. Therefore if `v ∈ ftvars(xtyMono)` is rigid (not a fresh preprocess var), then
   `S v = v` — it is untouched by the substitution. The `alphaEquivMap` succeeds
   trivially on those positions (identity is a bijection).
4. Fresh vars `$__ty0` CAN map to rigid vars (e.g., `$__ty0 ↦ a`) — this is
   legitimate `∀`-instantiation ("declared type was `∀α.α`, initializer has type
   `a`"). The rigid var `a` is not being refined; it's the *target* of an
   instantiation of a universally-quantified slot.

For the proofs, the key fact to establish is: **the unifier's assignment domain is
disjoint from the set of rigid ftvars in `Γ`** (i.e., `preprocess` generates names
outside `Γ`'s ftvar set). This is the invariant that makes the `alphaEquivMap`
check sufficient without a separate "targets must be fresh w.r.t. context" premise.
Concretely, this means a lemma like:

> `preprocess xty state = (xtyMono, tys, state')` ⇒
> `ftvars(xtyMono) \ ftvars_of_openFull(xty) ⊆ {state.tyPrefix ++ i | i ∈ ℕ}`

i.e., the only new vars introduced are the `$__ty`-prefixed ones, which the unifier
owns. Combined with `alphaEquivMap = some ⇒ bijective renaming`, this gives us that
rigid vars (which are NOT `$__ty`-prefixed) are fixed by `S`.

### Workflow (tests-first, then fix, then spec, then proofs)

1. **Tests first:** Write the full regression test suite (A/B/C below) recording
   **current** (buggy) behavior with `#guard_msgs`. This locks in the baseline.
   Rename `PolyProcBodyRefinementBug.lean` → `StatementPolyTests.lean` as part of
   this step (the file becomes the permanent poly/rigid test battery, not a bug
   probe).
2. **Checker** (Layer 2): add the `alphaEquivMap` gate. Re-run the test suite and
   update `#guard_msgs` expected output to reflect the new (correct) verdicts.
   The diff between step 1 and step 2 IS the evidence the fix works.
3. **Spec** (Layer 1): drop `∃ σ`, build `CmdTypeSpec`. This is a pure
   tightening; confirms it elaborates.
4. **Proofs** (Layer 3): rebuild `CmdTypeSpecProps`, read the four broken
   `init`/`set` goals — they pin the exact statement of the load-bearing lemma
   above. Prove the `alphaEquivMap` leaf lemmas, then the bridge, then close the
   soundness cases.
5. `ContextMono` preservation stays a **separate, independent** follow-up.

## Permanent regression tests

All of these are **real, permanent tests with concrete `#guard_msgs` expected
output** — not throwaway probes. The current `#eval`s in
`PolyProcBodyRefinementBug.lean` get finalized with their real expected messages
(post-fix), not deleted. Where a test must change verdict because of the fix, the
expected message is updated as part of the change and that diff IS the evidence the
fix works. Each test states *concrete-syntax* and, where it exercises a shape the
translator cannot emit, a parallel *abstract-syntax* version (direct `.init`/`.set`
construction in the `Statement`/`Cmd` AST) — because the checker/spec contract is
on abstract syntax (see the abstract-syntax section).

### A. Soundness regressions — `PolyProcBodyRefinementBug.lean`

- **A1 `refineThenCallBool`** — `Foo<a>(out x:a){ x:=0 }; call Foo(out y:bool)` →
  **changes from "verifies ✅" to a type error** post-fix (headline regression;
  currently wrongly verifies). The expected-message flip is the proof the fix lands.
- **A2 `refineThenCallInt`** — `Foo<a>(x:a){ var tmp:a:=0 }; call Foo(5)` →
  **changes to a type error** post-fix (body ill-typed; user-confirmed strict reading).
- **A3 `callSiteConflict`** — `Id<a>(x:a,out y:a){y:=x}; call Id(bool, out int)` →
  stays a type error (already correct today: `Impossible to unify a with int`;
  guards the opposite-direction regression).

### B. Must-still-accept (guard against over-rejection)

- **B4** — `Id<a>(x:a, out y:a){ y := x }` called at a *consistent* concrete type
  (`var b:bool; call Id(true, out b)`) → accepts. Genuinely-polymorphic body survives.
- **B5 (abstract-syntax ∀-instantiation — the case the fix must NOT break)** — the
  existing `StatementTypeTests.lean` polymorphic inits, which construct `.init` in
  abstract syntax with real `forAll` schemes: line 35 `.init "y" t[∀α. %α] (.det …)`
  and line 139 `var x : ∀a.a := 1; x := 2`. These must still pass — they exercise
  exactly the `xty = forAll [a] …` path that distinguishes the rigid-`AliasEquiv`
  design (drops `∃ σ`, keeps `openFull` ∀-instantiation) from a naive "no refinement
  at all" rule that would wrongly break them.

### C. Unit-level — `StatementTypeTests.lean`

- **C6** — `var x : int := true` → error (added this session; keep).
- **C7 (rigidity at the `var`/`set` level, abstract + concrete)** — inside a
  `procedure⟨a⟩`, `var x : a := 0` (and a `set` analogue) must be **rejected**.
  Also add the abstract-syntax form directly: a `Cmd.init` with `xty` a free rigid
  ftvar and an `int` initializer, checked against a `Γ` where that ftvar is bound —
  must be rejected. This is the test that distinguishes the rigid design from the
  current buggy one at the single-command granularity the spec actually covers.
- **C8 (suspected funcDecl gap)** — a `funcDecl` nested inside a `procedure⟨a⟩`
  whose signature alpha-matches the outer `a` (`FunctionType.lean:84` has no
  context-freshness check on the alpha map's targets). Write it as a real test
  recording current behavior. If it wrongly accepts, that is a **separate
  pre-existing finding** — fix tracked independently; do not fold into this change.

## Scope boundary

Fixes the **body-refinement** unsoundness + the mono-mismatch case, on **abstract
syntax** (the checker/spec/proof contract), with concrete-syntax tests as the
end-to-end witnesses. Does **not** touch `ContextMono` (orthogonal proof hygiene).
Does **not** need call-site changes — call-site instantiation consistency is already
sound (verified by `callSiteConflict`/A3). The `funcDecl` item (C8) is a separate
finding if confirmed.
