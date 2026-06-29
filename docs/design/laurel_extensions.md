# Laurel Extensions for Exception Handling (Holistic Design — WIP)

_Last updated: 2026-06-25_

This document proposes a **single, coherent set of Laurel extensions** intended to
host *all* the exception-handling features `F1`–`F36` — F1–F30 for the three initial
front-ends (Java/Python/JavaScript) and F31–F36 for the Kotlin/C# candidates (each
`F<n>` is named in the coverage table below). The features are interdependent, so we
design the extension *areas* together rather than feature-by-feature, then show how
each area serves the relevant `F<n>`.

It is anchored in a design baseline: a single optional `throws` type per procedure, a
separate `onThrow` exceptional postcondition, a value-carrying `throw`, and
predicate-based catch clauses, lowering toward `Result<Val, Err>`.

> **Scope.** Synchronous exception handling only.

> **STATUS: working draft.** Extensions E1–E7 below are worked through. The table
> below maps every feature (F1–F36) to the extension(s) that cover it.

---

## Feature coverage (F1–F36 → extensions)

How each feature `F1`–`F36` is covered by the design extensions E1–E7 below. E1 (the rooted `BaseException` typing of
`throw`/`catch`/`onThrow`) underlies the whole table; only the most relevant extensions are
named per row. "Front-end" means the feature is realized by a front-end desugaring or check
on top of the named extension, not by a new core construct.

| ID | Feature | Extension(s) | How it is covered |
|----|---------|-------------|-------------------|
| F1 | Unchecked | E4, E7 | front-end imposes no declare-or-catch; `throws` declared/inferred, lowered to `Result` |
| F2 | Checked exceptions | E4, E3 | Java front-end does declare-or-catch; Laurel records `throws`; multi-type via `onThrow` predicate |
| F3 | Any value thrown (JS) | E1 | JS front-end wraps raw values in `DynamicJsValue extends BaseException` |
| F4 | Single rooted hierarchy | E1 | prelude root `BaseException`; user types `extends` it |
| F5 | `Error` fatal tier (Java) | E1 | front-end makes Java's `Error` a direct child of the root, outside its catchable `Exception` tier, so `is Exception` is false |
| F6 | `BaseException`-only tier (Py) | E1 | front-end makes `SystemExit`/`KeyboardInterrupt`/`GeneratorExit` direct children of the root, outside its `Exception` tier |
| F7 | Type dispatch, most-specific-first | E3 | ordered `catch e when e is T`, first-match-wins |
| F8 | No dispatch, manual (JS) | E3, E1 | one catch-all clause + manual `is`/field inspection |
| F9 | At most one catch (JS) | E3 | front-end emits a single clause |
| F10 | Multiple catch clauses | E3 | ordered `catches` list |
| F11 | Multi-catch | E3 | one clause `catch e when e is A \|\| e is B` |
| F12 | Optional binding | E3 | binding mandatory in IR; front-end synthesizes a name when omitted |
| F13 | `else` (on success) | E5 | front-end desugars (success flag inside `finally`) |
| F14 | `finally` | E5 | core `Try.finally` arm |
| F15 | try-with-resources (Java) | E5 | front-end desugars to nested `try`/`finally` + suppressed (F26) |
| F16 | Context-manager `with` (Py) | E5 | front-end desugars to `try`/`finally` (`__enter__`/`__exit__`) |
| F17 | `with` suppression (Py) | E5 | front-end desugars to `try`/`catch`/`finally` with conditional rethrow |
| F18 | `return`-in-`finally` masking | E5 | `finally` lowering: abrupt completion wins |
| F19 | Explicit cause chaining | E6 | `cause` field on `BaseException`, set by front-end |
| F20 | Implicit context (`__context__`) | E6, E2 | `context` field, written when raising mid-handling |
| F21 | Chain suppression (`from None`) | E6 | `suppressContext` flag / cleared `cause` |
| F22 | `add_note` | E6 | `notes` list field appended by front-end |
| F23 | `throw e` preserves trace (Java) | E2 | base `throw e`; traces not modelled |
| F24 | Bare `raise` (Py) | E2 | front-end lowers to `throw e` against the catch binding |
| F25 | `AggregateError` (JS) | E6 | library composite with an `errors` list |
| F26 | Suppressed (Java) | E6, E5 | `suppressed` field; try-with-resources attaches the secondary failure |
| F27 | `ExceptionGroup`/`except*` (Py) | E6 | library composite; `except*` desugared; possible future first-class `catch*` |
| F28 | Generator `.throw()` (Py/JS) | E6 | deferred to the generator feature; reuses ordinary `throw` |
| F29 | Exceptions as control flow (Py) | E6 | ordinary composites (`StopIteration`/`GeneratorExit`) via the normal machinery |
| F30 | Cleanup-bypassing exit | E6 | builtin `ensures false` (`os._exit`) / `throw SystemExit` (`sys.exit`) |
| F31 | `Result`/`runCatching` (Kotlin) | E7 | the same `Result<Val, Err>` surfaced as a value |
| F32 | `when` guards (C#) | E3 | guard predicate `e is T && cond` |
| F33 | try-as-expression (Kotlin) | — | **out of scope (for now):** `Try` is a unified `StmtExpr`, but value-yielding semantics are deferred |
| F34 | `Nothing` bottom type (Kotlin) | E7 | non-throwers unwrapped; always-throws ⇒ `Nothing` on the normal channel (needs a bottom type) |
| F35 | `finally` cannot be exited (C#) | E5 | front-end check rejecting `return`/`break`/`continue` in `finally` |
| F36 | `ExceptionDispatchInfo` (C#) | E2 | collapses to `throw e` (traces not modelled) |

---

## Extension areas (overview)

The constructs the design adds to Laurel, grouped. Extensions E1–E7 resolve the choices
within these areas; the table above maps individual features.

- **A. Exceptional control-flow channel** — a `throw` statement plus an exceptional
  procedure-exit path.
- **B. Throwable values & exception hierarchy** — the `BaseException` channel root (E1);
  any tiering above it is front-end policy.
- **C. Procedure exceptional contract** — an optional single `throws` type and an
  `onThrow` exceptional postcondition.
- **D. Structured handler** — `try` / predicate-based `catch` / `finally` (E3, E5).
- **E. Resource & scoped cleanup** — try-with-resources and context-managers, by
  desugaring (E5).
- **F. Aggregation & groups** — multi-error carriers and group matching, deferred (E6).
- **G. Control-flow-as-exceptions & termination** — generator injection, iteration
  sentinels, cleanup-bypassing exit; deferred (E6).
- **H. Candidate-feature hooks (Kotlin/C#)** — F31–F36.
- **I. Lowering to Core** — `Result<Val, Err>` plus labelled blocks / `Exit` (E7).

---

## Extensions

### E1. Throwable values are rooted at a prelude `BaseException`

**Extension.** Laurel is extended with a single, prelude-defined root composite
`BaseException`, and every value that travels on the exceptional channel is a subtype of
it. `throw`'s operand, a `catch` binding, and the `onThrow` exception binder are all typed
`BaseException` (or a declared subtype).

The prelude defines **only the root** — the one type Laurel itself depends on, because it
anchors the exceptional channel for the type-checker:

```
composite BaseException {
  var message: string
};
```

**Tiering is front-end policy, not a Laurel concern.** Laurel deliberately does **not**
predefine an `Exception` / fatal split (or any other taxonomy). The "escapes an ordinary
catch-all" behavior — Java's `Error`, Python's `SystemExit`/`KeyboardInterrupt`/
`GeneratorExit` — is not a Laurel construct. It is realized entirely by (a) the front-end
choosing *which parent a type extends* and (b) the catch predicate. Laurel's subtype
machinery evaluates `e is T` generically and treats every exception type as an ordinary
composite.

This is intentional. Predefining a two-tier (or N-tier) taxonomy would bake Java/Python's
particular structure into a language-neutral IR — the same objection as enumerating every
`SystemExit`-like type — and it buys **no verification power**: VC generation, the E4
no-escape invariant (which is about the channel root), and E7's `Err` typing (bounded by
`BaseException`) are all tier-independent, and predefining tiers cannot stop a front-end
from extending the wrong parent anyway. So the catchable-vs-fatal distinction stays where
it belongs — in the front-end. Adding a built-in tier to Laurel would only be justified
later if Laurel grew a first-class catch-all that needed a built-in "everything except
fatal," or if the verifier needed to reason structurally about a fatal tier; neither is in
scope.

**How this serves F4–F6.**

- **F4 (single rooted hierarchy):** Java's `Throwable` / Python's `BaseException` map onto
  the root; user types `extends` it, directly or transitively.
- **F5/F6 (the "escapes a normal catch" tiers):** the front-end models its catchable tier
  (e.g. a front-end-defined `Exception` type) and its fatal/exit types as *separate*
  children of `BaseException`. Because a fatal type is not a subtype of the front-end's
  catchable tier, `e is Exception` is automatically `false` for it — the escape falls out
  of the subtype check, needing nothing beyond how the front-end wires `extends`.
  (F3/F8 — JavaScript's throw-anything and manual inspection — are handled by the JS
  wrapper; see Q1.)

> **Prelude gating (implementation note).** `BaseException` is a *composite*, so it
> participates in the heap model — unlike the always-on datatype/function prelude, which
> is "free" for SMT. The Laurel pipeline prepends the prelude unfiltered, so injecting a
> heap-participating composite into *every* program perturbs SMT heap reasoning for
> programs that don't use exceptions. The exception prelude is therefore prepended **only
> when a program references it** (names `BaseException` or a subtype). Programs that do
> not use exceptions are unaffected.

> **Note (type-checker, validated in prototype).** `e is T` is rejected as a *type error*
> when `e`'s static type and `T` are unrelated (neither is a subtype of the other), rather
> than evaluating to `false`. This is exactly why the catch binding is typed at the root
> `BaseException`: bound at the root, `e is Exception` (for a front-end `Exception` tier)
> is well-typed and resolves to `false`/`true` at verification, so F5/F6 work. Binding at
> a narrow sibling type instead would make the cross-tier test ill-typed.


#### Q1 (resolved): thrown values are `BaseException` composites; JS boxes into a wrapper

**Decision.** Every thrown value is a `composite` rooted at `BaseException`
(**alternative (i)** below). Non-composite values (**datatypes**) are *not* thrown
directly. JavaScript's throw-anything is handled by the front-end boxing the value in a
wrapper, `composite DynamicJsValue extends BaseException { var value: JsValue }`:

```
var ex := new DynamicJsValue; ex#value := JsString("oops"); throw ex
```

`catch` binds a `BaseException` and unwraps via `(e as DynamicJsValue)#value`.

**Why this is simplest.** It is a **front-end concern only** and reuses the E1 machinery
verbatim — `extends BaseException` (subtyping is already implemented via `TypeLattice`),
`new`, field assignment, and `as` are all existing AST constructs. The shared prelude
needs only the generic `BaseException` root; `DynamicJsValue`/`JsValue` are JS-front-end
types (the front-end already needs a `JsValue` representation for dynamic values). So this
adds **no new core construct, no type-system change, and no change to the Core/SMT
encoding**, and keeps the channel uniformly typed (simple `catch`/`onThrow` typing). F8's
manual inspection is emitted as ordinary `is`/field/`if` predicates. The only cost — a
wrapper allocation plus a downcast per throw — is a runtime/perf concern that does not
matter for verification (the allocation is conceptually free; the downcast is an
`AsType` the verifier already understands).

**Alternative (ii), rejected — datatypes thrown directly.** The thrown value would be the
`JsValue` datatype itself (`throw JsString("oops")`), with `catch` binding it at its own
type. *Pro:* no boxing. *Con:* the channel is no longer uniformly `BaseException` (its
type becomes "`BaseException` or any thrown value"), which forces a language-neutral
relaxation of the channel type away from `BaseException` — touching `throw`/`catch`/
`onThrow` typing in the type system *and* the Core/SMT encoding. That is strictly more
core surface area for no verification benefit, so we do not adopt it.


### E2. Bare rethrow lowers to `throw e` — no dedicated rethrow construct

**Extension.** Laurel adds **no** no-operand rethrow form. The base
`throw` keeps the rule that it "takes a value and nothing else," and
a source-level bare rethrow is lowered by the front-end to `throw e`, where `e` is the
catch binding for the currently-handled exception. This is always possible because
every `CatchClause` carries a **mandatory** binding, so inside any
handler there is always a name for the in-flight exception; where the source omits the
name (F12), the front-end synthesizes a fresh one.

**Why no construct is needed.** F23 is already the base `throw e` (Java re-throws by
naming the caught object). F24 (bare `raise`) and F36 (`ExceptionDispatchInfo`) are
motivated entirely by stack-trace preservation — a runtime-metadata concern Laurel does
not model — so re-throwing the same value via `throw e` is semantically identical to a
"trace-preserving" rethrow. Bare `raise` lowers to `throw e` against the catch binding.
A `rethrow` form would buy no IR-level behavior.

**Subtlety (relationship to F20).** Python distinguishes bare `raise` (F24 — re-raise
the current exception, *no* new `__context__`) from `raise e` (a fresh raise that, when
done mid-handling, sets `__context__` — that is F20, implicit context chaining).
Lowering both to `throw e` erases that distinction at the IR level, which is correct
**provided context chaining (F19–F22) stays front-end-managed** — i.e. the front-end
explicitly writes the `context`/`cause` fields when it wants them, rather than `throw`
establishing context implicitly. Chaining is already deferred to E6 on exactly
those terms, so this remains sound. The only thing that would force a dedicated
`rethrow` is giving `throw` *implicit* context semantics, which this design avoids
precisely to keep this viable.


### E3. Catch dispatch: predicate-based clauses

**Extension.** A `catch` clause is a binding plus an optional predicate guard (no
types). The observable dispatch is an ordered clause list with first-match-wins.
Type dispatch is written `catch e when e is T`, and multi-catch
`catch e when e is A || e is B`. This is a single, minimal mechanism: there is no
type-list clause form and no surface sugar — front-ends call `isType` explicitly.

**Clause shape and dispatch.**

```
structure CatchClause {
  binding   : Identifier        -- bound to the caught value (typed BaseException)
  predicate : Option StmtExpr    -- guard; absent = catch-all
  body      : StmtExpr
}
```

A `Try` holds an ordered `catches : List CatchClause`. Clauses are tried in order; for
each, `binding` is bound to the caught value and `predicate` (if present) is evaluated;
the first match runs its `body`; if none match, the exception propagates out of the
`try`. This is **first-match-wins**.

**Feature coverage** is the table's dispatch rows (F7–F12, F32). Java's
"broader-before-narrower is a compile error" ordering is a front-end check (Python's
runtime first-match is not an error).

**Points to pin down.**

- The binding stays typed `BaseException`. A multi-type catch
  (`catch e when e is A || e is B`) has no single narrow type, so the binding is the
  common root; a body that needs subclass fields narrows via `(e as T)`.
- Guard predicates are expected to be **pure**. F32's side-effecting filter idiom
  (`when (Log(e))` returning `false`) relies on observable side effects during matching
  and is therefore not modelled faithfully.
- A multi-type checked declaration only constrains the *type set*; per-type exceptional
  postconditions still require explicit `onThrow` clauses.

The `try` / `else` / `finally` *handler arms* (how the surrounding structure is shaped,
not how clauses match) are covered by **E5**.


### E4. `throws` enforcement is front-end-only; Laurel records, not enforces

**Extension.** Laurel **records** a procedure's declared exception type
(`throws`/`onThrow`) as exceptional-postcondition data the verifier reasons about, but
performs **no** Java-style declare-or-catch check. Java's checked-exception rule (F2) is
run by the Java front-end on the Java source; Python/JavaScript/Kotlin front-ends skip
it. F1 (unchecked) and F2 (checked) then produce identical Laurel constructs — the only
difference is whether the front-end ran the check.

**Recording ≠ enforcing.** Two things are easy to conflate:

- *Recording / soundness modelling* — the verifier must know a callee can exit
  exceptionally (its `throws`/`onThrow`) to reason about a call site. This is needed
  whether or not the source language has checked exceptions, and is **not** enforcement.
- *The declare-or-catch static check* (F2) — a source-language well-formedness rule.
  This is what is left to the front-end.

**How this serves the static-checking features:**

- **F2 (checked exceptions — Java):** the Java front-end performs declare-or-catch on the
  Java AST — where the checked/unchecked distinction, the hierarchy, and "unrelated
  checked types" all live — and emits the resulting `throws` declarations. Laurel does
  not re-check it.
- **F1 (unchecked — Java runtime tier, Py, JS):** nothing extra. The front-end imposes
  no declare-or-catch obligation; it just declares (or infers) `throws` on procedures
  that can throw so the verifier models them.

**The one invariant Laurel does enforce (semantic, language-agnostic).** Sound lowering
to `Result<Val, Err>` requires that *a procedure with no `throws` declaration cannot let
an exception escape* — every throw inside it must be caught. Violating it is a
verification failure (like an unmet postcondition). This is the language-neutral
*counterpart* of declare-or-catch, not Java's syntactic rule. Consequences:

- The *callee marking* ("this procedure can throw") must exist for soundness; it comes
  from the `throws` declaration, or from future inference (ties to E7).
- F1 front-ends therefore still declare or infer `throws` on throwing procedures even
  though their source language does not require it, so the invariant is satisfiable.

**Why front-end-only over Laurel-enforced.** Enforcing F2 in Laurel would bake a
Java-specific rule (checked vs unchecked tiers, hierarchy knowledge) into a
language-agnostic IR; every other front-end would have to opt out, and it would
duplicate the check the Java front-end already runs — with no benefit to verification.
Recording `throws` plus the semantic no-escape invariant gives soundness without the
Java-specific machinery.


### E5. `finally` is a core handler arm; `else` and resource forms are desugared

**Extension.** The `Try` structure gains one new core arm, `finally`; everything else in
this theme is front-end desugaring into `try`/`catch`/`finally`.

```
structure Try {
  body    : StmtExpr
  catches : List CatchClause
  finally : Option StmtExpr     -- core cleanup arm; runs on every exit path (F14)
}
```

**Why `finally` is core.** It runs on *every* exit path — normal completion,
`return`/`Exit`, and a propagating throw — and its interaction with abrupt completion is
the subtle part: a `return` or throw inside `finally` overrides a pending exception and
any prior return (F18). Centralizing it in one lowering means every front-end gets that
masking behavior correct for free, rather than each re-deriving it.

**Why `else` is not core.** Python's `else` (F13) is plain control flow — "run after the
body succeeds, outside the catches" — with no subtle interaction with the exceptional
channel, and it is Python-only. The front-end desugars it with a success flag inside the
`finally` scope, so it needs no core arm:

```
try {
  try { body; ok := true } catch e when e is E { handler }
  if ok { elsebody }
} finally { cleanup }
```

The remaining cleanup features are front-end work over `try`/`catch`/`finally` (see the
table): `else` (F13) as above; try-with-resources (F15) and `with`/context-managers
(F16/F17) by desugaring; and F35 (C# forbidding exit from `finally`) as a front-end check
— Laurel core must *allow* exit from `finally` to model F18 for the other languages.


### E6. Chaining, aggregation, control flow and termination are deferred (no new core)

**Extension.** None of these features get new core exception machinery now. Each rests on
top of E1–E5 as one of: (a) a **library composite** or extra **field** on
`BaseException`, (b) a **front-end desugaring** onto already-decided constructs, or
(c) an ordinary **builtin procedure**. They are deferred — recorded here so the design
is complete, but not specified in detail.

**The concrete shapes** (deferred, recorded for completeness):

- *Chaining/notes (F19–F22):* fields on `BaseException` written by the front-end —
  `cause : BaseException` (F19), `context : BaseException` (F20), a `suppressContext`
  flag (F21), a `notes` list (F22).
- *Aggregation/groups (F25–F27):* library composites —
  `AggregateError extends BaseException { errors : List BaseException }` (F25; the
  front-end picks the parent — e.g. its own `Error` tier); a
  `suppressed : List BaseException` field that try-with-resources (F15, E5) populates
  (F26); `ExceptionGroup extends BaseException { exceptions : List BaseException }` with
  `except*` desugared (F27).
- *Control flow (F28–F29):* F28 (generator `.throw()`) belongs to the generator feature
  and reuses ordinary `throw` once that lands; F29 (`StopIteration`/`GeneratorExit`) are
  ordinary composites via the normal machinery.
- *Termination (F30):* `os._exit`/`System.exit` is a builtin with `ensures false` (never
  returns, not a throw, so it bypasses `finally`); Python's catchable `sys.exit()` maps
  to `throw` of a front-end `SystemExit` type (a direct child of `BaseException`, outside
  the catchable tier) instead.

**Why `except*` (F27) is the only possible future core work.** The predicate catch of E3
is **select-one-of**: first-match-wins, exactly one clause fires, and it binds the whole
thrown value. `except*` is **partition-and-run-all-with-residual**: a single
`ExceptionGroup` is *split* across clauses (several may fire, each on its matching
subgroup), and the unmatched remainder re-raises automatically. The same primitives still
express it — the front-end emits a catch-all that splits the group, runs each matching
handler, and re-throws the remainder:

```
try { ... }
catch e {                                  // catch the whole group
  var m1 := splitMatching(e, ValueError);
  if !isEmpty(m1) { eg := m1; <handler1> }
  var m2 := splitMatching(e, TypeError);
  if !isEmpty(m2) { eg := m2; <handler2> }
  var rest := unmatched(e, [ValueError, TypeError]);
  if !isEmpty(rest) { throw rest }         // re-raise the remainder
}
```

A first-class `catch*` would simply bake in that split/run-all/residual shape; since it
desugars, it stays deferred.


### E7. `Result` lowering requires generic datatypes; non-throwers stay unwrapped

**Extension.** An exceptional procedure (one with a `throws` declaration) lowers to return
a generic `Result<Val, Err>` sum type carrying either the normal value (`Good`) or the
thrown exception (`Bad`); a **non-throwing procedure returns its value type directly,
unwrapped** — no `Result`, no `Err` (E4). This **requires Laurel to support
generic (polymorphic) datatypes** — a single `Result<Val, Err>`, not concrete
per-instantiation types. Laurel does not have polymorphic datatypes today (confirmed in
the grammar/AST and the `CoreDefinitionsForLaurel` "fix when Laurel supports polymorphism"
TODO), so this is a **prerequisite** for the lowering. Generics are a known, needed
addition expected soon, and we deliberately do **not** work around their absence by
synthesizing monomorphized `Result_<Val>_<Err>` types.

```
datatype Result<Val, Err> { Good(value: Val), Bad(err: Err) };
```

**`Err` typing.** `Err` is the procedure's single declared `throws` type, always bounded
by `BaseException` (E1). It is instantiated **precisely** where the throw set is a single
type (`Result<int, IOException>`), and **coarsened to
a common supertype** — `BaseException` or the nearest common ancestor — for the
multi-type checked case (Java multi-type `throws`, recorded as an `onThrow` predicate
carrying the precise set) and the JS-dynamic case (`DynamicJsValue`). Non-throwing
procedures have no `Err` at all.

**Lowering mechanics (reusing existing `Block`/`Exit`/`bodyLabel`).**

- `throw v` → assign `Bad(v)` to the result variable and `exit` the nearest enclosing
  `try` label, or the procedure's `bodyLabel` if there is no enclosing `try`.
- a call to a thrower → bind the returned `Result`; `if Result..isBad(tmp) then exit
  <tryCatches>`; otherwise extract `Result..value(tmp)` and continue.
- the handler region (`tryCatches`) runs the predicate-based catches (E3); an unmatched
  or re-thrown exception re-assigns `Bad` and exits outward; `finally` (E5) is inserted
  on every exit edge, which is where its F18 masking is realized.

No new control-flow construct is introduced — the lowering is built from Laurel's existing
labelled blocks and `Exit`.


---

## Status & open points

Extensions E1–E7 above are worked through, and all design questions are resolved.

**Out of scope for now:**

- **F33 (try-as-expression):** deferred. `Try` is a unified `StmtExpr`, but its
  value-yielding semantics are not specified and we are not handling them at this stage.

All extensions (E1–E7) are resolved — including E1/Q1 (thrown values are `BaseException`
composites; JS boxes into a `DynamicJsValue` wrapper). The table above gives the
per-feature mapping. 
