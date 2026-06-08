---
inclusion: fileMatch
fileMatchPattern: ['Strata/Languages/Laurel/**/*.lean', 'StrataTest/Languages/Laurel/**/*.lean']
---

# Working on Laurel

Pointers for agents editing Laurel code. For background, read the
[Laurel manual source](../../docs/verso/LaurelDoc.lean)
(sections *Design Principles*, *Conventions and Invariants*,
*Translation Pipeline*, and *Known Limits and Roadmap*), or its rendered HTML
under `docs/verso/_out/laurel/html-single/` after running `docs/verso/generate.sh`.

## Scope rules

Laurel is *the* language for features shared between imperative,
garbage-collected source languages (Java, Python, JavaScript, TypeScript).

* If a feature is only needed for one source language, put it in that
  front-end's translator, not in Laurel.
* If a feature is deductive-verification specific (e.g. opacity,
  `decreases`), it is OK to add to Laurel — Laurel targets multiple
  analyses but carries verification-specific annotations.
* Feature design is about user expressivity, not about how it lowers to
  Core. The Core encoding can change (see the heap rewrite in PR #338)
  without altering Laurel semantics.

## Do not

* **Do not split `StmtExpr` into separate statement and expression
  types.** The unified AST is deliberate and reduces duplication of
  constructs like `IfThenElse` and `Block`.
* **Do not invent a new "I don't know" type of node.** Use `.Hole` with a
  deterministic flag and let `InferHoleTypes` + `EliminateHoles` handle
  it. Adding a second unknown-node kind breaks every downstream pass.
* **Do not add side tables for metadata.** `AstNode` already carries
  `source`; if you need more, key it on post-resolution `uniqueId`.
* **Do not resolve identifiers by textual name** in any pass after
  resolution. Use `uniqueId`.
* **Do not encode Python-specific type information in Laurel types.**
  Python's `Any` lives in `Strata/Languages/Python/`; Laurel sees it as
  a single composite type with constructors, and that is the intended
  abstraction.
* **Do not lift procedure calls into assert/contract bodies.** Pure
  contexts must remain pure. If a front-end wants to check a property
  about a procedure call's result, it must first bind the result to a
  local.

## Do

* **Use `.Hole` to recover from errors in translators.** Emit a
  diagnostic and a hole in place of the problematic sub-expression; the
  rest of the program still compiles and the user sees a useful error.
* **When you add a `StmtExpr` constructor, update every pass.** At
  minimum: `MapStmtExpr`, `Resolution`, `HeapParameterization`,
  `InferHoleTypes` / `EliminateHoles` (if the constructor can contain a
  hole), `LiftImperativeExpressions`, `LaurelToCoreTranslator`,
  `LaurelFormat`, and `ConcreteToAbstractTreeTranslator` +
  `AbstractToConcreteTreeTranslator`. Missing one produces the classic
  "holes should have been eliminated before translation" error or
  equivalent.
* **Mark passes that invalidate resolution with `needsResolves := true`**
  in `LaurelCompilationPipeline.lean`. Otherwise subsequent passes will
  trip over dangling `uniqueId`s.
* **Keep the documented pipeline order in sync.** If you add, remove, or
  reorder a Laurel-to-Laurel pass in `LaurelCompilationPipeline.lean`,
  update the *Pipeline order* section below and the pass list in the Laurel
  manual. (PR #1222 replaces these hand-maintained lists with
  auto-generated documentation; prefer that mechanism once it lands.)
* **Keep the translation to Core "dumb".** If a Laurel → Core case needs
  non-trivial work, the work probably belongs in an earlier
  Laurel → Laurel pass.
* **Add an `Examples/` test for any new construct.** The
  `StrataTest/Languages/Laurel/Examples/Fundamentals/T*.lean` tests are
  numbered by convention; add to the appropriate theme or create a new
  `T` number.

## Pipeline order (`LaurelCompilationPipeline.lean`)

```
FilterNonCompositeModifies → EliminateValueReturns →
HeapParameterization (needsResolves) → TypeHierarchyTransform (needsResolves) →
ModifiesClausesTransform (needsResolves) → InferHoleTypes → EliminateHoles →
DesugarShortCircuit → LiftExpressionAssignments →
EliminateReturns (needsResolves) → ConstrainedTypeElim (needsResolves) →
CoreGroupingAndOrdering → LaurelToCoreTranslator
```

Invariants across passes:

1. After `Resolution`, every identifier reference has a `uniqueId` that
   matches some declaration.
2. After `EliminateHoles`, the program contains no deterministic holes.
   Non-deterministic holes are preserved by `EliminateHoles` and lowered to
   havocs later, by `LiftExpressionAssignments`.
3. After `LiftExpressionAssignments`, every statement-like `StmtExpr`
   sits in a statement position. Expression positions contain only
   expression-like constructors.
4. After `LaurelToCoreTranslator`, the result is a valid Core program.

Breaking any of these invariants is almost always a bug, not a deliberate
relaxation.

## Reserved identifier prefixes

Emit these from passes; do **not** accept them as user identifiers:

* `$heap`, `$heap_in` — heap parameters.
* `$hole_N` — uninterpreted functions generated by `EliminateHoles`.
* `$__ty_unused_N` — fresh type variables used as "unknown type"
  placeholders.
* `$` prefix in general — reserved for translator-generated names.

## Error reporting

* Collect diagnostics; do not abort on the first error if you can
  meaningfully continue with a hole.
* Resolution errors abort the pipeline before Core to avoid duplicate
  diagnostics. If your pass produces resolution errors, add them to the
  Laurel diagnostics list and let the pipeline do the early return.
* The Laurel pipeline is meant to produce user-actionable diagnostics.
  "Not yet implemented" is an acceptable diagnostic for an unreachable
  case; a panic is not.

## Common bugs

| Symptom | Likely cause |
|---------|--------------|
| `holes should have been eliminated before translation` | New translator case emits a hole inside a container (e.g., `Block`, `PureFieldUpdate`) that `EliminateHoles` does not descend into. |
| `Resolution failed: 'X' is not defined` after a Laurel → Laurel pass | Pass generated a fresh identifier without adding a declaration, or rewrote a reference without re-running resolution. Mark the pass `needsResolves := true`. |
| `calls to procedures are not supported in functions or contracts` | A procedure call reached a pure-context `StmtExpr` (inside an `Assert`, `Assume`, `Quantifier`, or a contract expression). The upstream translator must bind the call to a local first. |
| `Impossible to unify` at Core type-check time | A Laurel type slipped through to Core without being lowered; check that every Laurel-specific `HighType` is handled in `LaurelToCoreTranslator.translateType`. |
| `could not infer type` inside `translateType` | A `HighType.Unknown` survived because `InferHoleTypes` could not pick it up. Either the hole had no context, or the containing constructor is not traversed by the inference pass. |
| Build times blow up | A recursive pass over `StmtExpr` was written without a termination proof. Use the helpers in `MapStmtExpr.lean` rather than hand-rolling traversal when possible. |

## Useful starting points

* Authoritative AST: `Strata/Languages/Laurel/Laurel.lean`.
* Pipeline orchestrator:
  `Strata/Languages/Laurel/LaurelCompilationPipeline.lean`.
* Unified AST traversal helpers: `Strata/Languages/Laurel/MapStmtExpr.lean`.
* Resolution: `Strata/Languages/Laurel/Resolution.lean`.
* Final translation: `Strata/Languages/Laurel/LaurelToCoreTranslator.lean`.
* Generated docs: open
  `docs/api/.lake/build/doc/Strata/Languages/Laurel/Laurel.html` or
  rebuild the Verso manual from `docs/verso/LaurelDoc.lean`.
