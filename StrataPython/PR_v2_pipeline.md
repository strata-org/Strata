# PR: Python→Core v2 pipeline (proof-relevant coercion in the Laurel resolver)

## Summary

This PR adds `pyAnalyzeV2` (invoked as `pyAnalyzeLaurel --v2`): a second Python→Core
analysis pipeline that sits beside the existing `pyAnalyzeLaurel` (v1). v1 stays the
default frontend and continues to back the CBMC/GOTO bridge (`pyAnalyzeLaurelToGoto`).
v2 is opt-in and is checked against v1 as its oracle.

v2's defining choice: coercion between Python's dynamic `Any` and concrete types is a
single, generic subtyping judgment in the Laurel resolver. The judgment returns the
coercion to apply; the Python frontend plugs in the concrete runtime functions that
realize it.

## The pipeline (v2)

`pyAnalyzeV2ToCore` (PySpecPipeline.lean) runs five stages.

1. **Read** — parse the pre-generated `.python.st.ion` into the Python AST.
   (`.py → .ion` is produced by `strata.gen py_to_strata`, with `PYTHON_DIALECT_ST_ION`
   set to `Tools/Python/dialects/Python.dialect.st.ion`.)

2. **Resolution** (`StrataPython/Resolution.lean`) — resolves every name over the Python
   AST: locals, parameters, fields, classes, methods, module-level locals, and builtins.
   It takes each declaration's type from the user's annotation, and treats a module-level
   `MyInt = int` as a type alias so later uses of `MyInt` resolve to `int`.

3. **Translation** (`StrataPython/Translation.lean`) — produces untyped Laurel. Every
   Python value is wrapped in `Any`; operators become runtime calls (`PAdd`, `PLt`, …);
   classes become composites; field reads and writes become `.Var (.Field obj f)` and
   `.Assign [.Field obj f] v`; object creation becomes `.New C`. This Laurel becomes
   well-typed only after exceptions are threaded, which is why elaboration runs next.

4. **Elaboration** (`Strata/Languages/FineGrainLaurel/Elaborate.lean`) — turns untyped
   Laurel into effect-typed (FGCBV) Laurel. It infers each procedure's grade in the
   monoid `{pure, proc, err}` and threads exceptions through the calling convention
   (`leftResidual` computes the residual grade for a continuation). The heap is handled
   later by `heapParameterizationPass`, which consumes the bare field/`New` nodes from
   stage 3. Elaboration's subsumption carries effects; pure-type coercion is the
   resolver's job (stage 5).

5. **Laurel → Core** (`translateCombinedLaurelV2` → `LaurelCompilationPipeline`) — the
   generic Laurel resolver assigns pure types and inserts coercions (below); the lowering
   passes run (heap parameterization, type hierarchy, contracts, …); the result is
   translated to Core and verified by SMT.

## Coercion

### One judgment (`Strata/Languages/Laurel/LaurelAST.lean`)

Subtyping returns the coercion that witnesses it:

```
inductive Coercion
  | refl                  -- equal types: apply the value unchanged
  | inject  (source)      -- a concrete value becomes `Any`        (boxing)
  | project (target)      -- an `Any` becomes a concrete type      (unboxing / downcast)
  | upcast                -- a composite becomes one of its ancestors
  | truthify (source)     -- a concrete value becomes `bool` in boolean context

def coerce (ctx) (sub sup) : Option Coercion
def isConsistentSubtype (ctx) (sub sup) : Bool := (coerce ctx sub sup).isSome
```

`coerce` decides subtyping using the type lattice (`unfold` for aliases/constrained
types, `gradualTypes` for the dynamic type, `ancestors` for composite inheritance) and
returns the kind of coercion required. `isConsistentSubtype` is defined as "`coerce`
succeeds," so the verdict and the coercion come from the same source.

`Any` is the dynamic type that boxes and unboxes (`inject`/`project`). `Unknown` is the
gradual wildcard for synth gaps and holes; it coerces by `refl`. Composite values relate
to ancestors by `upcast`. A value used where `bool` is expected coerces by `truthify`.

### The frontend realizes the coercion (`StrataPython/PySpecPipeline.lean`)

`coerce` yields an abstract verdict; the Python frontend supplies a realizer (threaded
on `TypeLattice` next to `gradualTypes`) that turns each verdict into the concrete
runtime call:

```
inject  int        → from_int            project  int        → Any..as_int!
inject  str        → from_str            project  str        → Any..as_string!
inject  float      → from_float          project  float      → Any..as_float!
inject  ListAny    → from_ListAny        project  ListAny    → Any..as_ListAny!
inject  DictStrAny → from_DictStrAny     project  DictStrAny → Any..as_Dict!
inject  Composite  → from_Composite      project  Composite  → Any..as_Composite!
truthify int       → int_to_bool         truthify str        → str_to_bool   (etc.)
refl, upcast       → the value unchanged
```

The judgment is generic; the runtime vocabulary is Python's, supplied at the call site.
A Laurel-native program supplies no realizer and runs with refl-only coercion.

### Insertion sites (`Strata/Languages/Laurel/Resolution.lean`)

`coerceTo` checks `actual ≤ expected` and applies the realized witness to the term. The
resolver calls it at each check-mode boundary it rebuilds:

- call arguments, return values, and functional bodies (the subsumption path in
  `Check.resolveStmtExpr`);
- the right-hand side of an assignment / annotated initializer (`Synth.assign`,
  `Check.assign`);
- datatype-constructor arguments (`getCallInfo` supplies the constructor's field types);
- precondition conditions (checked against `TBool`, so `truthify` applies).

The `from_Composite` / `Any..as_Composite!` bridge stubs are typed via the `re_Match`
composite, which the type-hierarchy pass flattens to the synthesized `Composite`
datatype, giving them the correct Core types at the point `Composite` exists.

## Files

New (v2): `StrataPython/Resolution.lean`, `StrataPython/Translation.lean`,
`Strata/Languages/FineGrainLaurel/Elaborate.lean` (+ dialect),
`StrataPython/Specs/Error.lean`, `Scripts/pyAnalyzeV2.lean`, and the wiring in
`PySpecPipeline.lean`, `Pipeline/PyAnalyzeLaurel.lean`, `Cli.lean`, `StrataMain.lean`.

Modified (generic, additive): `Strata/Languages/Laurel/LaurelAST.lean` (`Coercion`,
`coerce`, the realizer field on `TypeLattice`), `Resolution.lean` (`coerceTo` and its
insertion sites), `LaurelPass.lean` and `LaurelCompilationPipeline.lean` (thread the
realizer), `PythonRuntimeLaurelPart.lean` (the Composite bridge stubs and stubs for the
`type`/`abs`/`chr`/`ord`/`getattr`/`setattr` builtins).

## Verification

**Unit suite (220 tests, `--solver z3`):** 167 Analysis success, 47 Inconclusive,
4 Failures, 2 Internal error, 0 crash. The 2 internal errors come from ill-formed
input (an unannotated `c = Cell(1)`; an ill-typed `x:int=42; x="hello"`).

**Against v1 golden files (`expected_laurel/`, by RESULT):** 192/220 identical. The 28
differences:

- **14** are v1 Analysis success → v2 Inconclusive: on these v2 produces weaker
  verification conditions and proves less than v1. These are precision regressions
  (sound, but worse than v1). (bitnot, class_field_use, class_mixed_init,
  composite_return, datetime, datetime_now_tz, for_range, list_slice, regex_positive,
  timedelta_expr, try_except_{basic,modeled,scoping}, with_void_enter.)
- **2** are v1 Analysis success → v2 Internal error, both from ill-formed input v1
  tolerated (test_field_write, test_reassign_different_type).
- **2** are v1 Analysis success → v2 Failures found, from bugFinding-mode reachability
  precision (test_class_methods, test_class_with_methods).
- **10** are v2 producing a verdict v1 did not (v1 User error / Inconclusive / Known
  limitation → v2 Analysis success). These are pending a soundness audit.

So v2 is worse than v1 on 18 of 220 (14 precision + 2 internal + 2 bugFinding),
identical on 192, and possibly ahead on up to 10 (unaudited).

**Benchmarks (StrataInternalBenchmarks, 420 `.py`, bugFinding, 120s cap):** 78 Analysis
success, 225 Inconclusive, 26 Failures, 57 Internal error, 35 timeout. v1 was not run on
this corpus, so this is a standalone v2 number, not a comparison.

## Follow-ups

- Root-cause the 14 precision regressions (v1 success → v2 inconclusive).
- Audit the 10 v2-ahead cases for soundness.
- Triage the 57 benchmark internal errors; the 35 benchmark timeouts are speed, not
  correctness.
- v2 is a parallel, opt-in pipeline; it does not replace v1 in this PR.
