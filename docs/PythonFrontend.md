# Strata's Python Front-End

## Overview

The Python front-end translates annotated Python programs into Strata's Core
intermediate representation so that they can be analysed by Strata's deductive
verifier (`pyAnalyzeLaurel`) or compiled through to CBMC GOTO programs
(`pyAnalyzeLaurelToGoto`).

The front-end is intentionally scoped. It does not attempt to model arbitrary
Python. Its target is the subset of Python that AI coding agents typically
produce when gluing together calls to external libraries: fully type-annotated
procedural code that invokes library APIs described by PySpec, raises a
handful of exception types, and avoids the more dynamic corners of the
language. Within that subset the aim is *sound* analysis — if the tool
reports "no bugs" then, modulo known specification gaps, there really are
none.

This document describes:

1. The pipeline from a Python `.py` file to a Core program.
2. The `Any`-boxed value encoding that underpins everything the front-end
   produces.
3. The PySpec mechanism that describes external library functions.
4. What is supported and what is *not*.
5. Where soundness hinges on translator-inserted tag checks rather than
   Strata's own type system.

Read this together with [`Architecture.md`](Architecture.md) for background
on Strata's dialects and Core type system.

## The pipeline at a glance

```
┌──────────────┐   ReadPython        ┌──────────────────┐
│ Python .py   │ ───────────────────▶│ Python AST       │
└──────────────┘   (cpython-derived) │ (DDM dialect)    │
                                     └────────┬─────────┘
                                              │ PythonToLaurel
                                              ▼
┌──────────────┐   pySpecToLaurel    ┌──────────────────┐
│ PySpec .ion  │ ───────────────────▶│ Laurel program   │
│ (libraries)  │                     │ (Any-boxed)      │
└──────────────┘                     └────────┬─────────┘
                                              │ Laurel→Core
                                              │ (resolution,
                                              │  heap param.,
                                              │  hole elim., ...)
                                              ▼
                                     ┌──────────────────┐
                                     │ Core program     │
                                     └────────┬─────────┘
                                              │
                      ┌───────────────────────┴───────────────────┐
                      ▼                                           ▼
            ┌────────────────────┐                     ┌────────────────────┐
            │ Core Verifier      │                     │ GOTO emission      │
            │ (VCG + SMT)        │                     │ (CBMC backend)     │
            └────────────────────┘                     └────────────────────┘
```

The two user-facing commands are:

* `strata pyAnalyzeLaurel` — runs the full pipeline into SMT-based deductive
  verification.
* `strata pyAnalyzeLaurelToGoto` — stops after Core and emits CBMC GOTO JSON.

Both consume the same `.python.st.ion` file (produced by the cpython-based
`Tools/Python` reader).

## Stage 1: Python to Laurel

Code: [`Strata/Languages/Python/PythonToLaurel.lean`](../Strata/Languages/Python/PythonToLaurel.lean)
(~3000 lines).

This is the single largest piece of the front-end. It walks the Python AST and
produces Laurel statements. Each Python construct is translated under the
following conventions:

### Every user value is `Any`

All user-defined variables, procedure arguments, and return values are typed
`Any` at the Laurel/Core level, regardless of their Python annotations. `Any`
is an inductive datatype defined in
[`PythonLaurelCorePrelude.lean`](../Strata/Languages/Python/PythonLaurelCorePrelude.lean):

```
datatype Any () {
  from_None (),
  from_bool (as_bool : bool),
  from_int  (as_int : int),
  from_float (as_float : real),
  from_str (as_string : string),
  from_datetime (as_datetime : int),
  from_bytes (as_bytes : string),
  from_DictStrAny (as_Dict : DictStrAny),
  from_ListAny (as_ListAny : ListAny),
  from_ClassInstance (classname : string, instance_attributes : DictStrAny),
  from_Slice (start : int, stop : OptionInt),
  exception (get_error : Error)
}
```

Under this encoding:

* A Python `int` literal `42` becomes `from_int(42)`.
* `x + y` on Python `int`s becomes
  `from_int(Any..as_int!(x) + Any..as_int!(y))`, bracketed by tag checks.
* A class instance is `from_ClassInstance("MyClass", <attrs>)`.
* An exception is `exception(<error>)` so that error propagation can be
  threaded through assignments without branching.

### Type checking = tag checking

Strata Core uses Hindley–Milner inference (see
[`LTy.lean`](../Strata/DL/Lambda/LTy.lean)). At the Core level the checker
only sees `Any` everywhere, so the real "type checking" is done by the
translator: before it emits `Any..as_int!(x)` it emits an assertion of
`Any..isfrom_int(x)`, and after computing a Python expression whose annotated
type is `int` it rewraps the result with `from_int`.

This is sound *if* the translator inserts all the right tag checks. Strata's
type system cannot catch a translator bug that drops one. Treat the translator
as the trusted part of the chain.

### Statements and control flow

The translator supports the following statement forms:

* Assignments, including augmented assignments (`x += 1`).
* `if/elif/else`.
* `while` and `for` (for-loops with `range(...)` or iterable expressions are
  desugared to counter-driven while-loops).
* `try/except`. The translator threads a sentinel `maybe_except : Error`
  through the block: after every statement that might raise, an `if
  isError(maybe_except) then exit exception_handlers_N` is inserted, and the
  `except` handlers are emitted as labelled blocks that the exit jumps to.
* `return`, `break`, `continue`, `pass`.
* Class and function definitions (see below).

### Procedure calls

Every Python call goes through `translateCall`, which distinguishes:

1. **User-defined functions** in the same file — translated as Laurel
   procedure calls using the locally gathered signatures.
2. **PySpec-modelled functions** (external libraries) — translated using the
   spec's pre/postconditions and return shape.
3. **Unmodelled calls** — translated to a `.Hole` placeholder, which the
   eventual hole-elimination pass turns into a fresh uninterpreted function
   call. Receiver objects and `Any`-typed arguments are havoc'd because the
   call may mutate them.

The translator inserts exception-check assertions around calls that may raise
— for a call `f(...)` that is declared to possibly return `Any|exception`,
the translator emits
`assert !Any..isexception(<result-variable>)` *after* the assignment, so that
downstream code does not silently continue with an exception in hand. When
the expression `f(...)` appears in a position where an embedded assert would
violate purity rules (e.g. inside an `if` condition, a `while` guard, a `for`
iterable, or another assignment RHS), the call is first extracted into a
temporary variable (see PR #1012 for the precise transformation).

### Classes

Classes are translated as Laurel composite types. A Python class becomes:

* A composite declaration listing each `self.field` encountered during
  translation (fields are inferred, not declared upfront, so classes without
  `__init__` initialisers still produce a complete composite).
* One procedure per method. Method names are mangled as
  `ClassName@methodName` to avoid clashes across classes.
* A heap parameterization pass later turns `self.field` reads/writes into
  `readField`/`updateField` on a common `Heap` parameter.

Inheritance is *not* modelled with subtyping. Classes involved in an
inheritance hierarchy are flagged in `classesInHierarchy`; method calls on
such classes are conservatively turned into holes (see PR #1019), because
dynamic dispatch is beyond what the `Any` encoding can recover after the
translation step.

### Holes

The translator emits `StmtExpr.Hole` whenever it cannot faithfully model a
construct. Later passes (`InferHoleTypes`, `EliminateHoles`) annotate each
hole with a type recovered from the surrounding context and replace it with
a call to a fresh, uninterpreted `$hole_N` procedure. The verifier can then
either havoc the result (bug-finding mode) or treat it as an arbitrary value
consistent with its type (deductive mode).

## Stage 2: PySpec — describing external libraries

Code: [`Strata/Languages/Python/Specs/`](../Strata/Languages/Python/Specs),
pipeline in
[`PySpecPipeline.lean`](../Strata/Languages/Python/PySpecPipeline.lean).

PySpec is the companion format that describes the external surface the user
code talks to: third-party libraries and parts of the standard library. A
PySpec file is itself a Strata program (in the `PythonSpecs` dialect) written
as an `.ion`. Large specs are typically generated offline from an upstream
API description (type stubs, interface definition files, service models) and
then compiled to `.pyspec.st.ion` by Strata.

A PySpec declaration is roughly:

```
composite KeyValueStore {
  function get_item(self : KeyValueStore, **kwargs : dict(container : str, key : str, ...)) -> dict(value : bytes, ...) {
    requires kwargs.container.length >= 3
    requires regex(kwargs.key, "^[^/]+(/.+)?$")
    ensures response.value is_bytes
    ...
  };
  ...
}
```

At translation time the front-end:

1. Reads the compiled PySpec Ion files selected by the `--pyspec` and
   `--dispatch` module-name flags (and any auxiliary modules they pull in),
   resolving each module name against the directory passed to `--spec-dir`.
2. Indexes overload tables so that a Python call like `store.get_item(...)`
   can be dispatched to the right PySpec procedure based on the argument shape
   (upstream API descriptions frequently have overloaded signatures).
3. Produces a Laurel procedure per PySpec procedure. The pre/post-conditions
   become Laurel `requires`/`ensures` clauses; the declared parameter
   constraints (regex, length, range, enum literals) become assertions inside
   the requires.

Because a library's full spec can easily run to thousands of procedures,
PySpec Ion files are compiled offline and cached on disk. In this repository,
the compilation step is exposed as the `pySpecs` subcommand:

```
lake exe strata pySpecs <python-source-dir> <output-dir>
```

which walks the source directory for `.py` stub files and emits one
`<module>.pyspec.st.ion` per module into the output directory. `--module`
restricts the run to selected modules and `--skip` excludes specific
top-level definitions. The resulting directory is then what gets passed to
`pyAnalyzeLaurel` as `--spec-dir`.

### The `--dispatch` flag

When the spec tree contains a top-level `<package>.pyspec.st.ion` (or
`<package>/__init__.pyspec.st.ion`) that exposes a factory, passing
`--dispatch <package>` makes the front-end load its dispatch table, so that
a call like `pkg.client("service-name")` resolves statically to the matching
composite. Without this, calls on the returned object fall back to holes.

## Stage 3: Laurel to Core and beyond

From Laurel onwards the pipeline is common to all front-ends:

1. **Resolution** annotates identifier uses with the declarations they refer
   to ([`Resolution.lean`](../Strata/Languages/Laurel/Resolution.lean)).
2. **Heap parameterization** lowers `self.field` access to
   `readField`/`updateField`
   ([`HeapParameterization.lean`](../Strata/Languages/Laurel/HeapParameterization.lean)).
3. **Hole elimination** assigns types to `Hole` expressions and replaces them
   with fresh procedures
   ([`InferHoleTypes.lean`](../Strata/Languages/Laurel/InferHoleTypes.lean),
   [`EliminateHoles.lean`](../Strata/Languages/Laurel/EliminateHoles.lean)).
4. **Laurel-to-Core translation**
   ([`LaurelToCoreTranslator.lean`](../Strata/Languages/Laurel/LaurelToCoreTranslator.lean))
   yields a Core program that is then type-checked and verified (or compiled
   to GOTO).

For deductive verification, the verifier then performs standard Core VC
generation and discharges the VCs through the SMT solver. Bug-finding mode is
similar but uses non-deterministic havoc instead of quantified universals on
the uninstantiated hole procedures.

## Supported Python subset

What the front-end handles well:

* Functions with complete `int`/`str`/`bool`/`float`/`bytes` annotations.
* `list`, `dict[str, Any]` with value semantics (see caveat below).
* Classes with `__init__`, regular methods, simple field access.
* `try/except` for a known exception type, and raising exceptions by
  instantiating them.
* External library calls (via PySpec), including auto-generated input
  validation and result narrowing.
* The `__name__ == "__main__"` idiom (kept as a plain `if`).
* Arithmetic, comparisons, and boolean combinators on boxed `Any` values.

## What is not supported (and why)

### Rejected outright

* Metaclasses, `__getattr__`, `__setattr__`, `__dict__` mutation.
* `eval` / `exec`.
* Generators and coroutines (`yield`, `async`, `await`).
* Closures / lambdas. Laurel has no first-class closures.
* Arbitrary decorators.
* Multiple inheritance / MRO-dependent behaviour.

These are not representable in the `Any` encoding without a heap-allocated
code model which Strata does not have.

### Collapsed to untyped

* Union types (`X | Y`), `Optional[X]`. The translator encodes these by
  erasing to `Any`; individual PySpec stubs occasionally introduce hand-rolled
  pairs such as `StrOrNone`, but there is no general union machinery.
* `TypedDict`, `Protocol`, `@overload`, `Literal`, `Callable`,
  `TypeGuard`/`TypeIs`, `Self`, `ParamSpec`. The Core type system has no
  subtyping, variance, row types, or intersection/constraint solving, so
  these annotations are stripped and replaced with tag checks where
  possible.
* Flow-sensitive narrowing (`if isinstance(x, int): x + 1` does not give `x`
  the type `int` in the branch). The Core checker is flow-insensitive;
  narrowing must be encoded manually via tag checks.

### Unusable libraries

Frameworks that rely on metaclasses, descriptors, dynamic class generation,
runtime reflection, or non-trivial C extensions are effectively outside the
supported subset: Django, SQLAlchemy, pydantic, NumPy, pandas, PyTorch, attrs,
FastAPI/Flask at the framework layer, pytest fixtures. Using any of these
typically leads to unmodelled calls being havoc'd into holes, which in turn
drives SMT verification toward "inconclusive".

### Aliasing and identity

Mutable containers (`list`, `dict`) are encoded as *value-semantics*
inductive datatypes (`ListAny`, `DictStrAny`), not as heap references. This
means the model does not capture aliasing: after `c = a; a.append(4)`, the
Python runtime has `c == a` with the appended element visible in both, but
the Strata model has `c` unchanged. Similarly, Python's `is` and user-defined
`__eq__`/`__hash__` are not modelled. This is a known latent unsoundness that
can affect verification results on code that relies on aliasing.

## Soundness posture

* **Tag checks are the contract.** Every place a Core expression consumes a
  specific constructor (e.g. `as_int`) must be preceded by a Strata assertion
  that the corresponding `isfrom_*` holds. The translator is responsible for
  inserting these; a missing one is a soundness bug.
* **PySpec correctness is assumed.** When a PySpec procedure states a
  postcondition, the verifier trusts it. Specs generated from upstream API
  descriptions inherit the same trust.
* **Holes are sound by construction.** Each hole becomes a fresh
  uninterpreted procedure; the verifier treats its outputs as arbitrary
  values consistent with their type. This is sound but often imprecise — a
  typical "inconclusive" result traces back to a hole.
* **Aliasing is unsound** as noted above.
* **Everything else follows from Strata's Core type system**, whose
  soundness is backed by Lean proofs in
  [`LTyUnify.lean`](../Strata/DL/Lambda/LTyUnify.lean) and surrounding files.

## Where to look in the code

| Concern | File |
|---------|------|
| AST reading (cpython dialect) | [`ReadPython.lean`](../Strata/Languages/Python/ReadPython.lean) |
| Any-box prelude and error type | [`PythonLaurelCorePrelude.lean`](../Strata/Languages/Python/PythonLaurelCorePrelude.lean) |
| Python→Laurel (statement translation) | [`PythonToLaurel.lean`](../Strata/Languages/Python/PythonToLaurel.lean), `translateStmt` |
| Python→Laurel (expression translation) | Same file, `translateExpr` |
| Unmodelled-call handling | Same file, `translateCall` |
| PySpec ingest and dispatch | [`PySpecPipeline.lean`](../Strata/Languages/Python/PySpecPipeline.lean), [`Specs/`](../Strata/Languages/Python/Specs) |
| Overload table | [`OverloadTable.lean`](../Strata/Languages/Python/OverloadTable.lean) |
| Laurel resolution | [`Resolution.lean`](../Strata/Languages/Laurel/Resolution.lean) |
| Hole lifecycle | [`InferHoleTypes.lean`](../Strata/Languages/Laurel/InferHoleTypes.lean), [`EliminateHoles.lean`](../Strata/Languages/Laurel/EliminateHoles.lean) |
| Laurel→Core | [`LaurelToCoreTranslator.lean`](../Strata/Languages/Laurel/LaurelToCoreTranslator.lean) |
| Command dispatch | `pyAnalyzeLaurelCommand`, `pyAnalyzeLaurelToGotoCommand` in [`StrataMain.lean`](../StrataMain.lean) |

## Related reading

* [`Architecture.md`](Architecture.md) — how dialects compose in Strata.
* [`CoreToGOTO_Gaps.md`](CoreToGOTO_Gaps.md) — what doesn't translate to GOTO
  once the Python front-end has done its job.
* [`GettingStarted.md`](GettingStarted.md) — tutorial walkthroughs, including
  a small Python example.
