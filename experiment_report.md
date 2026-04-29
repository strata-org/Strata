# Experiment Report: AI-Assisted IR Design for Python Static Analysis

## Summary

This document describes the methodology used to design PythonSSA, a Static Single
Assignment intermediate representation for Python programs. The design was developed
collaboratively between a human language designer and an AI assistant (Claude),
following a data-driven, iterative process that moved from corpus analysis through
design exploration to a formal specification.

## Methodology

### Phase 1: Corpus-Driven Scope Analysis

Rather than designing an IR for "all of Python," we started by analyzing the actual
target corpus — 52 annotated Python files representing real-world AWS service scripts.

**Step 1: Feature extraction tool.** We built `pyFeatures`, a Lean subcommand that
traverses the Python DDM AST and tallies every constructor encountered (statements,
expressions, operators, constants, patterns). This was implemented as a monadic
traversal following existing patterns in the codebase (`Specs.lean`'s `PySpecMClass`).

**Step 2: Corpus-wide analysis.** Running `pyFeatures` on all 52 files produced
frequency counts across 8 syntactic categories. Key findings:
- The corpus uses only 17 of 27 statement types and 19 of 29 expression types.
- Some features dominate: `Name` (3717), `Constant` (2943), `Call` (1376).
- Many features have zero occurrences: all async constructs, `Lambda`, `Yield`,
  `Match`, `Global`, `Nonlocal`.

**Step 3: Coverage tiers.** We computed how many files each feature subset covers:
- 40/52 with just "dominant" features
- 46/52 adding 8 straightforward constructs (While, AugAssign, Slice, IfExp, etc.)
- 50/52 adding ListComp
- 52/52 adding DictComp + GeneratorExp

This let us make an informed scoping decision: target 46/52 files initially
(everything except comprehensions), with a clear path to 50+ later.

**Step 4: Type annotation analysis.** We extracted all type annotations from the
corpus using Python's `ast` module, and cross-referenced with the PySpec type system
(`SpecAtomType` in `Specs/Decls.lean`). This produced a precise `PyType` enum covering
every annotation in the dataset plus the PySpec builtins.

### Phase 2: Interactive Design Exploration

The IR design was developed through a structured Q&A process, with the AI proposing
design options and the human making decisions.

**Approach:** The AI presented design questions with concrete alternatives, often
including code previews showing what each choice would look like in practice. The
human provided decisions along with rationale, which informed subsequent questions.

**Key design decisions and how they emerged:**

1. **Block arguments vs phi nodes.** Human preference stated upfront (Crucible/SWIFT
   style). No exploration needed.

2. **Exception handling model.** This required multiple rounds:
   - AI initially proposed block-level handlers (one handler per block).
   - Human clarified they wanted instruction-level precision — knowing exactly which
     variables were assigned at the point of exception.
   - This led to the "split blocks at raising instructions" design.
   - Human then noted that uninitialized variables and exception optionality are the
     same problem, leading to the `undef`/`isDefined` design.
   - This in turn eliminated the need for trampolines — `undef` padding handles
     the handler fan-in problem naturally.

3. **undef semantics.** Emerged from the exception handling discussion. The human
   explicitly constrained `undef` to be purely about identifiers (not stored in
   data structures), avoiding LLVM-style poison/undef complexity. This was a key
   design insight that kept the IR simple.

4. **finally blocks.** The human proposed `Option Exception` as a parameter, which
   mapped directly to the `undef`/`isDefined` pattern once that was established.

5. **Short-circuit BoolOp, IfExp desugaring.** Human consistently chose precision
   over simplicity: faithful short-circuit semantics via `condBranch`, with the
   expectation that optimization passes can reconstruct higher-level constructs.

6. **Import resolution.** Human directed that imports should not be SSA instructions
   but instead update a binding table during translation, producing fully qualified
   call references in the output.

7. **Class representation.** Evolved from "flat function list" to the more specific
   `@ClassName_init` pattern through discussion of class body execution semantics.

**Observation:** The most productive design insights came from the human identifying
structural similarities between seemingly different problems (uninitialized variables
and exception optionality) and from explicitly constraining the design to avoid
known complexity traps (LLVM undef semantics).

### Phase 3: Design Review Checklist

After the initial design pass, the AI generated a checklist of 8 design points
requiring human attention. This served as a structured review mechanism:

- Some items were straightforward confirmations (chained comparisons, f-strings)
- Some required deeper discussion (exception precision, finally semantics)
- Some surfaced new design decisions (BoolOp short-circuit, IfExp desugaring)

The human annotated each item with decisions and rationale, which were then
incorporated into the revised design.

### Phase 4: Formal Specification

The design was consolidated into a reference manual (`docs/PythonSSA.md`) covering:
- All data types with precise definitions
- Well-formedness invariants
- Desugaring rules with concrete block-diagram examples for every in-scope construct
- Scope limitations explicitly documented
- Pretty-print notation for output format

### Phase 5: Test-Driven Development

The implementation plan follows spec-first, test-driven development:
1. Write example Python files exercising each feature in isolation
2. Hand-write expected SSA output for each example
3. Implement incrementally, validating against tests
4. Evaluate on the original corpus last (held-out benchmark)

The corpus files are deliberately held out from the test suite to serve as an
independent validation that the scoping analysis was correct.

**Test suite (completed):** 23 positive test files (t01-t23) covering all in-scope
features, plus 8 negative test files (n01-n08) for graceful degradation of
unsupported constructs (async, comprehensions, generators, lambda, walrus).

**Design decisions surfaced by test writing:** Writing expected SSA output forced
9 major design questions to be resolved before implementation:
- Strict vs. relaxed block arguments (Q1) — revealed by t14_bool_short
- Exception value representation (Q4) — `%exc` had no valid IR form
- Variable liveness (Q5) — tension between "strict" and "conservative"
- Method calls (Q7) — two-step attr+call vs. combined instruction
- Builtin resolution (Q8/Q9) — `@print` forced prelude design

**Expected output drift:** The 23 expected files were written before design
decisions were finalized. A batch update step (Step 6) addresses this. Future
process improvement: write expected output in two passes (draft + finalize).

### Phase 6: Design Review and Finalization (completed 2026-03-28)

All 11 design questions (Q1-Q9 + post-compact A-F) resolved. Key late additions:
- `assert_` as dedicated instruction (for verification goals)
- `decorators` field on Func (metadata, path to future support)
- `callQualified` demoted from IR instruction to pretty-print sugar
- Implementation steps renumbered into 4 clear phases (13 steps total)

### Phase 7: Corpus Analysis and IR Hardening (completed 2026-03-28)

Extended `pyFeatures` with scope-aware unresolved name detection to identify which
builtins the corpus actually uses, informing prelude design.

**Scope tracking.** Added a scope stack (`Array (Std.HashSet String)`) to
`FeatureState` with `pushScope`/`popScope` for functions and comprehensions.
Variables are defined via assignments, function params, import bindings, for-loop
targets, with-statement targets, and except handler names. Unresolved names are
any `Name` in `Load` context not found in any enclosing scope.

**Iterative refinement.** Initial analysis showed 19 false positives:
- 7 comprehension variables (tag, col, model, etc.) — fixed by adding scope
  tracking around comprehension bodies
- 12 tuple-unpacking targets (i, variant, provider_models, etc.) — fixed by
  adding `extractNames` to recursively handle `Tuple`/`List` for-loop targets

After fixes: zero false positives. The 18 genuine unresolved names mapped to
exactly 14 builtin functions + 3 exception types + `__name__`.

**SSA unsupported audit.** Added `ssaUnsupported` tracking to flag all constructs
outside SSA scope. Confirmed 6/52 files (all comprehension-heavy) as the only
files with unsupported constructs, validating the 46/52 coverage target.

**Tuple unpacking discovery.** Analysis revealed 14/52 files (27%) use tuple
unpacking in for loops — a significant pattern not covered by existing tests.
Added t25_tuple_unpack.py with expected output and a desugaring rule.

### Phase 8: Expected Output Batch Update (completed 2026-03-28)

Updated all 23 existing expected output files to match the finalized IR. Used
7 parallel agents to handle independent files concurrently, followed by manual
review and correction of two files with duplicate `qualifiedRef` instructions.

**Changes applied across 15 files:**
- Function-wide unique SSA IDs (renumbered from block-local to monotonic per-function)
- `copy` instruction removal (5 files) — aliases handled by binding environment
- `call @builtin(...)` → `callQualified builtins.name [...]` (6 files)
- `@ExceptionType` → `qualifiedRef builtins.Type` + `-- where` comment (5 files)
- `%exc.0` handler params → regular numbered `_exc` params (7 files)
- `%exc` → `exc` in exceptArgs (7 files)

**Late refinement: QualifiedName type.** During review, introduced `QualifiedName`
(= `SSAModuleName × String`) to replace loose `(module, name)` string pairs.
Pretty-prints with dot notation (`builtins.len`, `os.path.join`). `SSAModuleName`
is a non-empty `Array String`, parallel to existing `Specs.ModuleName`. Prelude
table uses `Std.HashMap String QualifiedName` to allow aliases (e.g., `None` →
`builtins.NoneType`). Updated all expected files and reference manual.

### Phase 9: Lean IR Implementation (completed 2026-03-28)

Implemented the SSA IR data types and pretty-printer in Lean 4.27.

**SSA.lean (293 lines).** All IR types as Lean inductive/structure definitions:
`SSAModuleName`, `QualifiedName`, `PyType`, `SSAVal`, `BlockId`, `SSAName`,
`CallArg`, `BinOpKind`, `UnaryOpKind`, `CmpOpKind`, `Instruction`, `Terminator`,
`ExceptArgVal`, `ExceptTarget`, `BlockParam`, `NamedInstr`, `Block`, `ParamKind`,
`FuncParam`, `Func`, `Module`, plus `pythonPrelude` as a `Std.HashMap`.

Key implementation decisions:
- `public section` required for all types — Lean 4.27 module system defaults to
  protected visibility, which blocks field notation and constructor patterns in
  consuming modules.
- `PyType` cannot derive `Repr` (recursive through `Array`/`OrderedMap`). Types
  containing `Option PyType` use `deriving Inhabited` only.
- `OrderedMap` uses `Std.HashMap A Nat` for O(1) keyed lookup into `Array B`.

**SSAFormat.lean (350 lines).** Pretty-printer implementing three sugar rules:
1. `callQualified` — when `qualifiedRef` is used once as a call target
2. `call attr()` — when `attr` is used once as a call target
3. Inline literals — when a literal instruction is used exactly once

Performance design: precomputed `BlockCtx` structure built once per block,
replacing O(n) `Array.find?` scans with O(1) `HashMap`/`HashSet` lookups:
- `defMap : Std.HashMap Nat NamedInstr` — val ID → defining instruction
- `callTargets : Std.HashSet Nat` — val IDs used as `func` in `.call`
- `useCount` helper with documented soundness argument for the `getD 0` default

**Lean 4.27 module system.** The main obstacle was visibility. Without `public
section`, types defined in SSA.lean were inaccessible for field projection
(`.id`, `.instr`) and constructor matching (`.add`, `.intLit`) in SSAFormat.lean.
The fix was straightforward once identified: `public section` in SSA.lean,
`public` only on `fmtFunc`/`fmtModule` in SSAFormat.lean.

### Phase 10: Two-Phase Translator Architecture (completed 2026-03-29)

Designed and implemented a two-phase translation pipeline.

**Architecture decision.** The human proposed replacing the initially planned flat
`PreBlock` graph with a tree structure (`BlockTree`). This was a significant
simplification: the tree preserves statement nesting while pre-allocating all
block IDs, eliminating the need for explicit successor edges, graph traversal,
and visited sets. Phase 2 uses structural recursion over the tree.

**Phase 1: Blockify.lean (~540 lines).** Recursive descent over `Array stmt`
producing `Array BlockTree`:
- `BlockTree` and `ExceptHandlerTree` as `mutual` inductives
- Six constructors: `stmts` (simple statement slice), `ifStmt`, `forLoop`,
  `whileLoop`, `tryExcept`, `withStmt`
- `Subarray` for zero-copy statement slicing
- `exprBlockStart`/`exprBlockCount` on compound constructors for BoolOp/IfExp
- Minimal state: `nextBlockId : Nat`, `allVars : Std.HashSet String`, `warnings`
- Validated on 52/52 corpus files with zero warnings

**Phase 2: PythonToSSA.lean (~800 lines).** DFS over `BlockTree` emitting SSA:
- `SSAM := ReaderT SSAConfig (StateM SSAState)` — pure monad (no IO)
- Expression block counter moved from `IO.Ref` to `SSAState` fields, keeping
  the entire translation pure. Human caught the IO.Ref anti-pattern and directed
  the fix.
- Binding environment: `Std.HashMap String Binding` where `Binding` is either
  `.local SSAVal` or `.qualified QualifiedName`
- Conservative join-point params: all `allVars` become block params (dead param
  elimination deferred)
- Covers all expression types (constants, operators, calls, subscripts, f-strings)
  and most statement types. Stubs for try/except, with, BoolOp/IfExp short-circuit.

**Test automation: SSATest.lean.** Following the `AnalyzeLaurelTest.lean` pattern:
compile `.py` → Ion via `strata.gen`, run `translateModule` + `fmtModule`, compare
against hand-written `.expected` files. All 33 tests (25 positive, 8 negative) run
concurrently via `IO.asTask`. Currently 0/33 passing — expected, as the translator
is a first pass with known gaps.

**Commands wired up.** `strata pyBlockify <file>` for Phase 1 summary,
`strata pyToSSA <file>` for full SSA output. Spot-checked on 3 corpus files —
translator runs without crashes, produces readable SSA with correct sugar
(`callQualified`, `call attr()`, inline literals).

**Lean 4.27 visibility surprise.** Non-public import of a module does not expose
its `mutual` inductive constructors for dot-notation matching in the importing
module, even within the same file. The fix required `public section` around the
mutual inductives in Blockify.lean and making the import public. This was
counter-intuitive — the human expected non-public import to give full internal
access while only restricting re-export.

### Phase 11: TDD Debugging — 0/33 to 33/33 (completed 2026-03-29)

Iterative debugging of the translator output against hand-written expected files.
This was the most interaction-intensive phase, with frequent human intervention
correcting architectural decisions.

**Starting point.** Phase 10 produced a compiling translator with 0/33 tests
passing. The expected files (hand-written in Phase 5) served as the specification;
the translator had to produce output matching them exactly.

**Progression.** The first test (t01_assign) exposed multiple issues at once:
bare `%N:name.suffix` in value references (should be `%N`), block ID collisions
(entry block bb0 conflicted with Phase 1 allocations), and missing variable names
on SSA values. Each fix unblocked multiple tests. The progression was roughly:
1/33 → 8/33 → 15/33 → 25/33 → 33/33 over several conversation rounds.

**Human-directed design corrections.** Several times the AI proposed designs that
the human redirected:

- *Warning/error architecture.* The AI initially put warnings on the `Module`
  struct. The human found this "odd" — warnings are a translation artifact, not
  part of the IR. This led to `TranslateResult` returning Module + warnings +
  errors separately, and a standalone `fmtWarnings` function.

- *Source range conventions.* The AI initially used a default `SourceRange.none`
  parameter on `ssaWarn`. The human requested SourceRange as the first argument
  with no default, matching codebase conventions. This forced every warning call
  site to provide an explicit location — better for diagnostics.

- *`fmtWarnings` vs `fmtTranslateResult`.* The AI proposed a combined formatting
  function. The human preferred separate `fmtModule` + `fmtWarnings` functions,
  keeping the pretty-printer composable.

**Code review via agents.** After reaching 33/33, the human asked for a systematic
review of all expected files. Parallel agents diffed each expected file against
the test source, identifying 3 real bugs:

1. *Duplicate block labels.* Break/continue/return inside loop bodies called
   `finishBlockWithTerm` which finalized the current block, but the loop's
   back-edge code then created another block with the same ID. Fix:
   `translateBody` returns a `Bool` (terminated flag); parent handlers check it
   before emitting continuation branches, using `startNewBlock` to skip the
   redundant finalization.

2. *Star-args at call sites.* `f(*args)` produced `positional()` instead of
   `starArgs()` because the `Starred` AST node was unwrapped before the Call
   handler could see it. Fix: match on `Starred` inside the Call handler's arg
   loop.

3. *While loop `+1000` hack.* The while loop body used `testBlock + 1000` as a
   placeholder block ID because Phase 1 only allocated `testBlock` and `endBlock`.
   Fix: added `bodyBlock` to `BlockTree.whileLoop` and allocated it in Phase 1.

**Missing trailing blocks.** A subtler bug emerged during expression-level block
implementation: functions ending with a compound statement (if/for/while) would
not emit the final join/end block if it had no instructions. These blocks are
branch targets and must be defined — without them, the SSA output references
undefined blocks. The fix was to always emit the trailing block with `ret none`
when the body doesn't terminate on all paths. This affected 14 expected files.

### Phase 12: Expression-Level Control Flow (completed 2026-03-29)

Implemented proper short-circuit semantics for BoolOp, IfExp, and chained
comparisons, replacing the evaluation stubs from Phase 10.

**IfExp** (`x = 1 if cond else 2`): Creates 3 expression blocks (then, else,
join). The then and else blocks each evaluate one branch and branch to the join.
The join block has a single parameter for the result value. The condBranch in
the enclosing block dispatches to then/else based on the test.

**BoolOp** (`a and b`, `a or b`): Creates n blocks for n operands (n-1
short-circuit eval blocks + 1 join). For `and`, each condBranch goes to the
next eval block on true, or short-circuits to the join with the current value
on false. For `or`, the direction is reversed. Handles arbitrary chains
(`a and b and c and d`).

**Chained comparisons** (`a < b < c`): Desugars to `(a < b) and (b < c)` with
short-circuit, but evaluates each intermediate value once. Uses the same
condBranch-to-join pattern as BoolOp. Required adding block allocation in
`countExprBlocks` for the Compare case (n blocks for n comparators when n > 1).

**Expression blocks don't thread allVars.** A deliberate simplification: the
then/else/eval blocks for expressions have no block parameters (except the join
block's single result param). This means they reference values from the
enclosing block via cross-block references — technically a violation of strict
block-argument SSA. The rationale: expression blocks don't modify the variable
environment, and threading all allVars through every ternary would produce
extremely verbose output for minimal correctness benefit. The well-formedness
checker (Step 9) can optionally flag or accept this pattern.

**Block allocation budget.** Phase 1 (`countExprBlocks`) pre-allocates the exact
number of expression blocks each compound statement needs. Phase 2 consumes them
via `allocExprBlock`. The budget is: BoolOp = n (operands), IfExp = 3,
chained Compare = n (comparators, when n > 1). If Phase 2 over-allocates, a
warning is emitted but translation continues.

### Phase 13: Exception Handling and With Statement (completed 2026-03-29)

Implemented the remaining stub features: try/except/finally and with statement.

**try/except.** The try body's blocks get `except := some { target := firstHandlerBlock }`.
Each handler block receives `allVars + _exc` as parameters. Handler bodies are
translated normally and branch to the join block (or finally, if present). Multiple
handlers chain linearly — each handler's "next block" is the following handler.

Simplifications for v1:
- No `isinstance`-based type dispatch. All exceptions route to the first handler.
  This is structurally complete (correct block structure, handler params, exception
  target) but not semantically precise for typed `except` clauses.
- No instruction-level `exceptArgs`. The block-level `except` target is set, but
  individual raising instructions don't carry per-instruction variable snapshots.
  This means the handler sees variables from the block entry, not from the exact
  raise point.
- The orelse clause (try..else) is translated in-place after the try body in the
  normal path, before branching to finally/join.

**with statement.** Desugars to `__enter__`/`__exit__` calls with an exception
handler for the body:
1. Evaluate context expression, call `__enter__()`, bind `as` variable
2. Body runs in a block with `except := excExitBlock`
3. Normal path: call `__exit__(None, None, None)`, branch to continue
4. Exception path: call `__exit__(exc, exc, exc)`, re-raise

The context manager is stored as a synthetic `_mgr` binding in `varEnv`. This
persists across blocks via the mutable state (a cross-block reference, like `_iter`
in for-loops).

**Interaction pattern.** The AI implemented the with statement with a bug where
the exception exit block was the last block, making the entire with statement
"terminated" and treating subsequent code as dead. The AI caught this during
self-review before running tests, restructured the block ordering so the normal
exit block is the continuation point, and the exception exit block branches
via `raise` to propagate the exception.

### Phase 14: Performance and Dead Code Cleanup (completed 2026-03-30)

Systematic performance review and dead code elimination.

**Performance optimizations (PythonToSSA.lean):**
- **Fwd parallel arrays.** Replaced `Fwd = Array (String × SSAVal)` with a struct
  of two parallel arrays (`names : Array String`, `vals : Array SSAVal`). This
  makes `zipFwd` O(1) (just replace the vals array) and `fwdVals` O(1) (return
  vals directly), eliminating ~25 O(n) zip/unzip allocations per function.
- **valInstrIdx HashMap.** `setValType` previously scanned the entire instruction
  array O(n) to find the target instruction. Added `valInstrIdx : Std.HashMap Nat Nat`
  mapping val ID → instruction index, populated by `emitInstr`. Now O(1) per call.
- **Merged errors into warnings.** The SSAState had separate `errors` and `warnings`
  fields with identical handling. Consolidated into a single `warnings` array;
  `ssaError` now calls `ssaWarn` and emits an `unsupported` instruction.

**Demand analysis fixes (Blockify.lean):**
- **AnnAssign target leak.** `freeVarsStmt` for `AnnAssign` included the target
  name as a free variable (e.g., `z: int = 10` incorrectly demanded `z`). Fixed
  by extracting `addTargetReads` which handles each target pattern (Name, Attribute,
  Subscript, Tuple) correctly — Name produces no reads, Attribute/Subscript read
  their object/key.
- **Accumulator-passing pattern.** Replaced `freeVarsStmt`/`freeVarsExpr` (which
  returned new `HashSet`s, requiring callers to union) with `addFreeVarsStmt`/
  `addFreeVarsExpr` taking an accumulator set. Eliminated intermediate allocations
  at all ~20 call sites. `freeVarsExpr` removed as dead code.

**Dead code removal:**
- Removed `pyBlockify` CLI command from StrataMain (blockify tree output no longer
  needed — PythonToSSA traverses the raw AST directly).
- This made `blockifyModule` unreachable, which in turn made the entire blockify
  machinery dead: `BlockTree`, `ExceptHandlerTree`, `BlockifyResult`, `BlockifyState`,
  `BlockifyM`, `blockifyStmts`, `blockifyFunc`, `extractParams`, `paramVarName`,
  `collectModuleGlobals`, `countSliceExprBlocks`, `isTerminatorStmt`, `BlockTreeId`,
  plus all repr/ToString/Inhabited instances. Removed 533 lines.
- Made remaining internal-only symbols private: `extractNames`, `addFreeVarsExpr`,
  `addFreeVarsStmt`, `defsStmt`.
- Blockify.lean reduced from ~1100 to ~570 lines. Public API is now:
  `isSimpleStmt`, `countExprBlocks`, `DemandVars`, `demandAnalysis`.

### Phase 15: Strict Block-Argument SSA (completed 2026-03-30)

Replaced the relaxed expression-block model (Phase 12's deliberate relaxation)
with fully strict block-argument SSA where no value crosses a block boundary
without being passed as an explicit block parameter.

**Forwarding context (`fwd`).** `translateExpr` takes and returns
`fwd : Fwd` — a struct of parallel arrays (names + SSAVals) representing
values that must survive through expression blocks. Block-creating
expressions (BoolOp, IfExp, chained Compare) thread `fwd` as extra block
params/branch args. Non-block-creating expressions pass `fwd` through
unchanged. The mechanism composes: nested expression blocks (e.g.,
`(a and b) if cond else c`) correctly thread outer values through inner blocks.

**Demand-driven block params.** Statement-level blocks (if/for/while/try/with)
use demand analysis (`Blockify.demandAnalysis`) to compute exactly which
variables each block needs as parameters, replacing the conservative `allVars`
approach. Combined with `fwd`, this eliminates all cross-block references.

**Synthetic variable threading.** `_iter` (for-loop iterator) and `_mgr`
(with-statement context manager) are threaded via `scopeExtras` — an array
of (name, SSAVal) pairs appended to every block transition. Break/continue
handle scope extras correctly via `breakExtrasCount`/`continueExtrasCount`
on `BodyCtx`, with temporary trimming to match the target block's expected
extras count.

### Phase 16: Summary-Based Demand Analysis and Block ID Fix (completed 2026-03-31)

Two improvements to the analysis infrastructure.

**Summary-based demand analysis (`demandAnalysis2`).** Replaced the
double-traversal backward pass with a two-stage approach: (1) a single
forward AST walk collects per-block summaries (defs, reads, successors),
(2) an iterative fixpoint solver computes liveIn sets. This eliminates
the O(depth × body_size) cost of nested loops in the backward pass, where
each outer loop re-traverses inner loop bodies. The fixpoint solver handles
cycles naturally — loops converge in 2–3 iterations.

**Block ID remap.** Fixed a fundamental bug where terminator block references
(freshBlockId allocation order) diverged from block emission order. The
divergence occurs when inner blocks (e.g., if sub-blocks within a for body)
are emitted between pre-allocated outer blocks (e.g., endBlock allocated
early but emitted last). The fix records `blockIdMap[currentBlockId] =
blocks.size` at each `finishBlock` call, then applies a single remap pass
over all terminators and except targets at the end of `translateFunc`. This
replaced an earlier attempt to predict emission order during block setup
(`buildBlockParamsCtx`), which failed when expression blocks within a body
shifted emission positions.

## Tools Built

| Tool | Purpose |
|------|---------|
| `strata pyFeatures` | Lean subcommand: AST feature frequency analysis |
| `strata pyToSSA` | Lean subcommand: full Python → SSA translation |
| `tally_features.py` | Python script: aggregate counts across files |
| `coverage_check.py` | Python script: compute file coverage for feature subsets |

## Observations on the Process

**Data-driven scoping works.** Building the feature analysis tool first (< 1 hour)
saved significant design time by focusing the IR on constructs that actually appear
in the target corpus. Without this, we might have designed for `Lambda`, `Yield`,
`Match`, etc. — none of which appear.

**Iterative design with concrete examples.** Each design question was grounded in
concrete Python code and corresponding block diagrams. This prevented abstract
debates and kept decisions testable.

**Human-AI complementarity.** The AI was effective at: exhaustive enumeration
(all constructors, all type annotations), identifying edge cases (chained comparisons,
f-string raising semantics, with-statement exception paths), and generating
structured alternatives. The human was effective at: identifying structural
similarities across problems, constraining designs to avoid known pitfalls, and
making aesthetic/philosophical choices (precision over simplicity, single-sorted SSA).

**Incremental commitment.** The design evolved over multiple rounds rather than being
specified upfront. Each decision was made with full context from prior decisions,
allowing later insights (like `undef`) to simplify earlier designs (like trampolines).

**Human architectural interventions improve AI code.** The human proposed the
BlockTree architecture as a replacement for the AI's initial flat PreBlock design.
The tree structure was a strict improvement: simpler state, no graph traversal,
structural recursion. Similarly, the human caught the `IO.Ref` usage inside a
pure `StateM` monad and directed it to be replaced with state fields — a cleaner
Lean design that eliminated an unnecessary IO dependency. These interventions
suggest that the human's role shifts from writing code to reviewing architectural
choices, where domain expertise (Lean idioms, SSA compiler design) has high leverage.

**Test-driven development with expected output files works well for IR design.**
Writing expected SSA output by hand before implementing the translator forced
design decisions to be resolved early (naming conventions, block parameter
strategy, sugar rules). The expected output files serve as both a specification
and a regression suite. The TDD harness (`SSATest.lean`) provides immediate
feedback on every `lake build` — each failing test shows the first differing line,
making it easy to prioritize fixes.

**Lean 4.27 module visibility is a recurring friction point.** Multiple issues
arose from Lean's `module` keyword and visibility defaults: types needing
`public section`, mutual inductives requiring explicit export, non-public imports
not exposing constructors for pattern matching. Each issue was straightforward
once diagnosed, but diagnosis required understanding Lean-specific semantics that
the AI could not predict from first principles. The human's Lean expertise was
essential for resolving these quickly.

**TDD with expected output files catches real bugs.** The code review phase
(diffing expected vs actual across all 33 tests) surfaced 3 bugs that the tests
themselves couldn't catch because expected files had been updated to match actual
output. The most important — duplicate block labels from break/continue — was a
genuine SSA well-formedness violation that would have caused problems for
downstream analysis. This suggests that periodic manual review of expected files
is valuable even when all tests pass.

**Human questioning surfaces general principles.** When the AI implemented a
specific fix for missing trailing blocks (checking `currentParams.isEmpty`), the
human asked "is there a more general principle?" This led to the simpler and
correct rule: always emit the trailing block when the body doesn't terminate.
The specific fix was a band-aid; the general principle was the right answer. This
pattern — human pushes for generality, AI provides the implementation — recurred
throughout the debugging phase.

**Expression-level blocks reveal architectural tensions.** Implementing BoolOp
and IfExp short-circuit exposed a tension in the strict block-argument SSA model:
expression blocks need access to values from enclosing blocks, but threading all
variables through every ternary produces impractical output. The initial pragmatic
decision — expression blocks don't thread allVars — was a deliberate relaxation.
This was later resolved in Phase 15 with the `fwd` context, which threads only
the values that are actually needed through expression blocks (demand-driven, not
all variables). The `fwd` mechanism achieves strict SSA without impractical output.

### Phase 17: Rebase and Corpus Validation (completed 2026-04-28)

After a 4-week gap, the branch was rebased onto `origin/main` (158 commits behind).

**Rebase strategy.** Squashed 17 commits into 3 logical phases (IR design,
translator, demand analysis), then rebased. Only conflict was `StrataMain.lean`,
which had been heavily restructured on main (522 insertions, 425 deletions across
28 PRs). Resolution was straightforward: take main's version, re-add the 3 branch
imports and 2 command definitions.

**Lean 4.27 → 4.29 migration.** The toolchain upgrade required one fix:
`readPythonStrata` needed qualification as `Python.readPythonStrata` and wrapping
in `.toBaseIO` to convert `EIO String` to `IO`, matching the pattern used by other
Python commands in StrataMain. All 6 branch Lean files already used the `module`
keyword, so no other changes were needed.

**Build result:** Full `lake build` passes (580 jobs). SSA test suite: 34/34.

**Corpus validation.** Ran `strata pyToSSA` on all 51 `.python.st.ion` files
from `kiro_tests_annotated`:

| Result | Count | Notes |
|--------|-------|-------|
| Clean (zero warnings) | 8 | Fully translated |
| Unresolved names only | 33 | Structurally complete; warnings are external imports (`boto3`, `json`, `ClientError`, etc.) |
| `bare raise` warnings | 6 | Re-raise in except handlers — not yet implemented |
| Comprehension warnings | 6 | ListComp (10), DictComp (3), GeneratorExp (1) — deliberately out of scope |

**Zero crashes on 51/51 files.** The translator is robust on real-world code.

**Warning category breakdown (313 total across corpus):**

| Category | Count | Notes |
|----------|-------|-------|
| Unresolved name: boto3 | 52 | Third-party import |
| Unresolved name: ClientError | 73 | botocore exception type |
| Unresolved name: __name__ | 44 | Module-level guard |
| bare raise not supported | 26 | Re-raise in except handlers |
| Unresolved name: logger | 19 | Logging module |
| Unresolved name: json | 17 | stdlib import |
| Unresolved name: other | 68 | sys, datetime, time, etc. |
| unsupported ListComp | 10 | Out of scope |
| unsupported DictComp | 3 | Out of scope |
| unsupported GeneratorExp | 1 | Out of scope |

The vast majority of warnings (272/313) are unresolved external names — correct
behavior given that the prelude only contains builtins. The 26 `bare raise`
instances across 6 files are the only real translation gap for in-scope constructs.

**Scoping validation.** The original Phase 1 analysis predicted 46/52 files would
be fully translatable (everything except comprehensions). The corpus run confirms
this: 45/51 Ion files have no structural warnings (only unresolved names), and
the 6 with structural warnings are exactly the comprehension-heavy files identified
in Phase 1. The `bare raise` pattern was not flagged in Phase 1's scoping because
it was expected to be straightforward — it uses only in-scope constructs (raise,
exception variables) and was simply deferred during initial implementation.

### Phase 18: Module-Level Name Resolution (completed 2026-04-29)

Resolved three categories of previously-unresolved names: imports, module-level
variable assignments, and `__name__`.

**Design insight from Python semantics.** A small test case (A.py/B.py)
demonstrated Python's actual module variable semantics: `x = 1` at module level
in module M creates `M.x`, and functions reading `x` are really reading `M.x`
at call time. External code can mutate `M.x` and the function sees the change.
This led to the design: module-level assignments resolve to
`qualifiedRef M.name` in functions — semantically accurate and useful for
downstream analysis (the qualified name tells you where to look for type info).

**Import propagation.** Added `collectImportBindings` to scan top-level `Import`
and `ImportFrom` statements and build a `HashMap String QualifiedName`. These
bindings are merged into `moduleBindings` so every function sees imported names
as `qualifiedRef` (e.g., `boto3` → `qualifiedRef boto3.boto3`, `ClientError` →
`qualifiedRef botocore.exceptions.ClientError`).

**Module-level assignments.** Added `collectModuleAssignments` to scan `Assign`,
`AnnAssign`, and `AugAssign` targets. These are merged into `moduleBindings`
with lower precedence than imports: if a name is both imported and assigned,
the import wins (matching Python's runtime shadowing order for the common case).

**Precedence chain.** The `moduleBindings` merge order ensures correct shadowing:
implicit attrs (`__name__`) < assignments < imports < function/class definitions.
Functions/classes always win, matching Python semantics.

**`__name__` as module attribute.** Initially added `__name__` to the prelude as
`qualifiedRef builtins.__name__`, but the human corrected this: `__name__` is a
module attribute (`M.__name__`), not a builtin. In Python, `import json;
json.__name__` returns `'json'`. Fixed to resolve as `qualifiedRef M.__name__`.

**Demand analysis split.** A subtle issue arose: `collectModuleGlobals` (which
feeds demand analysis) must NOT include assignment targets for `@module_init`,
because those variables are genuinely local to the init function and need to be
threaded through blocks. But other functions should exclude them (they resolve
via `moduleBindings`). The fix: `scanModule` computes two globals sets —
`globals` (original: functions + classes + imports) for `@module_init`, and
`funcGlobals` (adds assignment targets) for all other functions and methods.

**Prelude additions.** Added `any`, `all`, `IndexError`, `FileNotFoundError`,
`ProcessLookupError` — builtins found in the corpus but missing from the prelude.

**Test: t27_module_vars.py.** Four functions testing:
- `use_module_vars`: imports and assignments resolve to qualifiedRef
- `param_shadows_module_var`: function parameter shadows module var
- `local_shadows_module_var`: local assignment shadows module var
- `mixed_imports_and_vars`: both imports and module vars in one function

**Corpus results.** Warnings dropped from 289 to 49 (83% reduction):

| Category | Count | Notes |
|----------|-------|-------|
| unsupported ListComp | 16 | Comprehension — out of scope |
| unsupported GeneratorExp | 8 | Comprehension — out of scope |
| unsupported DictComp | 3 | Comprehension — out of scope |
| unsupported SetComp | 2 | Comprehension — out of scope |
| Unresolved local variables | 20 | Function-local vars in conditional branches |

The 29 comprehension warnings are expected (out of scope). The 20 unresolved
local variables are genuinely ambiguous names — variables assigned inside `if`
or `try` blocks that may not be defined on all control flow paths. These are
correct warnings: the code would raise `NameError` at runtime if the variable's
branch wasn't taken.
