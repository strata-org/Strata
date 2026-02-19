# Existing Verifier Migration Feasibility Analysis

## Related PRs

- **PR #413**: Fix cover diagnostic messages to distinguish from assertions
  - Fixes `toDiagnosticModel` to be cover-aware
  - Adds verbosity-based reporting for unknown cover results
  - Status: Draft, pending merge

## Executive Summary

This document analyzes the feasibility of migrating the existing Core partial evaluator to fulfill the CoreSMT_Verifier requirements versus building from scratch. The analysis examines the current architecture, identifies gaps, and proposes a migration strategy.

**Recommendation:** Gradual migration of the existing infrastructure is more practical than building from scratch, but requires significant architectural changes to the verification flow.

## Current Architecture Overview

### B3 Verifier (Target Architecture)

The B3 verifier (`Strata/Languages/B3/Verifier/`) implements the streaming verification architecture we want:

| Component | File | Purpose |
|-----------|------|---------|
| State | `State.lean` | Incremental SMT solver state, verification context, push/pop |
| Expression | `Expression.lean` | B3 Expression → SMT Term translation |
| Statements | `Statements.lean` | Streaming symbolic execution of statements |
| Diagnosis | `Diagnosis.lean` | Automatic failure diagnosis (conjunction splitting) |
| Program | `Program.lean` | Entry point, procedure verification |

**Key Features:**
- Interactive SMT solver (cvc5/Z3) with incremental solving
- Streaming verification: statements translated and verified immediately
- User-friendly results: `VerificationResult` (proved/refuted/counterexample/unknown)
- Automatic diagnosis with conjunction splitting
- Path condition tracking for error context
- Error accumulation (doesn't short-circuit on first error)

### Core Verifier (Current Architecture)

The Core verifier (`Strata/Languages/Core/`) uses a different approach:

| Component | File | Purpose |
|-----------|------|---------|
| CmdEval | `CmdEval.lean` | Partial evaluation of commands |
| StatementEval | `StatementEval.lean` | Statement partial evaluation, path splitting |
| ProcedureEval | `ProcedureEval.lean` | Procedure-level evaluation |
| SMTEncoder | `SMTEncoder.lean` | Core Expression → SMT Term translation |
| Verifier | `Verifier.lean` | Entry point, batch verification |

**Key Features:**
- Batch verification: partial evaluation first, then SMT solving
- Deferred proof obligations: collected during evaluation, discharged later
- Path condition tracking via `Env.pathConditions`
- File-based SMT solving (writes to temp file, invokes solver)
- VCResult with Outcome (pass/fail/unknown/implementationError)

## Gap Analysis

### Requirement 1: CoreSMT Statement Verification

| Criterion | B3 Verifier | Core Verifier | Gap |
|-----------|-------------|---------------|-----|
| assume → path condition | ✅ `addPathCondition` | ✅ `addPathCondition` | None |
| init with expr → variable binding | ✅ Direct | ✅ `update` | None |
| init without expr → fresh variable | ✅ Direct | ✅ `genFreeVar` | None |
| assert → proof obligation | ✅ Direct check | ✅ `deferObligation` | Batch vs streaming |
| check → proof obligation | ✅ Direct check | ✅ `deferObligation` | Batch vs streaming |
| cover → reachability check | ✅ Direct check | ✅ `deferObligation` | Batch vs streaming |
| block → scope management | ✅ push/pop | ✅ `PathConditions` nesting | None |
| function decl → SMT declaration | ✅ `addFunctionDecl` | ✅ Via `SMT.Context.addUF` | None |
| function def → SMT definition | ✅ Via axiom | ✅ Via `SMT.Context.addIF` | None |
| Expression → SMT Term | ✅ `expressionToSMT` | ✅ `toSMTTerm` | None |

**Assessment:** Core verifier has all the semantic pieces. The only architectural difference is batch vs streaming verification - Core collects proof obligations during evaluation and discharges them all at the end, while B3 verifies each obligation immediately. Both approaches produce correct results; streaming enables better diagnosis and incremental feedback.

### Requirement 3: User-Friendly Verification Results

| Criterion | B3 Verifier | Core Verifier | Gap |
|-----------|-------------|---------------|-----|
| Assert result types (pass/fail/unknown) | ✅ `VerificationResult` | ✅ `Outcome` | None |
| Cover result types (pass/fail/unknown) | ✅ `VerificationResult` | ✅ `Outcome` | None |
| Error classification (cover vs assert) | ✅ `isError` | ✅ `toDiagnosticModel` (PR #413) | None |
| Configurable reporting | ❌ Not implemented | ✅ VerboseMode (PR #413) | None |
| Refuted detection (assertion provably false) | ✅ Via diagnosis | ❌ Not implemented | Diagnosis feature |
| Counterexample extraction | ✅ `SMTModel` | ✅ `SMTModel` | None |

**Assessment:** Core verifier now has adequate result types for basic verification. The `refuted` outcome (distinguishing "assertion is provably false" from "couldn't prove assertion") is a diagnosis feature that can be added later.

#### Current VCResult Architecture (Core Verifier)

The Core verifier uses a two-level result structure:

1. **`Core.SMT.Result`** - Raw SMT solver result:
   - `sat (m : SMTModel)` - Satisfiable with model
   - `unsat` - Unsatisfiable
   - `unknown` - Solver couldn't determine
   - `err (msg : String)` - Solver error

2. **`Core.Outcome`** - Analysis outcome:
   - `pass` - Verification succeeded
   - `fail` - Verification failed
   - `unknown` - Couldn't determine
   - `implementationError (e : String)` - Internal error

3. **`Core.VCResult`** - Full verification condition result:
   - `obligation : ProofObligation Expression` - The proof obligation
   - `smtResult : SMT.Result` - Raw SMT result
   - `result : Outcome` - Interpreted outcome
   - `estate : EncoderState` - SMT encoder state
   - `verbose : VerboseMode` - Verbosity level

The key function `smtResultToOutcome` interprets SMT results differently for cover vs assert:
- For **assert**: `unsat` → pass, `sat` → fail
- For **cover**: `sat` → pass (reachable), `unsat` → fail (unreachable)

The `toDiagnosticModel` function (fixed in PR #413) converts VCResult to user-facing diagnostics:
- For **fail** on cover: "cover property is not satisfiable"
- For **fail** on assert: "assertion does not hold"
- For **unknown** on cover: only reported in debug mode (verbosity > normal)
- For **unknown** on assert: always reported as "assertion could not be proved"

### Requirement 4: Automatic Diagnosis

| Criterion | B3 Verifier | Core Verifier | Gap |
|-----------|-------------|---------------|-----|
| Conjunction splitting | ✅ `diagnoseFailure` | ❌ Not implemented | Need to port |
| Context-aware diagnosis | ✅ Assumes LHS for RHS | ❌ N/A | Need to port |
| Refuted detection | ✅ Checks `A'` satisfiability | ❌ N/A | Need to port |
| Extensible strategies | ✅ Generic `diagnoseFailureGeneric` | ❌ N/A | Need to port |

**Assessment:** Diagnosis is B3-only. Need to port to Core.

### Requirement 5: Verification State Tracking

| Criterion | B3 Verifier | Core Verifier | Gap |
|-----------|-------------|---------------|-----|
| Track assumptions | ✅ `pathCondition` list | ✅ `pathConditions` | Compatible |
| Include in failure report | ✅ `VerificationContext` | ⚠️ Via `ProofObligation` | Need enhancement |
| Human-readable format | ✅ `formatStatement` | ⚠️ Basic | Need enhancement |

**Assessment:** Both track state. Core needs better reporting.

### Requirement 7: Streamable Architecture

| Criterion | B3 Verifier | Core Verifier | Gap |
|-----------|-------------|---------------|-----|
| Incremental verification | ✅ Direct SMT calls | ❌ Batch only | Major gap |
| On-the-fly transformation | ❌ N/A | ⚠️ `evalAuxGo` | Partial support |
| Incremental state updates | ✅ `addPathCondition` | ⚠️ `Env` updates | Need streaming |

**Assessment:** Core has partial evaluation infrastructure but not streaming verification.

### SMT Output Readability

The Core verifier produces SMT files through several mechanisms:

1. **ANF Encoding** (`Strata/DL/SMT/Encoder.lean`): The SMT encoder uses A-normal form (ANF) with `define-fun` declarations. Each subterm gets a unique identifier (`t0`, `t1`, etc.), making the output more readable than fully inlined expressions.

2. **Selective Function Inlining** (`Strata/DL/Lambda/LExprEval.lean`): The partial evaluator inlines function bodies only when they have `inline_attr` or `inline_if_constr_attr` attributes. Functions without these attributes are preserved as uninterpreted functions in the SMT output.

3. **Variable Substitution** (Current Limitation): The partial evaluator substitutes concrete values during evaluation. For example:
   ```
   init x := 2;
   init y := x + 3;
   ```
   Results in `y → 5` in the SMT output, NOT a variable `x` with value `2`. The variable `x` is substituted away during partial evaluation.

   Variables only appear in SMT output when they are symbolic:
   - `havoc x` → generates fresh symbolic variable (e.g., `$__x0`)
   - `init x` without expression → generates fresh symbolic variable
   - Free variables in assertions that couldn't be fully evaluated

   **This is not currently configurable.** To preserve variable names in SMT output for debugging, one would need to modify the verifier to emit `define-fun` for each `init` statement instead of substituting values.

4. **Expression Duplication Problem** (Addressed in Phase 5): When a variable is used multiple times, its definition currently gets inlined at each use site. Phase 5 fixes this by emitting `define-fun` for `init` statements instead of substituting values.
   
   Future optimization: Hash-consing could additionally share user-written duplicate expressions like `F(a)` appearing in multiple assertions.

### Requirement 16: Abstract SMT Solver Interface

| Criterion | B3 Verifier | Core Verifier | Gap |
|-----------|-------------|---------------|-----|
| Type class interface | ❌ Direct `Solver` use | ❌ Direct `Solver` use | Both need work |
| Expression builders | ❌ Direct construction | ❌ Direct construction | Both need work |
| IO commands | ✅ `Solver` monad | ✅ `Solver` monad | Compatible |
| Incremental solving | ✅ push/pop | ❌ File-based | Core needs upgrade |

**Assessment:** Neither has abstract interface. B3 has incremental solving.

## Reusable Components

### From B3 Verifier (Port to Core)

1. **`B3VerificationState`** → `CoreVerificationState`
   - SMT solver state management
   - Path condition tracking
   - Push/pop scope management

2. **`VerificationResult`** → `AssertResult`/`CoverResult`
   - User-friendly result types
   - Error classification

3. **`diagnoseFailure`** → `diagnoseAssertion`
   - Conjunction splitting
   - Context-aware diagnosis
   - Refuted detection

4. **Streaming execution pattern**
   - `statementToSMT` → `coreStatementToSMT`
   - Immediate verification during traversal

### From Core Verifier (Keep/Enhance)

1. **`SMTEncoder`** - Expression translation
   - `toSMTTerm` - Core Expression → SMT Term
   - `toSMTOp` - Operator translation
   - `SMT.Context` - Type/function tracking

2. **`Env`** - Evaluation environment
   - Variable tracking
   - Path conditions
   - Deferred obligations (for compatibility)

3. **`StatementEval`** - Statement traversal
   - `evalAuxGo` - Statement iteration
   - `processIteBranches` - If-statement handling
   - Path splitting logic

4. **`VCResult`** - Result type (enhance)
   - Add `refuted` outcome
   - Add diagnosis information

## Migration Strategy

### Phase 1: Abstract SMT Interface (Requirement 16)

**Goal:** Decouple verifiers from concrete SMT implementation.

**Tasks:**
1. Define `SMTSolverInterface` type class in `Strata/DL/SMT/Interface.lean`
2. Implement instance for existing `Solver` type
3. Refactor B3 verifier to use interface
4. Refactor Core SMTEncoder to use interface

**Risk:** Low - additive change, no breaking changes.

### Phase 2: Streaming Verification State (Requirements 1, 5)

**Goal:** Add streaming verification capability to Core.

**Tasks:**
1. Create `CoreSMT.VerificationState` based on B3's `B3VerificationState`
2. Add `push`/`pop` support for block statements
3. Add `addPathCondition` for assume statements
4. Add `prove`/`reach` for check/assert/cover statements

**Risk:** Medium - new code path, existing batch path unchanged.

### Phase 3: User-Friendly Results (Requirement 3)

**Goal:** Replace raw SMT results with user-friendly types.

**Status:** Complete via PR #413.

**Completed Tasks:**
1. ✅ Cover-aware diagnostic messages in `toDiagnosticModel`
2. ✅ Verbosity-based reporting for unknown cover results
3. ✅ Proper error classification for cover vs assert
4. ✅ Counterexample extraction via `SMTModel`

**Deferred to Phase 4 (Diagnosis):**
- `refuted` outcome detection (assertion provably false vs couldn't prove)

**Risk:** N/A - complete.

### Phase 4: Automatic Diagnosis (Requirement 4)

**Goal:** Port B3 diagnosis to Core.

**Tasks:**
1. Port `diagnoseFailureGeneric` to work with Core expressions
2. Implement conjunction splitting for Core expressions
3. Add context-aware diagnosis (assume LHS when checking RHS)
4. Add refuted detection (check satisfiability of assertion)

**Risk:** Medium - new functionality, optional feature.

### Phase 5: CoreSMT Statement Handlers (Requirement 1)

**Goal:** Implement streaming handlers for each statement type.

**Tasks:**
1. `assume` → `addPathCondition` + SMT assert
2. `init` with expr → SMT `define-fun` (preserves variable sharing, avoids expression duplication)
3. `init` without expr → SMT `declare-fun` (fresh symbolic variable)
4. `assert` → proof check + `addPathCondition`
5. `check` → proof check only
6. `cover` → reachability check
7. `block` → push/pop scope

**Key Change from Current Behavior:**
Currently, `init x := e` substitutes `e` for all uses of `x` during partial evaluation. This loses variable sharing - if `x` is used twice, `e` appears twice in the SMT output, and the solver must prove they're equal.

The new approach emits `(define-fun x () T e)` and uses `x` in subsequent assertions. This:
- Preserves variable sharing (solver knows `x = x` trivially)
- Improves SMT readability for debugging
- Matches how users think about their code
8. `funcDecl` → declare-fun or define-fun

**Risk:** Medium - core functionality, needs thorough testing.

### Phase 6: isCoreSMT Predicate (Requirement 11)

**Goal:** Define and enforce the CoreSMT subset.

**Tasks:**
1. Define `isCoreSMT` predicate on Statement/Expression
2. Implement `Except` return type for non-CoreSMT constructs
3. Add theorem: `isCoreSMT s → CoreSMT_Verifier s ≠ Except.error`

**Risk:** Low - predicate definition, theorem is optional.

### Phase 7: Core_Verifier Transformations (Requirements 2, 10, 13)

**Goal:** Implement transformations to reduce to CoreSMT.

**Tasks:**
1. If-statement elimination (already in `DetToNondet`)
2. Assignment to SSA transformation
3. Define phase predicates (input/output subsets)
4. Compose transformations with predicate checking

**Risk:** Medium - reuse existing transforms, add new SSA transform.

### Phase 8: API Compatibility (Requirement 9)

**Goal:** Make new verifier compatible with existing API.

**Tasks:**
1. Implement `Core_Verifier.verify` with same signature as `Core.verify`
2. Add verifier selection option to `Options`
3. Convert results to `VCResult` for compatibility
4. Support procedure filtering

**Risk:** Low - wrapper functions, no breaking changes.

## Effort Estimates

| Phase | Effort | Dependencies | Risk | Status |
|-------|--------|--------------|------|--------|
| 1. Abstract SMT Interface | 1-2 weeks | None | Low | Not started |
| 2. Streaming State | 2-3 weeks | Phase 1 | Medium | Not started |
| 3. User-Friendly Results | - | None | - | ✅ Complete (PR #413) |
| 4. Automatic Diagnosis | 2-3 weeks | Phases 2, 3 | Medium | Not started |
| 5. Statement Handlers | 3-4 weeks | Phases 1, 2 | Medium | Not started |
| 6. isCoreSMT Predicate | 1-2 weeks | Phase 5 | Low | Not started |
| 7. Transformations | 3-4 weeks | Phase 6 | Medium | Not started |
| 8. API Compatibility | 1-2 weeks | Phases 5, 7 | Low | Not started |

**Total:** 13-19 weeks for full migration.

## Build vs. Migrate Decision

### Arguments for Migration

1. **Reuse SMTEncoder** - 600+ lines of expression translation already working
2. **Reuse StatementEval** - Path splitting, if-handling already implemented
3. **Reuse Env** - Variable tracking, path conditions already working
4. **Reuse B3 patterns** - Diagnosis, streaming patterns proven to work
5. **Incremental delivery** - Each phase delivers value independently
6. **Test compatibility** - Existing tests continue to work

### Arguments for Building from Scratch

1. **Cleaner architecture** - No legacy constraints
2. **Simpler codebase** - No dual code paths
3. **Better abstractions** - Design for streaming from start
4. **Faster development** - No refactoring overhead

### Recommendation

**Migrate gradually** because:
- SMTEncoder is complex and well-tested (600+ lines)
- B3 verifier patterns are proven and can be ported
- Incremental delivery reduces risk
- Existing tests provide regression safety
- API compatibility is easier with migration

## Test Migration Strategy

### Phase 1: Port B3 Verifier Tests

The B3 verifier tests in `StrataTest/Languages/B3/Verifier/VerifierTests.lean` should be migrated to use Core syntax:

```lean
-- B3 syntax (current)
#eval testVerification $ #strata program B3CST;
function f(x : int) : int
axiom forall x : int pattern f(x) f(x) > 0
procedure test() {
  check 5 > 0 ==> f(5) > 0
}
#end

-- Core syntax (target)
#eval testVerification $ #strata program Core;
function f(x : int) : int;
axiom forall x : int :: {f(x)} f(x) > 0;
procedure test() {
  check 5 > 0 ==> f(5) > 0;
}
#end
```

### Phase 2: Add Property-Based Tests

Use Plausible to test:
1. **Structural properties** - Statement counts preserved through transformations
2. **Semantic properties** - Verification results equivalent between old/new pipelines
3. **Idempotence** - `transform(transform(x)) = transform(x)`

## Provability Analysis: Batch vs. Streaming Verification

### The Current Approach's Strength

The current Core verifier has a significant advantage for formal reasoning: **it separates concerns cleanly**.

1. **Partial Evaluation** (`StatementEval.lean`) - Pure transformation that collects proof obligations
2. **SMT Encoding** (`SMTEncoder.lean`) - Pure translation from Core expressions to SMT terms
3. **SMT Solving** (`Verifier.lean`) - IO-based solver invocation

This separation enables proofs like `CallElimCorrect` and `DetToNondetCorrect` which reason about:
- `EvalStmt` / `EvalBlock` - Inductive relations defining statement semantics
- `EvalStatementsContract` - Contracts relating input/output states
- Structural properties (e.g., `noFuncDecl` preservation)

The key insight: **proof obligations are data structures** that can be reasoned about independently of SMT solving.

### The B3 Streaming Approach's Challenge

The B3 verifier interleaves translation and verification in `IO`:

```lean
def statementToSMT ... : B3AST.Statement SourceRange → IO SymbolicExecutionResult
  | .check m expr => do
      let convResult := expressionToSMT ctx expr  -- Pure translation
      let result ← prove state convResult.term vctx  -- IO: SMT call
      pure <| mkExecutionResult convResult.errors (some result) state
```

This makes formal reasoning harder because:
1. **IO interleaving** - Can't use pure induction on statement structure
2. **Solver state mutation** - `push`/`pop` effects are implicit
3. **No intermediate representation** - Results depend on solver responses

### Solution: Hybrid Architecture for Provability

We can achieve **both** streaming verification **and** provability by separating the concerns:

#### Layer 1: Pure SMT Command Generation (Provable)

```lean
/-- Pure function that generates SMT commands from a statement -/
inductive SMTCommand where
  | declareFun : String → List TermType → TermType → SMTCommand
  | defineFun : String → List (String × TermType) → TermType → Term → SMTCommand
  | assert : Term → SMTCommand
  | checkSatAssuming : Term → SMTCommand
  | push : SMTCommand
  | pop : SMTCommand

/-- Pure translation from CoreSMT statement to SMT commands -/
def translateStatement : Statement → List SMTCommand
  | .assume e => [.assert (translateExpr e)]
  | .init x (some e) => [.defineFun x.name [] (translateType x.ty) (translateExpr e)]
  | .init x none => [.declareFun x.name [] (translateType x.ty)]
  | .block ss => [.push] ++ ss.flatMap translateStatement ++ [.pop]
  | ...
```

This is **pure** and can be reasoned about inductively.

#### Layer 2: SMT Command Semantics (Provable)

```lean
/-- Semantics of SMT commands as state transitions -/
inductive SMTSemantics : SMTState → SMTCommand → SMTState → Prop where
  | assert_sem : SMTSemantics s (.assert t) { s with assertions := t :: s.assertions }
  | push_sem : SMTSemantics s .push { s with stack := s.assertions :: s.stack }
  | pop_sem : SMTSemantics { s with stack := h :: t } .pop { s with assertions := h, stack := t }
  | ...
```

This defines what SMT commands **mean** without involving IO.

#### Layer 3: Soundness Theorem (Provable)

```lean
/-- Main soundness theorem: if SMT says unsat, the property holds -/
theorem coreSMT_soundness :
  isCoreSMT stmt →
  translateStatement stmt = cmds →
  SMTSemantics s₀ cmds s₁ →
  SMTSolverCorrect solver →  -- Axiom: solver is correct
  solver.checkSat s₁.assertions = .unsat →
  ∀ σ, evalStatement σ stmt → satisfiesProperty σ stmt.property
```

This theorem says: if the translation produces commands, and those commands lead to unsat, then the property holds.

#### Layer 4: IO Execution (Not Proved, but Correct by Construction)

```lean
/-- Execute SMT commands against a real solver -/
def executeCommands (solver : Solver) : List SMTCommand → IO SMTResult
  | [] => pure .done
  | .assert t :: rest => do solver.assert t; executeCommands solver rest
  | .checkSatAssuming t :: rest => do
      let result ← solver.checkSatAssuming t
      if result == .unsat then executeCommands solver rest
      else pure (.failed result)
  | ...
```

This is IO but **structurally mirrors** the pure semantics.

### Evidence: This Pattern Works

The existing `DetToNondetCorrect.lean` proves exactly this pattern:

```lean
/-- Proof that the Deterministic-to-nondeterministic transformation is correct -/
theorem StmtToNondetStmtCorrect :
  WellFormedSemanticEvalBool δ →
  WellFormedSemanticEvalVal δ →
  Stmt.noFuncDecl st →
  EvalStmt P (Cmd P) (EvalCmd P) extendEval δ σ st σ' δ →
  EvalNondetStmt P (Cmd P) (EvalCmd P) δ σ (StmtToNondetStmt st) σ'
```

This proves that:
1. A **pure transformation** (`StmtToNondetStmt`) preserves semantics
2. The proof uses **induction on statement structure**
3. The proof doesn't involve IO at all

### Recommended Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│                     CoreSMT_Verifier                            │
├─────────────────────────────────────────────────────────────────┤
│  Layer 4: IO Execution (streaming, not proved)                  │
│    executeCommands : Solver → List SMTCommand → IO SMTResult    │
├─────────────────────────────────────────────────────────────────┤
│  Layer 3: Soundness Theorem (proved)                            │
│    coreSMT_soundness : isCoreSMT stmt → ... → property holds    │
├─────────────────────────────────────────────────────────────────┤
│  Layer 2: SMT Command Semantics (proved)                        │
│    SMTSemantics : SMTState → SMTCommand → SMTState → Prop       │
├─────────────────────────────────────────────────────────────────┤
│  Layer 1: Pure Translation (proved)                             │
│    translateStatement : Statement → List SMTCommand             │
└─────────────────────────────────────────────────────────────────┘
```

### Key Insight

The streaming B3 approach **can** be made provable by:

1. **Extracting the pure translation** - `translateStatement` generates `List SMTCommand`
2. **Defining command semantics** - `SMTSemantics` as an inductive relation
3. **Proving soundness** - If translation + semantics + solver = unsat, property holds
4. **Executing in IO** - The streaming execution mirrors the pure semantics

The IO execution is **correct by construction** because it structurally follows the pure semantics. We don't prove the IO code directly, but we prove that the **pure specification** it implements is sound.

### Comparison with Current Approach

| Aspect | Current (Batch) | Proposed (Streaming) |
|--------|-----------------|----------------------|
| Proof obligations | Data structure (`ProofObligation`) | Data structure (`List SMTCommand`) |
| Translation | Pure (`toSMTTerms`) | Pure (`translateStatement`) |
| Semantics | `EvalStmt` relation | `SMTSemantics` relation |
| Soundness | Provable | Provable |
| IO execution | Batch (file-based) | Streaming (incremental) |
| Diagnosis | Not supported | Supported (in IO layer) |

### Conclusion on Provability

**Yes, the streaming approach can maintain provability** if we:

1. Keep the translation pure (`Statement → List SMTCommand`)
2. Define SMT command semantics as an inductive relation
3. Prove soundness at the pure level
4. Execute in IO following the pure structure

The key is that **diagnosis and streaming are IO concerns** that don't affect the soundness proof. The soundness proof only needs to show that the pure translation is correct.

## Composable CoreSMT Solver Architecture

### Overview

The CoreSMT verifier uses a composable solver architecture where solvers implement a common interface and can be wrapped to add functionality. This enables:

- **Streaming verification** - statements flow through immediately
- **Batch mode** - collecting solver gathers statements for later processing
- **Simplification** - wrapper solver tracks bindings and discharges trivial assertions
- **Same validity argument** - whether streaming or batch, the same interface ensures correctness

### CoreSMTSolver Interface

The interface mirrors how SMT solvers actually work - with separate `push`/`pop` commands and atomic statement processing:

```lean
/-- Abstract interface for CoreSMT solvers -/
class CoreSMTSolver (S : Type) where
  /-- Push a new scope onto the solver stack -/
  push : S → IO S
  /-- Pop the top scope from the solver stack -/
  pop : S → IO S
  /-- Process a single atomic CoreSMT statement (not a block) -/
  processAtomicStmt : S → (stmt : Core.Statement) → Core.isCoreSMT stmt → ¬stmt.isBlock → IO (S × List VerificationResult)
```

The interface has three methods:
- `push` / `pop` - scope management, matching SMT's incremental solving model
- `processAtomicStmt` - handles non-block statements (assume, init, assert, check, cover, funcDecl)
- The `isCoreSMT` proof ensures the statement is in the CoreSMT subset
- The `¬stmt.isBlock` proof ensures blocks are handled separately

### Block Statement Handling

Blocks are handled by a generic function that works with any `CoreSMTSolver`:

```lean
/-- Process any CoreSMT statement, handling blocks by push/pop + recursion -/
def processStmt [CoreSMTSolver S] (s : S) (stmt : Core.Statement) (h : Core.isCoreSMT stmt) 
    : IO (S × List VerificationResult) :=
  match stmt with
  | .block stmts => do
      let s' ← CoreSMTSolver.push s
      let (s'', results) ← processStmts s' stmts  -- recurse on inner statements
      let s''' ← CoreSMTSolver.pop s''
      pure (s''', results)
  | _ => 
      -- For non-block statements, we have ¬stmt.isBlock by case analysis
      CoreSMTSolver.processAtomicStmt s stmt h (by cases stmt <;> simp [Core.Statement.isBlock])
```

This design:
- **Matches SMT semantics** - push/pop are explicit operations, not hidden inside block handling
- **Avoids code duplication** - block handling is implemented once, not in every solver
- **Enables composition** - wrapper solvers only need to implement `push`, `pop`, `processAtomicStmt`
- **Preserves tree structure** - the recursive `processStmt` maintains the block nestingThis keeps the tree structure while enabling streaming - blocks are handled at the interface level, not in each solver implementation.

### Solver Layers

#### Layer 1: RawSMTSolver

The base solver that translates CoreSMT directly to SMT:

```lean
structure RawSMTSolver where
  solver : SMT.Solver
  encoder : SMT.EncoderState

instance : CoreSMTSolver RawSMTSolver where
  push s := do s.solver.push; pure s
  pop s := do s.solver.pop; pure s
  processAtomicStmt s stmt _hCoreSMT _hNotBlock := do
    match stmt with
    | .assume e => 
        let term ← translateExpr s.encoder e
        s.solver.assert term
        pure (s, [])
    | .init x (some e) =>
        let term ← translateExpr s.encoder e
        s.solver.defineFun x.name [] (translateType x.ty) term
        pure (s, [])
    | .init x none =>
        s.solver.declareFun x.name [] (translateType x.ty)
        pure (s, [])
    | .assert e =>
        let term ← translateExpr s.encoder e
        let result ← s.solver.checkSatAssuming (SMT.not term)
        s.solver.assert term  -- Add to solver state after checking
        pure (s, [interpretResult result e])
    | ...
```

#### Layer 2: SimplifyingSolver

A wrapper that tracks bindings and discharges trivial assertions:

```lean
structure SimplifyingSolver (Inner : Type) [CoreSMTSolver Inner] where
  inner : Inner
  bindings : HashMap Ident Expression  -- Variable → simplified expression
  assumptions : List Expression         -- Active assumptions
  bindingsStack : List (HashMap Ident Expression)  -- For push/pop

instance [CoreSMTSolver Inner] : CoreSMTSolver (SimplifyingSolver Inner) where
  push s := do
    let inner' ← CoreSMTSolver.push s.inner
    pure { s with inner := inner', bindingsStack := s.bindings :: s.bindingsStack }
  
  pop s := do
    let inner' ← CoreSMTSolver.pop s.inner
    match s.bindingsStack with
    | [] => pure { s with inner := inner' }  -- shouldn't happen if balanced
    | b :: bs => pure { s with inner := inner', bindings := b, bindingsStack := bs }
  
  processAtomicStmt s stmt hCoreSMT hNotBlock := do
    match stmt with
    | .init x (some e) =>
        -- Track binding for potential simplification
        let simplified := simplify s.bindings s.assumptions e
        let s' := { s with bindings := s.bindings.insert x simplified }
        -- Still emit to inner solver (for SMT file generation)
        let (inner', results) ← CoreSMTSolver.processAtomicStmt s'.inner stmt hCoreSMT hNotBlock
        pure ({ s' with inner := inner' }, results)
    | .assert e =>
        -- Try to simplify the assertion
        let simplified := simplify s.bindings s.assumptions e
        if simplified == .true then
          -- Trivially true - skip SMT call
          pure (s, [.proved e])
        else if simplified == .false then
          -- Trivially false - skip SMT call
          pure (s, [.refuted e])
        else
          -- Delegate to inner solver
          let (inner', results) ← CoreSMTSolver.processAtomicStmt s.inner stmt hCoreSMT hNotBlock
          pure ({ s with inner := inner' }, results)
    | _ =>
        -- Delegate other statements
        let (inner', results) ← CoreSMTSolver.processAtomicStmt s.inner stmt hCoreSMT hNotBlock
        pure ({ s with inner := inner' }, results)
```

Key points:
- The simplifier owns its state completely (bindings, assumptions, any caches it needs)
- `push`/`pop` save and restore the bindings state (matching SMT scope semantics)
- It wraps any `CoreSMTSolver`, enabling composition
- Trivial assertions are discharged locally without SMT calls
- Non-trivial assertions flow through to the inner solver

#### Layer 3: CollectingSolver (for Batch Mode)

A solver that collects SMT commands instead of executing them:

```lean
structure CollectingSolver where
  commands : List SMTCommand  -- push, pop, assert, define-fun, etc.

instance : CoreSMTSolver CollectingSolver where
  push s := pure { s with commands := .push :: s.commands }
  pop s := pure { s with commands := .pop :: s.commands }
  processAtomicStmt s stmt _hCoreSMT _hNotBlock := do
    let cmds := translateToSMTCommands stmt
    pure ({ s with commands := cmds.reverse ++ s.commands }, [])

/-- Execute collected commands against a real solver -/
def executeCollected (collected : CollectingSolver) (solver : SMT.Solver) : IO (List VerificationResult) := do
  let cmds := collected.commands.reverse
  cmds.foldlM (fun results cmd => do
    match cmd with
    | .push => solver.push; pure results
    | .pop => solver.pop; pure results
    | .assert t => solver.assert t; pure results
    | .checkSatAssuming t => 
        let r ← solver.checkSatAssuming t
        pure (interpretResult r :: results)
    | ...) []
```

This enables batch mode with the same interface - collect commands, then execute all at once.

### Composition Examples

```lean
-- Streaming with simplification (using the generic processStmt that handles blocks)
def streamingWithSimplification (program : Core.Program) : IO (List VerificationResult) := do
  let rawSolver ← RawSMTSolver.create
  let simplifyingSolver := SimplifyingSolver.wrap rawSolver
  processStmts simplifyingSolver program.stmts

-- Batch mode (collect then execute)
def batchMode (program : Core.Program) : IO (List VerificationResult) := do
  let collector := CollectingSolver.empty
  let (collector', _) ← processStmts collector program.stmts
  let solver ← SMT.Solver.create
  executeCollected collector' solver

-- Batch with simplification
def batchWithSimplification (program : Core.Program) : IO (List VerificationResult) := do
  let collector := CollectingSolver.empty
  let simplifyingCollector := SimplifyingSolver.wrap collector
  let (simplifyingCollector', _) ← processStmts simplifyingCollector program.stmts
  let solver ← SMT.Solver.create
  executeCollected simplifyingCollector'.inner solver
```

### Benefits of This Architecture

1. **Matches SMT semantics** - push/pop are explicit interface methods, not hidden
2. **Block handling is generic** - implemented once via `processStmt`, not in every solver
3. **Simplifier manages its own scope** - `bindingsStack` tracks bindings across push/pop
4. **Composable** - wrap any solver with simplification, diagnosis, logging, etc.
5. **Streaming preserved** - statements flow through immediately in streaming mode
6. **Batch mode supported** - `CollectingSolver` collects commands for later execution

### Relationship to Provability

The composable architecture supports the provability approach from the "Provability Analysis" section:

- **Layer 1 (Pure Translation)** corresponds to `CollectingSolver` - it produces `List SMTCommand`
- **Layer 2 (SMT Semantics)** can be defined on the collected commands
- **Layer 3 (Soundness)** proves that if the pure translation is correct, verification is sound
- **Layer 4 (IO Execution)** corresponds to `RawSMTSolver` - it executes against a real solver

The key insight: `SimplifyingSolver` is a **pure optimization** that doesn't affect soundness. If it discharges an assertion as trivially true, that's correct. If it passes through to the inner solver, the inner solver handles it. Either way, the result is sound.

## Conclusion

Gradual migration is recommended. The existing infrastructure provides significant value:
- SMTEncoder handles complex expression translation
- StatementEval handles path splitting
- B3 verifier provides proven streaming patterns

The migration can be done in 8 phases over 14-21 weeks, with each phase delivering independent value and maintaining backward compatibility.

**Regarding provability:** The streaming approach can be made equally provable as the batch approach by separating pure translation from IO execution. The soundness theorem operates on pure data structures (`List SMTCommand`), while streaming execution is correct by construction.
