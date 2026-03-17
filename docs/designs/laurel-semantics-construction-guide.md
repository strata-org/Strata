# How the Laurel Semantics and Proofs Were Constructed

**Date:** 2026-03-16

## Overview

This document describes the step-by-step process by which the Laurel
formal semantics, denotational interpreter, equivalence proofs, and
transformation correctness proofs were developed. The work spans 25
commits on the `main` branch, organized into distinct phases.

## Phase 1: Direct Operational Semantics

**Commits:**
- `9d8b242c` feat(laurel): Add direct operational semantics for Laurel IR
- `0af3af2a` fix(laurel): Address review feedback

**What was built:**

The first step was defining a standalone big-step operational semantics
for Laurel's `StmtExpr` AST in `LaurelSemantics.lean`. This required
several design decisions:

1. **Value domain.** A new `LaurelValue` type was created (int, bool,
   string, void, ref) rather than reusing Core expressions. Laurel has
   heap references and runtime type tags that Core encodes differently.

2. **Store and heap.** The store maps `String` (not `Identifier`) to
   `Option LaurelValue`. Using `String` ensures `BEq` and `DecidableEq`
   agree, which turned out to be critical for later bridging proofs. The
   heap maps `Nat` to `(String, String → Option LaurelValue)` pairs.

3. **Outcome type.** Non-local control flow (exit, return) was modeled
   as an `Outcome` type rather than using Core's goto mechanism. This
   keeps the semantics independent of Core.

4. **Relational store/heap operations.** `UpdateStore`, `InitStore`,
   `AllocHeap`, and `HeapFieldWrite` were defined as inductive relations
   with explicit frame conditions (all other entries unchanged). This
   makes determinism proofs straightforward.

5. **Deterministic allocation.** `AllocHeap` requires the address to be
   the smallest free address. This was a deliberate choice to make
   allocation deterministic, which simplifies all downstream proofs.

6. **Mutual induction.** `EvalLaurelStmt`, `EvalLaurelBlock`, and
   (initially) `EvalArgs` were defined as mutually inductive relations.

The initial version covered ~30 `StmtExpr` constructors including
literals, variables, primitive operations, control flow, assignments,
procedure calls, OO features, and specification constructs.

## Phase 2: Determinism Proofs

**Commits:**
- `4babd7e5` feat(laurel): Add auxiliary determinism lemmas for heap ops and EvalArgs
- `25022064` fix(laurel): Address review feedback
- `85c62333` feat(laurel): Prove EvalLaurelStmt and EvalLaurelBlock deterministic
- `c9909483` fix(laurel): Address review feedback

**What was built:**

Determinism was proved bottom-up in `LaurelSemanticsProps.lean`:

1. **Store operations first.** `UpdateStore_deterministic` and
   `InitStore_deterministic` — given the same inputs, the output store
   is unique. Proved by `funext` + case analysis on whether each
   variable is the target.

2. **Heap operations.** `AllocHeap_deterministic` — the smallest-free-
   address invariant makes the allocated address unique, and the frame
   condition makes the resulting heap unique. `HeapFieldWrite_deterministic`
   — similar argument.

3. **EvalArgs.** `EvalArgs_deterministic` — by induction on the first
   derivation, using determinism of `δ` (the expression evaluator).

4. **Main relations.** `EvalLaurelStmt_deterministic` and
   `EvalLaurelBlock_deterministic` — by mutual induction on the first
   derivation. Each case destructs the second derivation and uses
   determinism of sub-components to show the results agree.

The determinism proof required `maxHeartbeats 800000` due to the large
number of constructors.

## Phase 3: Store-Threading Argument Evaluation

**Commits:**
- `53d79ef9` feat(laurel): Add store-threading argument evaluation (EvalStmtArgs)
- `669bf72a` fix(laurel): Address review feedback
- `bb20b72f` feat(laurel): Add tests for extended semantics determinism

**What was built:**

The original `EvalArgs` used the pure evaluator `δ` for each argument.
This meant effectful arguments (assignments, calls in argument position)
had no derivation. To support the `liftImperativeExpressions` correctness
proof, a new `EvalStmtArgs` relation was added:

```
EvalStmtArgs δ π h σ args h' σ' vals
```

This evaluates arguments left-to-right using `EvalLaurelStmt` (not `δ`),
threading heap and store through each argument. Each argument must
produce `.normal v`; non-local control flow in arguments gets stuck.

`EvalStmtArgs` was added to the mutual block with `EvalLaurelStmt` and
`EvalLaurelBlock`. The `PrimitiveOp`, `StaticCall`, and `InstanceCall`
rules were updated to use `EvalStmtArgs` instead of `EvalArgs`.

Determinism was extended to cover `EvalStmtArgs_deterministic`.

The old `EvalArgs` was retained for reasoning about pure sub-expressions.

## Phase 4: Lift Correctness — Pure Expressions

**Commits:**
- `766f47ed` feat(laurel): Add lift correctness proof for pure expressions
- `0becd73e` fix(laurel): Address review feedback

**What was built:**

The first phase of the lift correctness proof (Phase 1 in the design
document) established that `transformExpr` is the identity on pure
expressions. Helper lemmas were added to `LaurelSemanticsProps.lean`:

- `EvalLaurelBlock_append` — evaluating `ss₁ ++ ss₂` can be split
- `EvalLaurelBlock_append_singleton` — special case for appending one stmt

## Phase 5: Lift Correctness — Single and Multi-Assignment

**Commits:**
- `9f0d251d` feat(laurel): Prove lift correctness for single assignment in PrimitiveOp
- `9a1b904b` feat(laurel): Add general PrimitiveOp multi-assignment lift correctness

**What was built:**

Phase 2 proved `lift_single_assign_correct`: for `op(x, x := e)`, the
lifted block `[var $snap := x; x := e; op($snap, x)]` evaluates to the
same result. The proof explicitly constructs intermediate stores.

Phase 3 generalized to arbitrary argument lists via the `ArgSpec`
framework. The key insight was modeling store effects as a right-to-left
threading function (`threadEffectsRL`) that mirrors the pass's
right-to-left traversal. The `SpecsOK` inductive captures well-formedness
conditions, and `allPrepends_eval` proves the prepended statements
evaluate correctly by structural recursion on `SpecsOK`.

## Phase 6: Lift Correctness — Statement Level

**Commits:**
- `42a617f8` feat(laurel): Add Phase 4 statement-level transformStmt correctness
- `d6c0d09b` fix(laurel): Address review feedback

**What was built:**

Phase 4 lifted expression-level results to statement-level correctness.
The generic `transformStmt_prepend_correct` theorem shows that
`prepends ++ [s']` evaluates correctly when prepends evaluate normally
and `s'` evaluates in the resulting store.

The `TransformOK` inductive was introduced to compose per-statement
results into block-level correctness. It handles all outcome types
(normal, exit, return) and the short-circuit behavior of non-local
control flow.

## Phase 7: Denotational Interpreter

**Commits:**
- `33f78b06` feat(laurel): Add fuel-based denotational interpreter for Laurel

**What was built:**

`LaurelDenote.lean` defines three mutually recursive functions
(`denoteStmt`, `denoteBlock`, `denoteArgs`) that mirror the relational
semantics. Key design decisions:

1. **Fuel parameter.** A `Nat` decremented on every recursive call
   ensures termination without restricting the class of programs.

2. **Computable helpers.** `updateStore`, `initStore`, `allocHeap`, and
   `heapFieldWrite'` are computable versions of the relational operations,
   returning `Option` on precondition failure.

3. **Heap search bound.** `allocHeap` searches up to 10000 addresses.
   This is a practical limitation that the completeness proof must
   account for.

## Phase 8: Bridging Lemmas

**Commits:**
- `287ea4af` feat(laurel): Add bridging lemmas for store/heap helpers

**What was built:**

`LaurelDenoteBridge.lean` proves sound/complete pairs for each
computable helper:

- `updateStore_sound` / `updateStore_complete`
- `initStore_sound` / `initStore_complete`
- `allocHeap_sound` / `allocHeap_complete`
- `heapFieldWrite_sound` / `heapFieldWrite_complete`

Plus `findSmallestFree_spec` and related lemmas connecting the
computable address search to the relational smallest-free-address
property.

These bridging lemmas are the critical glue between the two semantic
styles. Without them, the soundness and completeness proofs cannot
translate between `Option`-based pattern matching and inductive
derivation construction.

## Phase 9: Fuel Monotonicity

**Part of the denotational interpreter work.**

`LaurelDenoteMono.lean` proves `denoteStmt_fuel_mono`: if the
interpreter succeeds with fuel `f₁`, it succeeds with any `f₂ ≥ f₁`
giving the same result. Proved by mutual induction on fuel, case-
splitting on the statement.

This is essential for completeness: when composing fuel requirements
from sub-derivations, we take the sum and use monotonicity to lift each
sub-result to the common fuel level.

## Phase 10: Soundness Proof

**Commits:**
- `618507dc` fix(laurel): Address review feedback for Soundness
- `03b02e94` fix(laurel): Remove last two sorry's from denotational soundness proof

**What was built:**

`LaurelDenoteSound.lean` proves `denoteStmt_sound`: if `denoteStmt`
returns a result, then `EvalLaurelStmt` has a matching derivation.

The proof proceeds by mutual induction on fuel, then case-splitting on
the ~35 `StmtExpr` constructors. For each constructor:
1. Unfold `denoteStmt`
2. Pattern-match on intermediate `Option` results
3. Apply IH to sub-calls
4. Use bridging lemmas to convert computable results to relational facts
5. Construct the relational derivation

Three complex cases (While, StaticCall, InstanceCall) were extracted
into private helper lemmas to stay within heartbeat limits.

The last two `sorry`'s (in the `Assign` exhaustive pattern matching for
non-standard LHS patterns like `Assign [⟨.LiteralDecimal _, _⟩] _`)
were removed in the final commit by adding explicit `simp [denoteStmt]`
for each impossible pattern.

## Phase 11: Completeness Proof

**Commits:**
- `94fd6131` feat(laurel): Prove completeness of denotational interpreter

**What was built:**

`LaurelDenoteComplete.lean` proves `denoteStmt_complete`: if
`EvalLaurelStmt` has a derivation, then `denoteStmt` succeeds with
enough fuel.

The proof pattern-matches on the relational derivation constructor:
1. Recursively obtain fuel values for sub-derivations
2. Combine fuels (sum + 1)
3. Use `denoteStmt_fuel_mono` to lift each sub-result to the common fuel
4. Unfold `denoteStmt` and `simp` to show the result matches

The `HeapInBound` predicate was introduced to handle the gap between
the unbounded relational `AllocHeap` and the bounded computable
`allocHeap`.

## Phase 12: Equivalence Corollaries

**Commits:**
- `3c8faca2` feat(laurel): Add equivalence corollaries for denotational semantics
- `084fa113` fix(laurel): Address review feedback

**What was built:**

`LaurelDenoteEquiv.lean` combines soundness and completeness into:

- `denoteStmt_iff` — bidirectional equivalence (under `HeapInBound`)
- `denoteStmt_deterministic` — interpreter determinism (no `HeapInBound`
  needed, uses only soundness + relational determinism)

## Upstream Adaptation

**Commits:**
- `a9e31650` fix(laurel): Adapt semantics to upstream Identifier struct and API changes

**What happened:**

The upstream Strata repository changed `Identifier` from a `String`
abbreviation to a struct with `text` and `uniqueId` fields. This
required updating the semantics to use `name.text` for store lookups
and adding a `DecidableEq` instance for the new `Identifier` type.

## Summary of File Dependencies

```
Laurel.lean (AST)
  │
  ├── LaurelSemantics.lean (operational semantics)
  │     │
  │     ├── LaurelSemanticsProps.lean (determinism, monotonicity, append)
  │     │
  │     └── LiftImperativeExpressionsCorrectness.lean (lift proof)
  │
  ├── LaurelDenote.lean (denotational interpreter)
  │     │
  │     ├── LaurelDenoteMono.lean (fuel monotonicity)
  │     │
  │     └── LaurelDenoteBridge.lean (computable ↔ relational)
  │           │
  │           ├── LaurelDenoteSound.lean (denote → eval)
  │           │
  │           └── LaurelDenoteComplete.lean (eval → denote)
  │                 │
  │                 └── LaurelDenoteEquiv.lean (iff + determinism)
  │
  └── LiftImperativeExpressions.lean (transformation)
```

## Lessons Learned

1. **String keys matter.** Using `String` instead of `Identifier` for
   store keys was essential. The `BEq`/`DecidableEq` agreement is needed
   by bridging proofs that convert between `if x == y` (computable) and
   `x = y` (propositional).

2. **Deterministic allocation simplifies everything.** The smallest-free-
   address invariant makes `AllocHeap` deterministic, which cascades
   through all proofs. A non-deterministic allocator would require
   existential witnesses everywhere.

3. **Bridging lemmas are the bottleneck.** The soundness and completeness
   proofs are structurally straightforward (case-split, apply IH). The
   hard part is connecting computable helpers to relational operations.

4. **Fuel monotonicity is non-negotiable.** Without it, the completeness
   proof cannot compose fuel requirements from sub-derivations.

5. **Extract complex cases.** The While, StaticCall, and InstanceCall
   cases in the soundness proof each required their own helper lemma to
   stay within heartbeat limits. Trying to inline them caused timeouts.

6. **Bottom-up proof development works.** The phased approach (store ops
   → determinism → single assignment → multi-assignment → statement level
   → denotational → bridging → soundness → completeness → equivalence)
   allowed each step to be independently verified and reviewed.

7. **Review feedback improves proofs.** Many commits are "Address review
   feedback" — code review caught naming issues, missing edge cases, and
   opportunities to simplify proofs.
