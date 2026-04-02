# Laurel Denotational Semantics

**Date:** 2026-03-20
**Files:**
- `Strata/Languages/Laurel/LaurelSemantics.lean` — shared types and helpers
- `Strata/Languages/Laurel/LaurelDenote.lean` — interpreter
- `Strata/Languages/Laurel/LaurelDenoteMono.lean` — fuel monotonicity

## Overview

This document describes the fuel-based denotational interpreter for
Laurel IR. The interpreter is a computable Lean function that serves
as an executable reference semantics for Laurel programs. It is used
for testing, debugging, and as the foundation for the concrete
evaluator.

## Motivation

For testing, debugging, and downstream tooling, we need a computable
interpreter that:

1. Can be `#eval`'d on concrete programs
2. Is deterministic by construction (it is a function, not a relation)
3. Covers all Laurel constructs comprehensively

## Design

### Fuel Parameter

The interpreter uses a `fuel : Nat` parameter decremented on every
recursive call. This ensures termination (required by Lean for
non-`partial` functions) without restricting the class of programs that
can be evaluated — any terminating program can be evaluated with
sufficient fuel.

When fuel reaches zero, the interpreter returns `none` (indistinguishable
from a stuck program). This is a limitation: the interpreter cannot
distinguish non-termination from insufficient fuel.

### Three Mutually Recursive Functions

| Function | Signature | Purpose |
|----------|-----------|---------|
| `denoteStmt` | `δ → π → fuel → h → σ → StmtExpr → Option (Outcome × LaurelStore × LaurelHeap)` | Evaluate a single statement/expression |
| `denoteBlock` | `δ → π → fuel → h → σ → List StmtExprMd → Option (Outcome × LaurelStore × LaurelHeap)` | Evaluate a block of statements |
| `denoteArgs` | `δ → π → fuel → h → σ → List StmtExprMd → Option (List LaurelValue × LaurelStore × LaurelHeap)` | Evaluate arguments left-to-right |

### Return Convention

The interpreter returns `Option (Outcome × LaurelStore × LaurelHeap)`:
- `some (outcome, σ', h')` — successful evaluation
- `none` — stuck state or fuel exhaustion

### Computable Store/Heap Helpers

The shared types in `LaurelSemantics.lean` include inductive relations
for store and heap operations (`UpdateStore`, `InitStore`, `AllocHeap`,
`HeapFieldWrite`). The denotational interpreter needs computable
versions:

| Computable | Relational | Purpose |
|------------|------------|---------|
| `updateStore σ x v` | `UpdateStore σ x.text v σ'` | Update existing variable |
| `initStore σ x v` | `InitStore σ x.text v σ'` | Initialize new variable |
| `allocHeap h typeName` | `AllocHeap h typeName addr h'` | Allocate heap object |
| `heapFieldWrite' h addr field v` | `HeapFieldWrite h addr field v h'` | Write heap field |

Each computable helper returns `Option` — `none` when the precondition
fails (e.g., `updateStore` on an undefined variable).

### Heap Allocation Bound

The computable `allocHeap` searches a bounded range (`heapSearchBound =
10000`) for a free address using `findSmallestFree`. The relational
`AllocHeap` has no such bound. This means the interpreter can fail on
programs that allocate more than 10000 objects.

## Construct Coverage

The interpreter covers the following constructs:

- **Literals:** `LiteralInt`, `LiteralBool`, `LiteralString` — return
  the value directly
- **Variables:** `Identifier` — look up in store
- **Operations:** `PrimitiveOp` — evaluate args via `denoteArgs`, apply op
- **Control flow:** `IfThenElse`, `Block`, `Exit`, `Return`, `While`
- **Assignments:** `Assign` (single target, field target), `LocalVariable`
- **Verification:** `Assert`, `Assume` — evaluate condition, discard
  state effects, require `true`
- **Calls:** `StaticCall`, `InstanceCall` — evaluate args, bind params,
  evaluate body, handle normal/return outcomes
- **OO:** `New`, `FieldSelect`, `PureFieldUpdate`, `ReferenceEquals`,
  `This`, `IsType`, `AsType`
- **Specification:** `Forall`, `Exists`, `Old`, `Fresh`, `Assigned`,
  `ProveBy`, `ContractOf` — delegated to `δ`
- **Omitted:** `Abstract`, `All`, `Hole` — return `none`

## Fuel Monotonicity

`LaurelDenoteMono.lean` proves that the interpreter is monotone in fuel:

```
denoteStmt_fuel_mono : fuel₁ ≤ fuel₂ →
  denoteStmt δ π fuel₁ h σ s = some r →
  denoteStmt δ π fuel₂ h σ s = some r
```

If the interpreter succeeds with `fuel₁`, it succeeds with any larger
fuel giving the same result. This is proved by mutual induction on fuel,
case-splitting on the statement, and applying the IH to sub-calls.

Analogous theorems hold for `denoteBlock` and `denoteArgs`.

## Limitations

1. **Fuel exhaustion is indistinguishable from stuck.** When fuel
   reaches zero, the interpreter returns `none` — the same result as
   for a stuck program (e.g., undefined variable, type error). There
   is no way to distinguish "needs more fuel" from "genuinely stuck."

2. **Heap allocation bound.** The computable `allocHeap` searches at
   most `heapSearchBound = 10000` addresses for a free slot. Programs
   that allocate more than 10000 objects will fail. This bound is
   hardcoded.

3. **No partial evaluation.** The interpreter is total (not `partial`),
   which means it cannot handle non-terminating programs at all — it
   simply runs out of fuel.

4. **Unsupported constructs.** `LiteralDecimal` returns `none` (no
   float/decimal value type). `Abstract`, `All`, `Hole` return `none`.
   Multi-target `Assign` returns `none`. `DivT` and `ModT` are not
   handled by `evalPrimOp`. Float64 operands are not supported.
   Procedures with `Abstract` or `External` bodies cannot be called
   (`getBody` returns `none`). Non-local control flow in arguments
   causes `none` (each argument must produce `.normal v`).
