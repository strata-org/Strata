# Laurel Denotational Semantics

**Date:** 2026-03-16
**Files:**
- `Strata/Languages/Laurel/LaurelDenote.lean` — interpreter
- `Strata/Languages/Laurel/LaurelDenoteMono.lean` — fuel monotonicity
- `Strata/Languages/Laurel/LaurelDenoteBridge.lean` — bridging lemmas

## Overview

This document describes the fuel-based denotational interpreter for
Laurel IR. The interpreter is a computable Lean function that mirrors
the relational operational semantics in `LaurelSemantics.lean`. It
serves as an executable reference implementation and as the basis for
the soundness/completeness proof connecting the two semantic styles.

## Motivation

The relational operational semantics (`EvalLaurelStmt` and friends) is
an inductive relation — it specifies *what* evaluations are valid but
cannot be executed directly. For testing, debugging, and downstream
tooling, we need a computable interpreter that:

1. Can be `#eval`'d on concrete programs
2. Agrees with the relational semantics (soundness + completeness)
3. Is deterministic by construction (it is a function, not a relation)

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

Note the tuple order: `(Outcome, Store, Heap)`. The relational semantics
uses the order `(Heap, Store, Outcome)` in its judgment form. The bridging
proofs account for this difference.

### Computable Store/Heap Helpers

The relational semantics uses inductive relations for store and heap
operations (`UpdateStore`, `InitStore`, `AllocHeap`, `HeapFieldWrite`).
The denotational interpreter needs computable versions:

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
programs that allocate more than 10000 objects, even though the
relational semantics would succeed. The completeness proof accounts for
this via the `HeapInBound` predicate.

## Construct Coverage

The interpreter covers the same constructs as the relational semantics:

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

Fuel monotonicity is essential for the completeness proof: when composing
fuel requirements from sub-derivations, we need to show that a single
fuel value (the maximum of all sub-fuels) suffices for the entire
computation.

## Bridging Lemmas

`LaurelDenoteBridge.lean` connects the computable helpers to their
relational counterparts:

### Store Operations

- `updateStore_sound`: `updateStore σ x v = some σ' → UpdateStore σ x.text v σ'`
- `updateStore_complete`: `UpdateStore σ x.text v σ' → updateStore σ x v = some σ'`
- `initStore_sound` / `initStore_complete`: analogous for `InitStore`

### Heap Operations

- `allocHeap_sound`: `allocHeap h typeName = some (addr, h') → AllocHeap h typeName addr h'`
- `allocHeap_complete`: `AllocHeap h typeName addr h' → allocHeap h typeName = some (addr, h')`
  (requires `addr ≤ heapSearchBound`)
- `heapFieldWrite_sound` / `heapFieldWrite_complete`: analogous for `HeapFieldWrite`

### findSmallestFree Specification

- `findSmallestFree_spec`: if `addr` is the smallest free address and
  `addr ≤ heapSearchBound`, then `findSmallestFree h 0 = addr`
- `findSmallestFree_finds_free`: the returned address is actually free
- `findSmallestFree_below_occupied`: all addresses below the result are occupied

These bridging lemmas are the glue that makes the soundness and
completeness proofs work — they translate between the computable world
(where we pattern-match on `Option`) and the relational world (where we
construct inductive derivations).

## Limitations and Assumptions

### Inherited from the Operational Semantics

The denotational interpreter mirrors the relational semantics exactly,
so it inherits all of its limitations:

- `LiteralDecimal` returns `none` (no float/decimal value type)
- `Abstract`, `All`, `Hole` return `none`
- Multi-target `Assign` returns `none`
- `DivT` and `ModT` are not handled by `evalPrimOp`
- Float64 operands are not supported
- Procedures with `Abstract` or `External` bodies cannot be called
  (`getBody` returns `none`)
- Non-local control flow in arguments causes `none` (each argument
  must produce `.normal v`)

See the operational semantics document for the full list.

### Specific to the Denotational Interpreter

1. **Fuel exhaustion is indistinguishable from stuck.** When fuel
   reaches zero, the interpreter returns `none` — the same result as
   for a stuck program (e.g., undefined variable, type error). There
   is no way to distinguish "needs more fuel" from "genuinely stuck."

2. **Heap allocation bound.** The computable `allocHeap` searches at
   most `heapSearchBound = 10000` addresses for a free slot. Programs
   that allocate more than 10000 objects will fail even though the
   relational semantics would succeed. This bound is hardcoded and
   affects the completeness proof (which requires the `HeapInBound`
   predicate).

3. **BEq/DecidableEq agreement assumption.** The bridging lemma
   `heapFieldWrite_complete` relies on `String` having a `BEq` instance
   that agrees with `DecidableEq` (via `beq_iff_eq`). This is true for
   `String` but would break if `Identifier` ever received a non-standard
   `BEq` instance. The code comments flag this explicitly.

4. **No partial evaluation.** The interpreter is total (not `partial`),
   which means it cannot handle non-terminating programs at all — it
   simply runs out of fuel. The relational semantics also cannot handle
   non-termination (it is inductive, not coinductive), so this is
   consistent, but it means neither semantics can reason about diverging
   programs.

5. **Tuple order differs from relational semantics.** The interpreter
   returns `(Outcome, Store, Heap)` while the relational judgment uses
   the order `(Heap, Store, Outcome)`. This is a cosmetic difference
   but requires care in the bridging proofs.
