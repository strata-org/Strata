# Proof of LiftImperativeExpressions Correctness

**Date:** 2026-03-16
**File:** `Strata/Languages/Laurel/LiftImperativeExpressionsCorrectness.lean`

## Overview

This document explains the correctness proof for the
`liftImperativeExpressions` pass, which transforms Laurel programs so
that assignments and imperative calls no longer appear in expression
position. The proof follows a phased bottom-up approach (Option C from
the design document), building from simple cases to the general theorem.

## What the Pass Does

The pass extracts effectful sub-expressions (assignments, imperative
calls) from expression contexts into preceding statements, introducing
snapshot variables to preserve intermediate values.

**Before:**
```
var y: int := x + (x := 1;) + x;
```

**After:**
```
var $x_0: int := x;     // snapshot x = 0
x := 1;                 // lifted assignment
var y: int := $x_0 + x + x;
```

Both programs produce `y = 2` and `x = 1`.

## Phase 2: Single Assignment in PrimitiveOp

### `lift_single_assign_correct`

```lean
theorem lift_single_assign_correct
    (δ : LaurelEval) (π : ProcEnv) (h : LaurelHeap) (σ : LaurelStore)
    (op : Operation) (x snap : Identifier)
    (e : StmtExprMd) (ty : HighTypeMd)
    (md tmd : Imperative.MetaData Core.Expression)
    (v_old v_new result : LaurelValue)
    (hx_def : σ x.text = some v_old)
    (hfresh : σ snap.text = none)
    (hne : snap.text ≠ x.text)
    (he_ext : ∀ σ', (∀ y, y ≠ snap.text → σ' y = σ y) →
      EvalLaurelStmt δ π h σ' e h σ' (.normal v_new))
    (hop : evalPrimOp op [v_old, v_new] = some result) :
    ∃ σ_block, EvalLaurelBlock δ π h σ
      [ ⟨.LocalVariable snap ty (some ⟨.Identifier x, md⟩), md⟩,
        ⟨.Assign [⟨.Identifier x, tmd⟩] e, md⟩,
        ⟨.PrimitiveOp op [⟨.Identifier snap, md⟩, ⟨.Identifier x, md⟩], md⟩ ]
      h σ_block (.normal result)
```

**In English:** Consider a primitive operation `op(x, x := e)` where `x`
currently holds `v_old`, the assignment `x := e` produces `v_new`, and
`op(v_old, v_new) = result`. The lifted version is:

1. `var $snap := x;` — snapshot `x`'s current value (`v_old`)
2. `x := e;` — perform the assignment (now `x = v_new`)
3. `op($snap, x)` — compute using snapshot and updated value

The theorem says this three-statement block evaluates to `.normal result`
in some final store `σ_block`.

**Preconditions:**
- `hx_def`: `x` is defined in the store with value `v_old`
- `hfresh`: the snapshot name `snap` is not in the store
- `hne`: `snap` and `x` are different names
- `he_ext`: the RHS `e` evaluates to `v_new` in any store that agrees
  with `σ` on all variables except `snap` (i.e., `e` doesn't read `snap`)
- `hop`: the primitive operation produces `result`

**Proof sketch:** The proof constructs the intermediate stores explicitly:
- `σ_snap` = `σ` extended with `snap ↦ v_old`
- `σ_final` = `σ_snap` with `x` updated to `v_new`

Then it builds the block derivation step by step using `InitStore`,
`UpdateStore`, and the evaluation rules.

### `lift_single_assign_from_eval`

```lean
theorem lift_single_assign_from_eval
    (heval : EvalLaurelStmt δ π h σ
      ⟨.PrimitiveOp op [⟨.Identifier x, md⟩,
                         ⟨.Assign [⟨.Identifier x, tmd⟩] e, md⟩], md⟩
      h' σ' (.normal result))
    (hfresh : σ snap.text = none)
    (hne : snap.text ≠ x.text)
    (he_pure : EvalLaurelStmt δ π h σ e h σ (.normal v_new))
    (he_ext : ...) :
    ∃ σ_block, EvalLaurelBlock δ π h σ
      [ ⟨.LocalVariable snap ty (some ⟨.Identifier x, md⟩), md⟩,
        ⟨.Assign [⟨.Identifier x, tmd⟩] e, md⟩,
        ⟨.PrimitiveOp op [⟨.Identifier snap, md⟩, ⟨.Identifier x, md⟩], md⟩ ]
      h' σ_block (.normal result)
```

**In English:** If the *original* expression `op(x, x := e)` evaluates
to `result`, then the lifted block also evaluates to `result`. This
connects the "before" semantics to the "after" semantics.

The proof destructs the original evaluation derivation to extract the
intermediate values, then applies `lift_single_assign_correct`.

## Phase 3: General PrimitiveOp with Multiple Assignments

Phase 3 generalizes to arbitrary argument lists with multiple assignments.

### ArgSpec — Argument Specification

Each argument is classified as either pure or an assignment:

```lean
inductive ArgSpec where
  | pure (ref : StmtExprMd) (val : LaurelValue)
  | assign (x snap : Identifier) (e : StmtExprMd)
           (ty : HighTypeMd) (val : LaurelValue)
```

Helper functions extract the components:
- `ArgSpec.value` — the value the argument evaluates to
- `ArgSpec.cleanedArg md` — the expression after lifting (original for
  pure, `Identifier x` for assignments)
- `ArgSpec.prepends md tmd` — the prepended statements (empty for pure,
  `[LocalVariable snap ..., Assign [x] e]` for assignments)
- `allPrepends md tmd specs` — concatenation of all prepends (right-to-left
  order, matching the pass's traversal)
- `cleanedArgs md specs` — the cleaned argument list
- `argValues specs` — the list of values

### Store Effect Model

```lean
def applyArgEffect (σ : LaurelStore) : ArgSpec → LaurelStore
  | .pure _ _ => σ
  | .assign x snap _ _ val =>
    fun y => if y == x.text then some val
             else if y == snap.text then σ x.text
             else σ y
```

Each assignment updates `x` to the new value and introduces `snap`
holding the old value of `x`.

```lean
def threadEffectsRL (σ : LaurelStore) : List ArgSpec → LaurelStore
```

Threads effects right-to-left: for `[a₁, ..., aₙ]`, applies `aₙ` first,
then `aₙ₋₁`, ..., then `a₁`. This matches the execution order of
`allPrepends` (which are accumulated newest-first).

### SpecsOK — Well-Formedness Witness

```lean
inductive SpecsOK :
    LaurelEval → ProcEnv → LaurelHeap → LaurelStore →
    MD → MD → List ArgSpec → Prop
```

An inductive witness that a spec list is well-formed:
- Snapshot names are fresh in the original store
- Snapshot names don't collide with any other spec's variables
- Target variables are defined after threading preceding effects
- Each assignment's RHS evaluates correctly in the threaded store

### `allPrepends_eval`

```lean
theorem allPrepends_eval
    (hok : SpecsOK δ π h σ md tmd specs) :
    ∃ v, EvalLaurelBlock δ π h σ
      (allPrepends md tmd specs)
      h (threadEffectsRL σ specs) (.normal v)
```

**In English:** If the spec list is well-formed, then the concatenated
prepended statements evaluate successfully, producing the threaded store.
This is proved by structural recursion on `SpecsOK`, composing single
assignment evaluations via `EvalLaurelBlock_append`.

### `lift_multi_assign_correct`

```lean
theorem lift_multi_assign_correct
    (hok : SpecsOK δ π h σ md tmd specs)
    (hargs_eval : EvalStmtArgs δ π h (threadEffectsRL σ specs)
      (cleanedArgs md specs) h (threadEffectsRL σ specs) (argValues specs))
    (hop : evalPrimOp op (argValues specs) = some result) :
    ∃ σ_final, EvalLaurelBlock δ π h σ
      (allPrepends md tmd specs ++ [⟨.PrimitiveOp op (cleanedArgs md specs), md⟩])
      h σ_final (.normal result)
```

**In English:** The full lifted block — all prepended statements followed
by the cleaned `PrimitiveOp` — evaluates to the same result as the
original expression. This composes `allPrepends_eval` with the
`PrimitiveOp` evaluation.

## Phase 4: Statement-Level transformStmt

Phase 4 lifts the expression-level results to statement-level correctness.

### Identity Cases

For statements where `transformStmt` returns `[stmt]` unchanged (Return,
Exit, Assert, Assume, literals), preservation is immediate:

```lean
theorem transformStmt_identity_correct
    (heval : EvalLaurelStmt δ π h σ s h' σ' o) :
    EvalLaurelBlock δ π h σ [s] h' σ' o
```

### Prepend Composition

When `transformStmt` produces `prepends ++ [s']`, the generic composition
theorem applies:

```lean
theorem transformStmt_prepend_correct
    (hprep : EvalLaurelBlock δ π h σ prepends h₁ σ₁ (.normal v₁))
    (hstmt : EvalLaurelStmt δ π h₁ σ₁ s h₂ σ₂ o) :
    EvalLaurelBlock δ π h σ (prepends ++ [s]) h₂ σ₂ o
```

**In English:** If the prepended statements evaluate normally (setting up
the store), and the cleaned statement evaluates in the resulting store,
then the whole block evaluates correctly.

Specialized versions exist for each statement kind: `transformStmt_assign_correct`,
`transformStmt_local_var_correct`, `transformStmt_ite_correct`,
`transformStmt_while_correct`, `transformStmt_static_call_correct`.

### Block Correctness

For blocks, `transformStmt` maps over each statement and flattens:

```lean
theorem transformStmt_block_correct
    (hinner : EvalLaurelBlock δ π h σ stmts_flat h' σ' o)
    (hcatch : catchExit label o = o') :
    EvalLaurelBlock δ π h σ
      [⟨.Block stmts_flat label, md⟩] h' σ' o'
```

### TransformOK — General Composition

```lean
inductive TransformOK :
    LaurelEval → ProcEnv → LaurelHeap → LaurelStore →
    List StmtExprMd → List StmtExprMd →
    LaurelHeap → LaurelStore → Outcome → Prop
```

An inductive witness that a list of statement transformations preserves
semantics. Each entry says: if the source statement evaluates to some
result, then the transformed statements evaluate to the same result.

Constructors handle: empty blocks, last statement (normal/exit/return),
cons with normal continuation, cons with exit/return short-circuit.

```lean
theorem TransformOK_eval
    (htok : TransformOK δ π h σ src tgt h' σ' o) :
    EvalLaurelBlock δ π h σ tgt h' σ' o
```

**In English:** If `TransformOK` holds between source and target statement
lists, then the target block evaluates correctly. This is the main
composition theorem for Phase 4.

## What Is Not Yet Proved

The current proof covers Phases 2–4 of the bottom-up approach. The
following remain as future work:

- **Phase 5: Conditional and imperative call lifting** — when
  `IfThenElse` or imperative `StaticCall` appears in expression position,
  the pass introduces fresh result variables and lifts the entire
  construct. This case is not yet covered.
- **End-to-end monadic connection** — the theorems prove that *if* the
  transformation produces certain output, then semantics is preserved.
  They do not yet formally connect to the actual monadic output of
  `transformExpr`/`transformStmt`.
- **Freshness verification** — the proofs assume snapshot names are fresh.
  A separate theorem could verify that the pass's name generation
  satisfies this assumption.

## Limitations and Assumptions

### Freshness Assumptions

All theorems in Phases 2–3 assume that snapshot variable names are fresh:

- `hfresh : σ snap.text = none` — the snapshot name is not in the store
- `hne : snap.text ≠ x.text` — the snapshot name differs from the target
- In `SpecsOK`: snapshot names don't collide with any other spec's
  variables

These conditions are assumed, not derived from the pass's name generation
logic. The pass generates names like `$x_0`, `$x_1`, `$c_0` using
counters, which in practice don't collide with user variables (which
don't start with `$`), but this is not formally verified.

### Pure Expression Assumption

The `he_ext` hypothesis in `lift_single_assign_correct` requires that
the RHS expression `e` evaluates identically in any store that agrees
with `σ` on all variables except the snapshot name. This is a purity
assumption — it says `e` does not read the snapshot variable. In
practice, this holds because snapshot names are freshly generated and
cannot appear in the original program, but the proof takes it as an
explicit hypothesis.

### Heap Invariance

The Phase 2–3 theorems assume the heap is unchanged by the expressions
being lifted (the heap `h` appears on both sides of the evaluation).
This is valid for pure expressions and simple assignments but would not
hold for expressions containing `New`, `PureFieldUpdate`, or calls that
modify the heap. The current proofs do not cover heap-modifying
expressions in argument position.

### TransformOK Weakness

The `TransformOK` inductive in Phase 4 has a noted weakness: in the
`cons_normal` constructor, the source statement produces value `_v` and
the target block produces `_v'`, but these are not required to be equal.
This means `TransformOK` does not fully specify semantic preservation
for intermediate values — only the final (heap, store, outcome) must
match. This is sufficient for the current use (since `EvalLaurelBlock`
discards intermediate normal values via `cons_normal`), but it weakens
`TransformOK` as a general specification.

### Structural Composition Only

The Phase 4 theorems (`transformStmt_prepend_correct` and its
specializations) are structural composition lemmas. They show that
`prepends ++ [s']` evaluates correctly *given that* prepends evaluate
normally and `s'` evaluates in the resulting store. They do not claim
that the prepends are semantically related to the original expression —
that connection comes from Phases 2–3 for `PrimitiveOp` arguments and
is not yet established for other constructs.

### While Loop Caveat

The `transformStmt_while_correct` theorem prepends condition-lifting
statements *before* the loop. The `while_true` rule re-evaluates the
condition on each iteration, but the prepends only execute once. This
is correct for the lifting pass (which only lifts pure snapshot
operations whose values don't change across iterations), but the theorem
does not verify this invariant — callers must ensure that prepends
capture only loop-invariant values.
