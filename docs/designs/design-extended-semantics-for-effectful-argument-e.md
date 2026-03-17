# Design: Extended Semantics for Effectful Argument Evaluation

**Date:** 2026-03-10
**Status:** Proposal

## 1. Problem Statement

The current Laurel operational semantics (`LaurelSemantics.lean`) evaluates
call arguments using `EvalArgs`, which delegates to the pure expression
evaluator `δ`. This means any argument with side effects — assignments,
imperative calls, or blocks containing assignments — has no derivation.
The program gets stuck.

This is a problem because Laurel's `StmtExpr` AST intentionally unifies
statements and expressions. Real Laurel programs (translated from Java,
Python, JavaScript) can contain effectful expressions in argument position.
The `liftImperativeExpressions` pass (`LiftImperativeExpressions.lean`)
transforms these into equivalent programs where arguments are pure, but
we cannot state or prove its correctness without a "before" semantics
that gives meaning to the un-lifted programs.

### Concrete examples

**Assignment in argument position:**
```
// Laurel pseudocode
var x: int := 0;
var y: int := x + (x := 1;) + x;
```

Under left-to-right evaluation, this should produce `y = 0 + 1 + 1 = 2`:
the first `x` reads 0, then `x := 1` updates x and evaluates to 1, then
the second `x` reads the updated value 1. Currently, `prim_op` uses
`EvalArgs δ σ args vals`, which requires `δ σ arg = some v` for each
argument. Since `δ` is pure, `x := 1` has no `δ`-value, so no derivation
exists.

**Imperative call in argument position:**
```
// Laurel pseudocode
var z: int := f(g(x));  // where g modifies global state
```

Same issue: `g(x)` is a `StaticCall` that modifies the store, but
`EvalArgs` requires a pure evaluation.

**Why this matters for correctness:**
The `liftImperativeExpressions` pass transforms the first example into:
```
var $x_1 := x;     // snapshot x before first assignment
x := 1;            // lifted assignment
var $x_0 := x;     // snapshot x before second assignment (not present here, but pattern)
var y: int := $x_1 + x + x;
```

To prove this transformation correct, we need:
1. A semantics for the source program (with effectful args) — **this design**
2. A semantics for the target program (pure args) — already exists
3. A theorem: both produce the same final store and outcome

## 2. Background

### 2.1 Current argument evaluation

`EvalArgs` is defined outside the `mutual` block as a non-mutual inductive:

```lean
inductive EvalArgs : LaurelEval → LaurelStore → List StmtExprMd → List LaurelValue → Prop where
  | nil  : EvalArgs δ σ [] []
  | cons : δ σ e.val = some v → EvalArgs δ σ es vs → EvalArgs δ σ (e :: es) (v :: vs)
```

Key properties:
- Uses the pure evaluator `δ : LaurelStore → StmtExpr → Option LaurelValue`
- Does not thread store or heap — all arguments see the same `σ`
- Cannot evaluate `Assign`, `StaticCall` (imperative), `Block` with assignments

It is used by `prim_op`, `static_call`, `static_call_return`,
`static_call_return_void`, `instance_call`, `instance_call_return`, and
`instance_call_return_void`.

### 2.2 The mutual inductive block

`EvalLaurelStmt` and `EvalLaurelBlock` are mutually inductive. Adding a
third relation to this block is the natural way to define store-threading
argument evaluation, since it must reference `EvalLaurelStmt` (to evaluate
each argument as a statement) and be referenced by `EvalLaurelStmt` (in
the `prim_op` and call rules).

### 2.3 Assignment return value

The current `assign_single` rule returns `.normal .vVoid`:

```lean
| assign_single :
    EvalLaurelStmt δ π h σ value h₁ σ₁ (.normal v) →
    σ₁ name = some _ →
    UpdateStore σ₁ name v σ₂ →
    EvalLaurelStmt δ π h σ ⟨.Assign [⟨.Identifier name, tmd⟩] value, md⟩ h₁ σ₂ (.normal .vVoid)
```

For effectful argument evaluation, we need `x := 1` in expression position
to evaluate to the assigned value (1), not void. The lifting pass relies
on this: it replaces `x := 1` with a snapshot variable that holds the
value that was assigned.

### 2.4 Determinism proof

`LaurelSemanticsProps.lean` contains a mutual determinism proof
(`EvalLaurelStmt_deterministic` / `EvalLaurelBlock_deterministic`) that
covers all current constructors. Any change to the `mutual` block requires
updating this proof. The proof currently uses `EvalArgs_deterministic` for
the `prim_op` and call cases.

### 2.5 The liftImperativeExpressions pass

`LiftImperativeExpressions.lean` transforms programs by:
1. Traversing arguments right-to-left
2. Lifting assignments to preceding statements with snapshot variables
3. Lifting imperative calls similarly
4. Handling if-then-else in expression position by introducing fresh variables

The pass produces programs where all arguments to `PrimitiveOp` and
`StaticCall` are pure. The correctness theorem would state: for any
program `p`, evaluating `p` under the extended semantics produces the
same result as evaluating `liftImperativeExpressions p` under the
existing (or extended) semantics.

## 3. Design Options

### Option A: Mutual `EvalStmtArgs` + change `assign_single` to return assigned value

Add `EvalStmtArgs` to the mutual block. Change `assign_single` to return
the assigned value instead of void.

#### a. Implementation strategy

**LaurelSemantics.lean** — three changes:

1. Add `EvalStmtArgs` to the `mutual` block:
```lean
inductive EvalStmtArgs :
    LaurelEval → ProcEnv → LaurelHeap → LaurelStore →
    List StmtExprMd → LaurelHeap → LaurelStore →
    List LaurelValue → Prop where
  | nil  : EvalStmtArgs δ π h σ [] h σ []
  | cons :
    EvalLaurelStmt δ π h σ e h₁ σ₁ (.normal v) →
    EvalStmtArgs δ π h₁ σ₁ es h₂ σ₂ vs →
    EvalStmtArgs δ π h σ (e :: es) h₂ σ₂ (v :: vs)
```

2. Replace `EvalArgs` with `EvalStmtArgs` in `prim_op` and all 6 call
   constructors (`static_call`, `static_call_return`,
   `static_call_return_void`, `instance_call`, `instance_call_return`,
   `instance_call_return_void`):
```lean
-- prim_op (old → new)
| prim_op :
    EvalStmtArgs δ π h σ args h' σ' vals →
    evalPrimOp op vals = some result →
    EvalLaurelStmt δ π h σ ⟨.PrimitiveOp op args, md⟩ h' σ' (.normal result)
```

   Similarly for calls: the heap/store output of `EvalStmtArgs` feeds into
   `bindParams` and the body evaluation. For `static_call`:
```lean
| static_call :
    π callee = some proc →
    EvalStmtArgs δ π h σ args h₁ σ₁ vals →
    bindParams proc.inputs vals = some σBound →
    getBody proc = some body →
    EvalLaurelStmt δ π h₁ σBound body h' σ' (.normal v) →
    EvalLaurelStmt δ π h σ ⟨.StaticCall callee args, md⟩ h' σ₁ (.normal v)
```

   For `instance_call`, the target is evaluated first (already threads
   heap/store), then `EvalStmtArgs` starts from the target's output state:
```lean
| instance_call :
    EvalLaurelStmt δ π h σ target h₁ σ₁ (.normal (.vRef addr)) →
    h₁ addr = some (typeName, _) →
    π (typeName ++ "." ++ callee) = some proc →
    EvalStmtArgs δ π h₁ σ₁ args h₂ σ₂ vals →
    bindParams proc.inputs ((.vRef addr) :: vals) = some σBound →
    getBody proc = some body →
    EvalLaurelStmt δ π h₂ σBound body h₃ σ₃ (.normal v) →
    EvalLaurelStmt δ π h σ ⟨.InstanceCall target callee args, md⟩ h₃ σ₂ (.normal v)
```

3. Change `assign_single` to return the assigned value:
```lean
| assign_single :
    EvalLaurelStmt δ π h σ value h₁ σ₁ (.normal v) →
    σ₁ name = some _ →
    UpdateStore σ₁ name v σ₂ →
    EvalLaurelStmt δ π h σ ⟨.Assign [⟨.Identifier name, tmd⟩] value, md⟩ h₁ σ₂ (.normal v)
```

   This is safe because statement-level code discards the return value via
   `cons_normal` (which ignores `_v`).

**LaurelSemanticsProps.lean** — update determinism proof:

- Add `EvalStmtArgs_deterministic` to the mutual block
- Update `prim_op` case to use `EvalStmtArgs_deterministic` and propagate
  heap/store equality
- Update all 6 call cases similarly
- The `assign_single` case proof structure is unchanged (just different
  output value)

#### b. Internal representation

`EvalStmtArgs` threads `(LaurelHeap, LaurelStore)` through a list of
arguments left-to-right, producing a list of values. Each argument is
evaluated as a full `EvalLaurelStmt`, so assignments, calls, blocks —
anything — can appear in argument position.

The judgment form is:
```
δ, π, h, σ, [e₁, ..., eₙ] ⊢ h', σ', [v₁, ..., vₙ]
```
where `h', σ'` is the state after evaluating all arguments.

#### c. End-to-end correctness

The correctness chain is:

1. **Backward compatibility lemma** — For pure arguments (where each `eᵢ`
   evaluates without changing heap/store), `EvalStmtArgs` agrees with
   `EvalArgs`:
```lean
theorem EvalStmtArgs_pure_compat :
    (∀ i e, args[i]? = some e → ∃ v, EvalLaurelStmt δ π h σ e h σ (.normal v) ∧ δ σ e.val = some v) →
    EvalStmtArgs δ π h σ args h σ vals →
    EvalArgs δ σ args vals
```

2. **Lifting correctness** — The main theorem for `liftImperativeExpressions`:
```lean
theorem liftImperativeExpressions_correct :
    EvalLaurelStmt δ π h σ s h' σ' outcome →
    EvalLaurelStmt δ π h σ (liftImperativeExpressions s) h' σ' outcome
```
   (Simplified; the actual statement will need to account for the
   transformation operating on procedures/programs, not individual
   statements.)

3. **Existing pipeline** — Programs after lifting have pure arguments, so
   the existing `EvalArgs`-based semantics (or the new `EvalStmtArgs` with
   pure args) applies. The Laurel→Core translation correctness proof
   (future work) can target either semantics.

#### d. Testing strategy

**Unit tests** (`LaurelSemanticsTest.lean`):
- Test `EvalStmtArgs` with pure arguments (should match `EvalArgs` results)
- Test `prim_op` with an assignment in argument position:
  `x + (x := 1;)` where `x` starts at 0 → result is `0 + 1 = 1`
- Test `assign_single` returns the assigned value (not void)
- Test `static_call` with effectful arguments
- Test nested effectful arguments: `f((x := 1;), (x := 2;))` → args are `[1, 2]`, final `x = 2`

**Property tests**: Determinism still holds (the proof itself is the test).

**Limitations**:
- Non-local control flow in arguments (e.g., `f(return 5)`) produces
  `Outcome.ret` from the argument, which has no `EvalStmtArgs` derivation
  (the `cons` constructor requires `.normal v`). This is intentional —
  such programs are ill-formed.

#### e. Complexity and risk

**Files changed:** 2 (`LaurelSemantics.lean`, `LaurelSemanticsProps.lean`)

**Risk: Lean mutual inductive limitations.** Adding a third inductive to
the mutual block may increase elaboration time or hit Lean 4 kernel
limitations. The original `EvalArgs` was kept non-mutual specifically to
avoid this. Mitigation: the `EvalStmtArgs` type is structurally simple
(just `nil`/`cons`), so the risk is moderate.

**Risk: Determinism proof complexity.** The proof is already ~400 lines
with `maxHeartbeats 800000`. Adding `EvalStmtArgs_deterministic` and
updating 7 constructor cases (prim_op + 6 calls) will increase this.
The heap/store threading adds intermediate equalities to propagate.
Mitigation: extract a shared helper lemma for the call-case prefix
(proc lookup → args → bind → body → outcome discrimination) as the
existing TODO suggests.

**Risk: `assign_single` semantic change.** Changing the return value from
`.vVoid` to `.normal v` is observable if any code pattern-matches on the
outcome of an assignment. In practice, `cons_normal` discards `_v`, so
statement-level assignments are unaffected. But any existing proof that
assumes `assign_single` returns `.vVoid` will break. Mitigation: grep
for such assumptions; the test file and props file are the only consumers.

### Option B: Separate `EvalStmtArgs` outside mutual block + `assign_expr` constructor

Keep `EvalStmtArgs` outside the mutual block by parameterizing it over
an evaluation relation. Add a separate `assign_expr` constructor for
assignments in expression position.

#### a. Implementation strategy

Define `EvalStmtArgs` as a standalone inductive parameterized by the
statement evaluator:

```lean
inductive EvalStmtArgs
    (Eval : LaurelEval → ProcEnv → LaurelHeap → LaurelStore →
            StmtExprMd → LaurelHeap → LaurelStore → Outcome → Prop) :
    LaurelEval → ProcEnv → LaurelHeap → LaurelStore →
    List StmtExprMd → LaurelHeap → LaurelStore →
    List LaurelValue → Prop where
  | nil  : EvalStmtArgs Eval δ π h σ [] h σ []
  | cons :
    Eval δ π h σ e h₁ σ₁ (.normal v) →
    EvalStmtArgs Eval δ π h₁ σ₁ es h₂ σ₂ vs →
    EvalStmtArgs Eval δ π h σ (e :: es) h₂ σ₂ (v :: vs)
```

Then in the `prim_op` rule, use `EvalStmtArgs EvalLaurelStmt`:
```lean
| prim_op :
    EvalStmtArgs EvalLaurelStmt δ π h σ args h' σ' vals →
    evalPrimOp op vals = some result →
    EvalLaurelStmt δ π h σ ⟨.PrimitiveOp op args, md⟩ h' σ' (.normal result)
```

Add `assign_expr` as a new constructor:
```lean
| assign_expr :
    EvalLaurelStmt δ π h σ value h₁ σ₁ (.normal v) →
    σ₁ name = some _ →
    UpdateStore σ₁ name v σ₂ →
    EvalLaurelStmt δ π h σ ⟨.Assign [⟨.Identifier name, tmd⟩] value, md⟩ h₁ σ₂ (.normal v)
```

#### b. Internal representation

Same threading model as Option A, but `EvalStmtArgs` is parameterized
rather than mutual. The `assign_expr` constructor coexists with
`assign_single` — the same syntax has two rules.

#### c. End-to-end correctness

**Problem: non-strict positivity.** Lean 4's kernel requires strict
positivity for inductive types. `EvalStmtArgs EvalLaurelStmt` appearing
in a premise of `EvalLaurelStmt` means `EvalLaurelStmt` occurs in a
negative position (as an argument to `EvalStmtArgs`). **This will be
rejected by Lean's kernel.** This is the fundamental reason the original
code used `EvalArgs` with `δ` instead.

Even if we could work around this (e.g., via well-founded recursion on
derivation depth), the `assign_expr` constructor makes the semantics
non-deterministic: `assign_single` and `assign_expr` both apply to the
same syntax `Assign [Identifier name] value`. The determinism proof
would need to show they produce the same store (they do, since both
evaluate `value` the same way), but the outcomes differ (`.vVoid` vs
`.normal v`), so determinism fails.

#### d. Testing strategy

Same tests as Option A, plus tests showing both `assign_single` and
`assign_expr` apply to the same program (demonstrating non-determinism).

#### e. Complexity and risk

**Files changed:** 2-3

**Risk: Lean rejects the definition.** The strict positivity violation
is a hard blocker. This option is likely not implementable in Lean 4
without significant workarounds (e.g., encoding as a well-founded
relation, which would lose the benefits of inductive types for proof).

**Risk: Non-determinism.** Having two rules for the same syntax
complicates all downstream proofs. Every theorem about `Assign` must
consider both cases.

### Option C: Mutual `EvalStmtArgs` + keep `assign_single` returning void + add `assign_expr`

Like Option A but keep `assign_single` unchanged and add `assign_expr`
as a separate constructor. This preserves backward compatibility for
statement-level assignments.

#### a. Implementation strategy

Same as Option A for `EvalStmtArgs` (mutual block). Keep `assign_single`
returning `.normal .vVoid`. Add:

```lean
| assign_expr :
    EvalLaurelStmt δ π h σ value h₁ σ₁ (.normal v) →
    σ₁ name = some _ →
    UpdateStore σ₁ name v σ₂ →
    EvalLaurelStmt δ π h σ ⟨.Assign [⟨.Identifier name, tmd⟩] value, md⟩ h₁ σ₂ (.normal v)
```

#### b. Internal representation

Same as Option A for argument threading. Assignments have two rules:
`assign_single` (returns void) and `assign_expr` (returns value).

#### c. End-to-end correctness

**Non-determinism breaks the determinism theorem.** Given `x := 1`, both
`assign_single` (outcome `.normal .vVoid`) and `assign_expr` (outcome
`.normal (.vInt 1)`) apply. The heap and store outputs are identical, but
the outcomes differ. `EvalLaurelStmt_deterministic` would need to be
weakened to only assert `h₁ = h₂ ∧ σ₁ = σ₂` without `o₁ = o₂`, or
the theorem statement would need to exclude `Assign` nodes.

This weakening propagates: any theorem that depends on outcome
determinism (e.g., proving that a transformation preserves the final
value of a program) would need to handle both outcomes.

The lifting correctness proof would need to show that the transformation
maps `assign_expr` derivations (in the source) to equivalent derivations
(in the target), while `assign_single` derivations at statement level
are preserved unchanged.

#### d. Testing strategy

Same as Option A, plus explicit tests for both `assign_single` and
`assign_expr` on the same syntax.

#### e. Complexity and risk

**Files changed:** 2

**Risk: Non-determinism.** Same as Option B. The determinism proof either
breaks or must be weakened. Every downstream proof about assignments must
handle two cases.

**Risk: Proof burden.** The lifting correctness proof must reason about
which rule was used in the source derivation. This is manageable but adds
complexity compared to a deterministic semantics.

## 4. Recommendation

**Option A: Mutual `EvalStmtArgs` + change `assign_single` to return assigned value.**

Rationale:

1. **Determinism is preserved.** This is the single most important
   property for downstream proofs. Options B and C introduce
   non-determinism, which weakens the determinism theorem and complicates
   every proof that depends on it.

2. **The `assign_single` change is safe.** Statement-level assignments
   discard the return value via `cons_normal` (which binds `_v` and
   ignores it). No existing code or proof depends on the specific value
   being `.vVoid`. The change makes assignments behave like C's `=`
   operator (returns the assigned value), which is the natural semantics
   for a language that unifies statements and expressions.

3. **Lean 4 feasibility.** Adding a third inductive to the mutual block
   is the standard approach. The original `EvalArgs` workaround was
   explicitly documented as a limitation ("Lean 4 mutual inductive
   limitations"). The `EvalStmtArgs` type is structurally simple — just
   `nil`/`cons` with one `EvalLaurelStmt` premise — so the risk of
   hitting kernel limits is low.

4. **Option B is not implementable.** The strict positivity violation
   is a hard blocker in Lean 4.

5. **Minimal diff.** Only 2 files change. The `EvalStmtArgs` definition
   is 6 lines. The `prim_op` and call constructor changes are mechanical
   (replace `EvalArgs` with `EvalStmtArgs`, add heap/store threading).
   The determinism proof update follows the existing pattern.

### Implementation plan

1. Add `EvalStmtArgs` to the `mutual` block in `LaurelSemantics.lean`
2. Update `prim_op` and all 6 call constructors to use `EvalStmtArgs`
3. Change `assign_single` to return `.normal v`
4. Add `EvalStmtArgs_deterministic` to the mutual determinism proof
5. Update `prim_op` and call cases in the determinism proof
6. Add unit tests for effectful argument evaluation
7. State the backward compatibility lemma (`EvalStmtArgs_pure_compat`)
8. Verify the build passes: `lake build`
