# Design: Assert/Assume Condition Purity

## Status

**Current:** Strategy B (permissive rules, purity as convention).
**Target:** Strategy C (syntactic purity predicate with proof).

## Problem

The `assert_true` and `assume_true` rules in `LaurelSemantics.lean` govern
how assert/assume conditions are evaluated. The denotational interpreter
(`LaurelDenote.lean`) evaluates the condition, discards any state effects,
and returns the original heap and store:

```lean
-- LaurelDenote.lean
| .Assert c =>
  match denoteStmt δ π fuel h σ c.val with
  | some (.normal (.vBool true), _, _) => some (.normal .vVoid, σ, h)
  | _ => none
```

The relational semantics must match this behavior. The question is how
tightly the relational rules constrain the condition's evaluation.

## Strategy B (Current)

The relational rules allow the condition to produce arbitrary state effects,
which are then discarded:

```lean
| assert_true :
    EvalLaurelStmt δ π h σ c h' σ' (.normal (.vBool true)) →
    EvalLaurelStmt δ π h σ ⟨.Assert c, md⟩ h σ (.normal .vVoid)
```

The condition evaluates to `(h', σ', .normal (.vBool true))` for some `h'`
and `σ'`, but the Assert returns the original `(h, σ)`.

**Pros:**
- Soundness and completeness proofs are straightforward — the denotational
  interpreter and relational semantics agree exactly.
- No `sorry`s needed.
- Determinism is preserved (the output is always `(h, σ, .normal .vVoid)`).

**Cons:**
- The relational semantics doesn't enforce that assert conditions are pure.
  A program with `assert(x := 1; x > 0)` has a valid derivation even though
  the assignment is discarded. This is arguably a semantic bug — the
  assignment happens in the denotational interpreter but its effects vanish.
- Downstream analyses that assume "if `assert_true` holds, the condition
  didn't modify state" would be wrong.

## Strategy C (Target): Syntactic Purity Predicate

### Overview

Define a predicate `IsPure : StmtExpr → Prop` that identifies the
side-effect-free fragment of `StmtExpr`, prove that pure expressions
preserve state, and strengthen the relational rules to require purity.

### Step 1: Define `IsPure`

```lean
inductive IsPure : StmtExpr → Prop where
  | literal_int  : IsPure (.LiteralInt i)
  | literal_bool : IsPure (.LiteralBool b)
  | literal_str  : IsPure (.LiteralString s)
  | identifier   : IsPure (.Identifier name)
  | prim_op      : (∀ a ∈ args, IsPure a.val) → IsPure (.PrimitiveOp op args)
  | ite          : IsPure c.val → IsPure t.val → IsPure e.val →
                   IsPure (.IfThenElse c t (some e))
  | ite_no_else  : IsPure c.val → IsPure t.val →
                   IsPure (.IfThenElse c t none)
  | field_select : IsPure target.val → IsPure (.FieldSelect target field)
  | forall_sem   : IsPure (.Forall param trigger body)
  | exists_sem   : IsPure (.Exists param trigger body)
  | old_sem      : IsPure (.Old val)
  | ref_eq       : IsPure lhs.val → IsPure rhs.val →
                   IsPure (.ReferenceEquals lhs rhs)
  | is_type      : IsPure target.val → IsPure (.IsType target ty)
  | as_type      : IsPure target.val → IsPure (.AsType target ty)
```

Notably absent: `Assign`, `LocalVariable`, `StaticCall`, `InstanceCall`,
`New`, `PureFieldUpdate`, `While`, `Return`, `Exit`, `Block`.

### Step 2: Prove state preservation for pure expressions

```lean
theorem isPure_preserves_state :
    IsPure s →
    EvalLaurelStmt δ π h σ ⟨s, md⟩ h' σ' outcome →
    h' = h ∧ σ' = σ
```

Proof by mutual induction on `IsPure` and `EvalLaurelStmt`. Each pure
constructor maps to evaluation rules that don't modify state:
- Literals: `h' = h, σ' = σ` by definition.
- `Identifier`: just a store lookup, no modification.
- `PrimitiveOp`: arguments are pure (by IH), so state threads through
  unchanged. The operation itself doesn't modify state.
- `IfThenElse`: condition and chosen branch are pure (by IH).
- `FieldSelect`: target is pure (by IH), field read doesn't modify state.
- Quantifiers/Old/Fresh/Assigned: delegated to `δ`, which by convention
  doesn't modify state (this would need `δ` to be pure as a hypothesis).

**Complication:** `PrimitiveOp` uses `EvalStmtArgs` which threads state
through arguments left-to-right. We'd need a lemma:

```lean
theorem isPure_args_preserves_state :
    (∀ a ∈ args, IsPure a.val) →
    EvalStmtArgs δ π h σ args h' σ' vals →
    h' = h ∧ σ' = σ
```

This follows by induction on `EvalStmtArgs`, applying
`isPure_preserves_state` at each step.

**Complication:** Quantifiers and specification constructs (`Old`, `Fresh`,
`Assigned`, `ContractOf`) are delegated to the expression evaluator `δ`.
The state preservation proof would need a hypothesis that `δ` is pure:

```lean
(hδ_pure : ∀ σ e, δ σ e = some v → True)  -- δ doesn't touch heap/store
```

This is trivially true since `δ : LaurelStore → StmtExpr → Option LaurelValue`
doesn't even receive the heap, and returns a value without a new store.

### Step 3: Strengthen the relational rules

```lean
| assert_true :
    IsPure c.val →
    EvalLaurelStmt δ π h σ c h σ (.normal (.vBool true)) →
    EvalLaurelStmt δ π h σ ⟨.Assert c, md⟩ h σ (.normal .vVoid)
```

With `IsPure c.val` as a premise, `isPure_preserves_state` guarantees
`h' = h ∧ σ' = σ`, so the condition evaluation can use `h σ` in both
input and output positions.

### Step 4: Update soundness proof

The soundness proof would need to show that when the denotational
interpreter succeeds on `Assert c`, the condition `c` is pure. This
requires either:

(a) The denotational interpreter checks purity (Strategy A — not feasible
    for function-typed stores), or

(b) The soundness theorem adds `IsPure c.val` as a hypothesis for the
    Assert/Assume cases, or

(c) A well-formedness predicate on programs that ensures all assert/assume
    conditions are syntactically pure, threaded through the soundness proof.

Option (c) is the most realistic: define `WellFormed : StmtExpr → Prop`
that checks (among other things) that assert/assume conditions are pure,
and make the soundness theorem conditional on well-formedness.

### Step 5: Update completeness proof

The completeness proof would need `IsPure c.val` to construct the
`assert_true` derivation. This comes from the well-formedness hypothesis.

### Estimated Effort

| Step | Effort | Dependencies |
|------|--------|-------------|
| Define `IsPure` | Small | None |
| Prove `isPure_preserves_state` | Medium | Mutual induction with `EvalStmtArgs` |
| Strengthen relational rules | Small | Step 1 |
| Define `WellFormed` | Medium | Step 1 |
| Update soundness proof | Medium | Steps 2, 3, 4 |
| Update completeness proof | Small | Steps 3, 4 |
| Update determinism proof | Small | Step 3 |
| Update correctness proofs | Small | Step 3 (if they use assert/assume) |

Total: ~2-3 days of focused work.

### Migration Path

1. Implement Steps 1-2 as standalone lemmas (no breaking changes).
2. Add `IsPure` to the relational rules (Step 3) — this breaks soundness
   and completeness proofs.
3. Define `WellFormed` and update proofs (Steps 4-6).
4. Remove Strategy B's permissive rules.

Steps 1-2 can be done incrementally without breaking anything. Step 3 is
the breaking change that requires Steps 4-6 to be done together.
