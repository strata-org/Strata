# Laurel Operational Semantics

**Date:** 2026-03-16
**File:** `Strata/Languages/Laurel/LaurelSemantics.lean`

## Overview

This document describes the big-step operational semantics for Laurel IR,
Strata's common intermediate representation for front-end languages (Java,
Python, JavaScript). The semantics is defined as a set of mutually
inductive relations directly on Laurel's `StmtExpr` AST, independent of
the Strata Core semantics.

## Motivation

Before this work, Laurel had no formal semantics of its own. Its meaning
was defined only implicitly through the translation to Strata Core in
`LaurelToCoreTranslator.lean`. This made it impossible to:

- Detect bugs in the translator (the translator *was* the semantics)
- State or prove determinism, progress, or type preservation for Laurel
- Prove that the Laurel-to-Core translation preserves program meaning
- Give a formal account of Laurel-specific constructs like labeled
  `Block`/`Exit`, the statement-expression duality, or OO features

## Semantic Domains

### Values

Laurel values are a separate type from Core expressions:

| Constructor | Description |
|-------------|-------------|
| `vInt i` | Integer value |
| `vBool b` | Boolean value |
| `vString s` | String value |
| `vVoid` | Unit/void value |
| `vRef addr` | Heap reference (address) |

### Store

The variable store is a function `LaurelStore := String → Option LaurelValue`.
Variables are keyed by the `.text` field of `Identifier`. A variable is
defined when the store maps its name to `some v`, and undefined when it
maps to `none`.

Two relational operations maintain store invariants:

- `UpdateStore σ x v σ'` — updates an existing variable (`σ x = some _`)
- `InitStore σ x v σ'` — initializes a new variable (`σ x = none`)

Both require that all other variables are unchanged.

### Heap

The heap models object allocation and field access:

```
LaurelHeap := Nat → Option (String × (String → Option LaurelValue))
```

Each heap cell maps an address to a pair of (type name, field store).
Three operations are defined:

- `AllocHeap h typeName addr h'` — allocates at the smallest free address
  (deterministic bump-allocator model)
- `heapFieldRead h addr field` — reads a field (computable function)
- `HeapFieldWrite h addr field v h'` — writes a field (relational)

### Outcomes

Non-local control flow is modeled by the `Outcome` type:

| Constructor | Description |
|-------------|-------------|
| `normal v` | Normal completion with value `v` |
| `exit label` | Exit to a labeled block (models break/continue) |
| `ret (some v)` | Return with value |
| `ret none` | Return void |

When a statement produces `exit` or `ret`, subsequent statements in the
same block are skipped. A labeled `Block` catches a matching `exit` via
the `catchExit` function.

## Judgment Forms

The semantics consists of three mutually inductive relations:

### EvalLaurelStmt

```
EvalLaurelStmt δ π h σ s h' σ' o
```

Evaluates a single statement/expression `s` in evaluator `δ`, procedure
environment `π`, heap `h`, and store `σ`, producing new heap `h'`, new
store `σ'`, and outcome `o`.

### EvalLaurelBlock

```
EvalLaurelBlock δ π h σ stmts h' σ' o
```

Evaluates a list of statements sequentially. If a statement produces
`normal`, its value is discarded (unless it is the last statement) and
execution continues. If it produces `exit` or `ret`, the remaining
statements are skipped.

### EvalStmtArgs

```
EvalStmtArgs δ π h σ args h' σ' vals
```

Evaluates a list of arguments left-to-right, threading heap and store
through each argument. Each argument must evaluate to `.normal v`;
non-local control flow in arguments has no derivation (the program gets
stuck).

## Evaluation Rules

### Literals and Variables

Literals evaluate to their corresponding value without modifying state.
`Identifier name` looks up `σ name.text` and requires it to be `some v`.

### Primitive Operations

`PrimitiveOp op args` evaluates arguments left-to-right via
`EvalStmtArgs` (which threads heap and store through each argument),
then applies `evalPrimOp` to the resulting values. This supports
effectful arguments (assignments, calls) in argument position.

### Control Flow

- `IfThenElse`: evaluates the condition, then the appropriate branch.
  The condition may modify the store (it is a full `StmtExpr`).
- `Block stmts label`: evaluates statements via `EvalLaurelBlock`, then
  applies `catchExit label` to the outcome.
- `Exit target`: immediately produces `exit target`.
- `Return`: evaluates the return value (if any) and produces `ret`.
- `While`: if the condition is true, evaluates the body; if the body
  completes normally, recurses on the same `While`. If the body exits
  or returns, that outcome propagates immediately.

### Assignments

- `assign_single`: evaluates the RHS, checks the target exists in the
  store, then updates it. Returns `.normal v` (the assigned value), not
  void — this models assignment-as-expression.
- `assign_field`: evaluates the target to a reference, evaluates the
  value, then writes to the heap field.
- `local_var_init`: evaluates the initializer, checks the variable does
  not exist, then initializes it. Returns `.normal .vVoid`.
- `local_var_uninit`: initializes the variable to `vVoid`.

### Procedure Calls

`static_call` and `instance_call` evaluate arguments via `EvalStmtArgs`,
bind parameters to values in a fresh store (lexical scoping via
`bindParams`), evaluate the body, and return the result. Three sub-rules
handle normal completion, explicit return with value, and void return.

For instance calls, the target is evaluated first to obtain a reference,
the type name is looked up on the heap, and the method is resolved as
`typeName.methodName` in the procedure environment.

### OO Features

- `new_obj`: allocates a new heap object with the given type name.
- `field_select`: evaluates the target to a reference, reads the field.
- `pure_field_update`: evaluates target and value, writes the field,
  returns the reference.
- `reference_equals`: evaluates both sides to references, compares addresses.
- `is_type`: evaluates target, looks up the type tag on the heap.
- `as_type`: evaluates target, passes through the value (no runtime check).

### Specification Constructs

`Assert` and `Assume` evaluate their condition but discard any state
effects — the result always uses the original heap and store. Quantifiers
(`Forall`, `Exists`) and specification constructs (`Old`, `Fresh`,
`Assigned`, `ContractOf`) are delegated to the expression evaluator `δ`.

## Intentionally Omitted Constructs

The following `StmtExpr` constructors have no evaluation rules:

- `Abstract` — specification-level marker, not executable
- `All` — specification-level reference to all heap objects
- `Hole` — represents incomplete programs

Programs containing these constructs get stuck (no derivation exists).

## Key Design Decisions

1. **Unified StmtExpr.** Laurel does not separate expressions from
   statements. The semantics handles this by having `EvalLaurelStmt`
   cover both, with `Outcome.normal v` carrying the "expression value."

2. **Assignment returns a value.** `assign_single` returns `.normal v`
   rather than `.normal .vVoid`. This is needed for effectful argument
   evaluation where `x := 1` in expression position should evaluate to 1.

3. **Deterministic heap allocation.** `AllocHeap` requires the address
   to be the smallest free address. This makes allocation deterministic
   but precludes heap deallocation.

4. **Store keyed by String.** The store uses `String` keys (the `.text`
   field of `Identifier`) to ensure `BEq` and `DecidableEq` agree, which
   is required by the bridging proofs.

5. **Assert/Assume discard state effects.** The condition is evaluated
   (to check it is true), but any side effects are discarded. This
   matches the denotational interpreter's behavior.

## Limitations and Assumptions

### Unsupported Constructs

The following `StmtExpr` constructors have **no evaluation rules** in
either the relational or denotational semantics. Programs using them
get stuck (no derivation / return `none`):

| Constructor | Reason |
|-------------|--------|
| `LiteralDecimal` | No runtime representation for decimals. The denotational interpreter explicitly returns `none`. The `LaurelValue` type has no float/decimal variant. |
| `Abstract` | Specification-level marker for abstract contracts. Not executable by design. |
| `All` | Specification-level reference to all heap objects (reads/modifies clauses). Not executable. |
| `Hole` | Represents incomplete programs. Not executable by design. |

### Partially Supported Constructs

| Construct | Limitation |
|-----------|------------|
| `Assign` with multiple targets | Only single-target assignment (`Assign [⟨.Identifier name, _⟩] value` and `Assign [⟨.FieldSelect target field, _⟩] value`) is handled. Multi-target assignment (for procedures with multiple outputs) has no evaluation rule. This is a known TODO. |
| `getBody` for procedures | Only `Transparent` and `Opaque` bodies with an implementation are supported. `Abstract` and `External` procedure bodies return `none` from `getBody`, so calls to such procedures get stuck. |

### Unsupported Primitive Operations

The `evalPrimOp` function handles a subset of the `Operation` type:

| Supported | Not Supported |
|-----------|---------------|
| `Eq`, `Neq`, `And`, `Or`, `Not`, `Implies` | `DivT` (truncation division) |
| `Add`, `Sub`, `Mul`, `Div`, `Mod`, `Neg` | `ModT` (truncation modulus) |
| `Lt`, `Leq`, `Gt`, `Geq`, `StrConcat` | |

Additionally, `evalPrimOp` only handles integer, boolean, string, and
reference operands. Float64 operands are not supported (there is no
`LaurelValue` variant for floats).

`Div` and `Mod` return `none` when the divisor is zero (the program
gets stuck rather than producing an error value).

### Non-Standard Design Choices

1. **Assignment returns a value.** In most languages, assignment is a
   statement that returns void. Here, `assign_single` returns
   `.normal v` (the assigned value), modeling assignment-as-expression
   like C's `=` operator. This is needed for effectful argument
   evaluation (e.g., `f(x := 1)` should evaluate to 1), but it means
   the semantics does not match languages where assignment is void.

2. **Assert/Assume discard state effects.** The condition of `Assert`
   and `Assume` is evaluated (to check it is `true`), but any side
   effects from the condition evaluation are discarded — the result
   always uses the original heap and store. This is a pragmatic choice
   that matches the denotational interpreter, but a more principled
   design would restrict conditions to a syntactically pure fragment.
   See `docs/designs/design-assert-assume-purity.md`.

3. **No heap deallocation.** The bump-allocator model (`AllocHeap`
   requires the smallest free address) makes allocation deterministic
   but precludes any `free` operation. If Laurel ever needs
   deallocation, the model must be relaxed to a free-list, which would
   invalidate `AllocHeap_deterministic` and all downstream proofs.

4. **Identifier BEq hack.** The upstream `BEq Identifier` instance
   only compares the `.text` field (ignoring `uniqueId`), described as
   a "temporary hack" in `Laurel.lean`. The semantics works around this
   by keying the store on `String` (the `.text` field) and defining a
   separate `DecidableEq Identifier` that compares both fields. Proofs
   that rely on `BEq` agreeing with `DecidableEq` must use `String`
   keys or `beq_iff_eq` explicitly.

5. **Specification constructs are opaque.** Quantifiers (`Forall`,
   `Exists`) and specification constructs (`Old`, `Fresh`, `Assigned`,
   `ContractOf`) are delegated to the expression evaluator parameter
   `δ`. The semantics does not define their meaning — it is whatever
   `δ` says. This means properties like determinism hold only when `δ`
   is itself deterministic.

6. **Only terminating programs.** The inductive semantics only captures
   terminating executions. Non-terminating programs (e.g., `while true {}`)
   have no derivation. This is standard for big-step semantics but means
   the semantics cannot distinguish non-termination from getting stuck.

7. **Non-local control flow in arguments gets stuck.** `EvalStmtArgs`
   requires each argument to produce `.normal v`. If an argument
   produces `exit` or `return` (e.g., `f(return 5)`), there is no
   derivation. This is intentional — such programs are ill-formed — but
   it is not enforced by a type system.

8. **Lexical scoping for calls.** `bindParams` creates a fresh store
   from scratch (starting from `fun _ => none`), so called procedures
   cannot access the caller's local variables. This models lexical
   scoping, not dynamic scoping. The caller's store after argument
   evaluation (`σ₁`) becomes the caller's store after the call — the
   callee's store modifications are invisible to the caller.

## Properties

The following properties are proved in `LaurelSemanticsProps.lean`:

- **Determinism:** `EvalLaurelStmt`, `EvalLaurelBlock`, and
  `EvalStmtArgs` are all deterministic — given the same inputs, they
  produce the same outputs.
- **Store monotonicity:** `UpdateStore` and `InitStore` preserve
  definedness of other variables.
- **Determinism of store/heap operations:** `UpdateStore`, `InitStore`,
  `AllocHeap`, and `HeapFieldWrite` are all deterministic.
- **Block append:** `EvalLaurelBlock_append` allows splitting evaluation
  of `ss₁ ++ ss₂` into evaluating `ss₁` then `ss₂`.
