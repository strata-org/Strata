# Proof of Equivalence Between Operational and Denotational Semantics

**Date:** 2026-03-16
**Files:**
- `Strata/Languages/Laurel/LaurelDenoteSound.lean` — soundness
- `Strata/Languages/Laurel/LaurelDenoteComplete.lean` — completeness
- `Strata/Languages/Laurel/LaurelDenoteEquiv.lean` — equivalence corollaries

## Overview

This document explains the proof that the fuel-based denotational
interpreter (`denoteStmt`) and the relational operational semantics
(`EvalLaurelStmt`) define the same semantics for Laurel IR. The proof
has two directions — soundness and completeness — which are combined
into bidirectional equivalence theorems and used to derive determinism
of the interpreter.

## The Two Semantics

**Relational (operational):** `EvalLaurelStmt δ π h σ s h' σ' o` is an
inductive relation. A derivation is a proof tree built from inference
rules. It is not computable.

**Functional (denotational):** `denoteStmt δ π fuel h σ s.val` is a
computable function returning `Option (Outcome × LaurelStore × LaurelHeap)`.
It uses a fuel parameter for termination.

## Part 1: Soundness

**Statement:** If the denotational interpreter returns a result, then the
relational semantics has a matching derivation.

### Main Theorems

```lean
theorem denoteStmt_sound (fuel : Nat)
    {h : LaurelHeap} {σ : LaurelStore} {s : StmtExpr}
    {o : Outcome} {σ' : LaurelStore} {h' : LaurelHeap}
    (md : MD)
    (heval : denoteStmt δ π fuel h σ s = some (o, σ', h')) :
    EvalLaurelStmt δ π h σ ⟨s, md⟩ h' σ' o
```

In English: if `denoteStmt` with `fuel` steps evaluates statement `s`
starting from heap `h` and store `σ`, producing outcome `o`, new store
`σ'`, and new heap `h'`, then there exists a derivation in the relational
semantics `EvalLaurelStmt` with the same inputs and outputs. The metadata
`md` is arbitrary — the relational semantics is parametric in metadata.

```lean
theorem denoteBlock_sound (fuel : Nat)
    {h : LaurelHeap} {σ : LaurelStore} {ss : List StmtExprMd}
    {o : Outcome} {σ' : LaurelStore} {h' : LaurelHeap}
    (heval : denoteBlock δ π fuel h σ ss = some (o, σ', h')) :
    EvalLaurelBlock δ π h σ ss h' σ' o
```

In English: if `denoteBlock` evaluates a list of statements `ss` to
outcome `o` with final store `σ'` and heap `h'`, then `EvalLaurelBlock`
has a matching derivation.

```lean
theorem denoteArgs_sound (fuel : Nat)
    {h : LaurelHeap} {σ : LaurelStore} {as : List StmtExprMd}
    {vs : List LaurelValue} {σ' : LaurelStore} {h' : LaurelHeap}
    (heval : denoteArgs δ π fuel h σ as = some (vs, σ', h')) :
    EvalStmtArgs δ π h σ as h' σ' vs
```

In English: if `denoteArgs` evaluates arguments `as` to values `vs`
with final store `σ'` and heap `h'`, then `EvalStmtArgs` has a matching
derivation.

### Proof Strategy

The proof proceeds by mutual induction on `fuel`, then case-splitting
on the input statement/expression.

For each constructor:
1. Unfold `denoteStmt` to expose the match chain
2. Pattern-match on intermediate results (using `match ... with`)
3. Apply the induction hypothesis to sub-calls (at fuel `n` when the
   outer call uses fuel `n + 1`)
4. Construct the relational derivation using the appropriate constructor

For example, for `IfThenElse c thenBr (some elseBr)`:
- Match on `denoteStmt δ π n h σ c.val`
- If it returns `some (.normal (.vBool true), σ₁, h₁)`, apply IH to get
  `EvalLaurelStmt` for the condition, then apply IH to the then-branch,
  and construct `.ite_true`
- If it returns `some (.normal (.vBool false), σ₁, h₁)`, similarly
  construct `.ite_false`
- All other patterns (non-boolean, exit, return, none) lead to
  contradictions via `simp`

### Helper Lemmas

Three complex cases are extracted into private helper lemmas to stay
within Lean's heartbeat limits:

- `denoteStmt_sound_while` — handles the `While` case, which has three
  sub-cases (true+normal→recurse, true+exit, true+return, false)
- `denoteStmt_sound_static_call` — handles `StaticCall`, which chains
  argument evaluation, parameter binding, body lookup, and body evaluation
- `denoteStmt_sound_instance_call` — handles `InstanceCall`, which adds
  target evaluation and type-based method resolution

### Bridging Lemma Usage

The soundness proof uses the "sound" direction of bridging lemmas:
- `updateStore_sound` — when `denoteStmt` calls `updateStore` and gets
  `some σ₂`, the proof invokes this to get `UpdateStore σ₁ x.text v σ₂`
- `initStore_sound` — analogous for `initStore`
- `allocHeap_sound` — analogous for `allocHeap`
- `heapFieldWrite_sound` — analogous for `heapFieldWrite'`

### Resource Requirements

The main `denoteStmt_sound` theorem requires `maxHeartbeats 6400000` and
`maxRecDepth 4096` due to the large number of `StmtExpr` constructors
(~35) and the depth of the mutual recursion.

## Part 2: Completeness

**Statement:** If the relational semantics has a derivation, then the
denotational interpreter succeeds with enough fuel.

### Main Theorems

```lean
theorem denoteStmt_complete
    {h : LaurelHeap} {σ : LaurelStore}
    {s : StmtExprMd} {h' : LaurelHeap} {σ' : LaurelStore} {o : Outcome}
    (heval : EvalLaurelStmt δ π h σ s h' σ' o)
    (hib : ∀ hx, HeapInBound hx) :
    ∃ fuel, denoteStmt δ π fuel h σ s.val = some (o, σ', h')
```

In English: if the relational semantics derives that statement `s`
evaluates from `(h, σ)` to `(h', σ', o)`, and every heap encountered
has a free address within the search bound, then there exists a fuel
value such that `denoteStmt` returns the same result.

The `HeapInBound` precondition is needed because the computable
`allocHeap` searches a bounded range for free addresses, while the
relational `AllocHeap` has no such bound. For any program allocating
fewer than 10000 objects, this condition is trivially satisfied.

```lean
theorem denoteBlock_complete
    (heval : EvalLaurelBlock δ π h σ ss h' σ' o)
    (hib : ∀ hx, HeapInBound hx) :
    ∃ fuel, denoteBlock δ π fuel h σ ss = some (o, σ', h')
```

```lean
theorem denoteArgs_complete
    (heval : EvalStmtArgs δ π h σ as h' σ' vs)
    (hib : ∀ hx, HeapInBound hx) :
    ∃ fuel, denoteArgs δ π fuel h σ as = some (vs, σ', h')
```

### Proof Strategy

The proof proceeds by pattern-matching on the relational derivation
(the `EvalLaurelStmt` constructor).

For each constructor:
1. Recursively obtain fuel values for sub-derivations
2. Combine fuels (typically `f₁ + f₂ + ... + 1`)
3. Use `denoteStmt_fuel_mono` to show that the combined fuel suffices
   for each sub-call
4. Unfold `denoteStmt` and `simp` to show the result matches

For example, for `.ite_true hc hthen`:
1. Get `⟨f₁, hf₁⟩` from `denoteStmt_complete hc hib` (condition)
2. Get `⟨f₂, hf₂⟩` from `denoteStmt_complete hthen hib` (then-branch)
3. Use fuel `(f₁ + f₂) + 1`
4. Apply `denoteStmt_fuel_mono` to show `hf₁` holds at fuel `f₁ + f₂`
   (since `f₁ ≤ f₁ + f₂`)
5. Apply `denoteStmt_fuel_mono` to show `hf₂` holds at fuel `f₁ + f₂`
6. Unfold and simplify

### Fuel Monotonicity Usage

Fuel monotonicity (`denoteStmt_fuel_mono`) is the key technical tool.
When composing sub-derivations that each require different fuel amounts,
we take the sum and use monotonicity to lift each sub-result to the
common fuel level. The pattern `show fᵢ ≤ f₁ + f₂ + ... by omega`
appears throughout.

### Bridging Lemma Usage

The completeness proof uses the "complete" direction of bridging lemmas:
- `updateStore_complete` — given `UpdateStore σ x.text v σ'`, produces
  `updateStore σ x v = some σ'`
- `initStore_complete` — analogous
- `allocHeap_complete` — requires `addr ≤ heapSearchBound`
- `heapFieldWrite_complete` — analogous

### Helper Lemmas for Block Cases

Three private helpers handle block evaluation patterns:
- `denoteBlock_exit_of_head` — if the first statement exits, the block exits
- `denoteBlock_return_of_head` — if the first statement returns, the block returns
- `denoteBlock_cons_normal` — if the first statement completes normally
  and the rest evaluates, the whole block evaluates

### Resource Requirements

`denoteStmt_complete` requires `maxHeartbeats 12800000` and
`maxRecDepth 4096`.

## Part 3: Equivalence Corollaries

`LaurelDenoteEquiv.lean` combines soundness and completeness into
clean bidirectional theorems.

### Equivalence (iff) Theorems

```lean
theorem denoteStmt_iff
    (hib : ∀ hx, HeapInBound hx) :
    (∃ fuel, denoteStmt δ π fuel h σ s.val = some (o, σ', h')) ↔
    EvalLaurelStmt δ π h σ s h' σ' o
```

In English: under the heap bound assumption, a result is reachable by
the interpreter (for some fuel) if and only if the relational semantics
has a derivation. This is the central equivalence theorem.

Analogous `_iff` theorems exist for `denoteBlock` and `denoteArgs`.

### Determinism of the Interpreter

```lean
theorem denoteStmt_deterministic
    (h₁ : denoteStmt δ π fuel₁ h σ s.val = some r₁)
    (h₂ : denoteStmt δ π fuel₂ h σ s.val = some r₂) :
    r₁ = r₂
```

In English: if the interpreter returns results at two different fuel
levels, the results are identical. This follows from soundness (both
results correspond to relational derivations) plus relational determinism
(the relational semantics is deterministic, proved in
`LaurelSemanticsProps.lean`).

Note that this theorem does *not* require the `HeapInBound` assumption —
it only uses soundness, not completeness.

Analogous determinism theorems exist for `denoteBlock` and `denoteArgs`.

## Proof Architecture Summary

```
LaurelSemantics.lean          LaurelDenote.lean
  (relational)                  (functional)
       │                             │
       │                             │
       ▼                             ▼
LaurelSemanticsProps.lean     LaurelDenoteMono.lean
  (determinism)                 (fuel monotonicity)
       │                             │
       └──────────┬──────────────────┘
                  │
          LaurelDenoteBridge.lean
          (computable ↔ relational helpers)
                  │
          ┌───────┴───────┐
          ▼               ▼
  LaurelDenoteSound    LaurelDenoteComplete
  (denote → eval)      (eval → denote)
          │               │
          └───────┬───────┘
                  ▼
          LaurelDenoteEquiv.lean
          (iff + determinism corollaries)
```

## Limitations and Assumptions

### HeapInBound Precondition

The completeness direction (and therefore the `_iff` equivalence
theorems) requires `∀ hx, HeapInBound hx` — that every heap has a free
address within the search bound of 10000. This is universally quantified
over *all* heaps, not just the initial heap, because intermediate heaps
produced during evaluation must also satisfy the bound.

For any program that allocates fewer than 10000 objects, this condition
is trivially satisfied. Programs that exceed this bound have valid
relational derivations but the interpreter cannot reproduce them.

The soundness direction and the determinism corollaries do *not* require
this assumption.

### Scope of Equivalence

The equivalence is between the relational semantics and the denotational
interpreter. It does not cover:

- Equivalence with the existing `partial def eval` interpreter in
  `LaurelEval.lean` (which uses a different AST and value domain)
- Equivalence with the Strata Core semantics after translation
- Equivalence with any concrete language (Java, Python, JavaScript)
  that Laurel represents

### Metadata Independence

The soundness proof shows that `denoteStmt_sound` holds for *any*
metadata `md`. This means the relational semantics is parametric in
metadata — the evaluation result does not depend on source locations or
annotations. However, the denotational interpreter strips metadata
(it operates on `StmtExpr`, not `StmtExprMd`), so the soundness proof
must supply metadata when constructing the relational derivation.

### Inherited Limitations

Both directions of the proof inherit all limitations of the underlying
semantics: unsupported constructs (`LiteralDecimal`, `Abstract`, `All`,
`Hole`), partial `Assign` coverage, missing `DivT`/`ModT` operations,
no float support, and the restriction to terminating programs. The
equivalence says "the two semantics agree on what they can evaluate" —
it does not extend coverage to constructs that neither semantics handles.
