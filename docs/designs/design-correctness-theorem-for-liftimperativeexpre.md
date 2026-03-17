# Design: Correctness Theorem for liftImperativeExpressions

**Date:** 2026-03-10
**Status:** Proposal

## 1. Problem Statement

The `liftImperativeExpressions` pass (`LiftImperativeExpressions.lean`)
transforms Laurel programs so that assignments and imperative calls no
longer appear in expression position. It does this by extracting effectful
sub-expressions into preceding statements, introducing snapshot variables
to preserve the values that the original expression would have observed.

This pass is a critical part of the Laurel → Core pipeline: Core's
expression language is pure, so all side effects must be sequenced into
statements before translation. If the pass changes program meaning, every
downstream verification result is unsound.

We need a machine-checked proof that the transformation preserves
semantics with respect to the big-step operational semantics defined in
`LaurelSemantics.lean`.

### Concrete example 1: Assignment in PrimitiveOp arguments

Source program:
```
var x: int := 0;
var y: int := x + (x := 1;) + x;
// Left-to-right evaluation: y = 0 + 1 + 1 = 2, final x = 1
```

After lifting:
```
var x: int := 0;
var $x_0: int := x;     // snapshot x = 0 before assignment
x := 1;                 // lifted assignment
var y: int := $x_0 + x + x;
// $x_0 = 0, x = 1, so y = 0 + 1 + 1 = 2, final x = 1
```

Both programs must produce `y = 2` and `x = 1`.

### Concrete example 2: Conditional in expression position

Source program:
```
var b: bool := true;
var z: bool := (if (b) { b := false; } else { b := true; }) || b;
```

After lifting:
```
var b: bool := true;
var $c_0: bool;
if (b) {
  b := false;
  $c_0 := b;
} else {
  b := true;
  $c_0 := b;
}
var z: bool := $c_0 || b;
```

### Concrete example 3: Statement-level assignment (identity case)

Source program:
```
x := expr;
```

After lifting (when `expr` is pure):
```
x := expr;    // unchanged
```

The pass should be the identity on programs without effectful expressions.

### Why this is hard

1. **Monadic implementation.** The pass uses `StateM LiftState`, threading
   fresh-name counters, a substitution map, and a prepend-statement stack.
   The proof must relate the monadic output to the semantic derivation.

2. **Right-to-left traversal.** `transformExpr` processes `PrimitiveOp`
   arguments right-to-left (via `args.reverse.mapM transformExpr` then
   `.reverse`), emitting snapshot declarations via `cons` (newest-first).
   The semantics evaluates arguments left-to-right via `EvalStmtArgs`.
   The proof must show these orderings are consistent.

3. **Freshness.** Generated names like `$x_0`, `$c_0` must not collide
   with program variables. The proof needs a freshness side condition.

4. **Substitution map invariant.** The map tracks which snapshot variable
   holds the value of each program variable at each point in the
   right-to-left traversal. The proof invariant must relate this map to
   the store state at the corresponding point in left-to-right evaluation.

## 2. Background

### 2.1 Operational semantics

The big-step semantics is defined in `LaurelSemantics.lean` as three
mutually inductive relations:

- `EvalLaurelStmt δ π h σ s h' σ' o` — evaluates a single statement/expression
- `EvalLaurelBlock δ π h σ ss h' σ' o` — evaluates a list of statements
- `EvalStmtArgs δ π h σ args h' σ' vals` — evaluates arguments left-to-right,
  threading heap and store, requiring each argument to produce `.normal v`

Key rules for the correctness proof:

- `prim_op`: evaluates arguments via `EvalStmtArgs`, then applies the
  primitive operation. This is the main rule where effectful arguments appear.
- `assign_single`: evaluates the RHS, then updates the store. Returns the
  assigned value (not void), modeling assignment-as-expression.
- `local_var_init`: evaluates the initializer, then adds the variable to
  the store. Returns `.normal .vVoid`.
- `block_sem`: evaluates a list of statements via `EvalLaurelBlock`, then
  applies `catchExit` for labeled blocks.
- `cons_normal`: evaluates the first statement, discards its value, then
  evaluates the rest. This is how prepended statements are sequenced.

### 2.2 The lifting pass

Defined in `LiftImperativeExpressions.lean`. Two mutually recursive
functions:

- `transformExpr (expr : StmtExprMd) : LiftM StmtExprMd` — processes an
  expression, lifting effectful sub-expressions to `prependedStmts` and
  replacing them with snapshot variable references.
- `transformStmt (stmt : StmtExprMd) : LiftM (List StmtExprMd)` — processes
  a statement, calling `transformExpr` on sub-expressions and prepending
  the accumulated statements.

The `LiftState` carries:
- `prependedStmts : List StmtExprMd` — accumulated statements (newest-first via cons)
- `varCounters : List (Identifier × Nat)` — per-variable fresh name counters
- `subst : SubstMap` — maps variable names to their current snapshot names
- `env : TypeEnv` — type environment for `computeType`
- `condCounter : Nat` — global counter for conditional result variables

Key invariant: after `transformExpr` returns, the result expression is
pure (no assignments), and `prependedStmts` contains the extracted
statements in reverse order. The caller (typically `transformStmt`)
retrieves them via `takePrepends` and prepends them to the output.

### 2.3 Existing properties

`LaurelSemanticsProps.lean` proves:
- `EvalLaurelStmt_deterministic` / `EvalLaurelBlock_deterministic` /
  `EvalStmtArgs_deterministic` — full determinism of the semantics
- `UpdateStore_deterministic`, `InitStore_deterministic`,
  `AllocHeap_deterministic`, `HeapFieldWrite_deterministic` — determinism
  of store and heap operations
- `UpdateStore_def_monotone`, `InitStore_def_monotone` — store operations
  preserve definedness of other variables
- `catchExit_normal`, `catchExit_return` — catchExit is identity on
  non-exit outcomes

### 2.4 Related work in Strata

The `Strata/Transform/` directory contains transformation correctness
proofs for Core-level passes:
- `DetToNondetCorrect.lean` — deterministic-to-nondeterministic
- `CallElimCorrect.lean` — procedure call elimination
- `LoopElimCorrect.lean` — loop elimination

These follow a common pattern: define a simulation relation between
source and target states, then prove that each evaluation step in the
source has a corresponding step in the target. However, those proofs
operate on Core's `EvalStmt`/`EvalBlock` which are simpler than Laurel's
(no unified StmtExpr, no effectful arguments).

## 3. Design Options

### Option A: Direct monadic extraction

**a. Implementation strategy**

Extract a pure specification from the monadic `transformExpr`/`transformStmt`
by running the `StateM` computation on a concrete initial state and
reasoning about the output. The correctness theorem directly relates the
monadic output to the semantic derivation.

The main theorem would be:

```lean
theorem transformStmt_correct
    (δ : LaurelEval) (π : ProcEnv) (h : LaurelHeap) (σ : LaurelStore)
    (s : StmtExprMd) (h' : LaurelHeap) (σ' : LaurelStore) (o : Outcome)
    (st : LiftState)
    (Heval : EvalLaurelStmt δ π h σ s h' σ' o)
    (Hfresh : FreshFor st s)
    (Henv : EnvConsistent st.env σ) :
    let (stmts, st') := transformStmt s |>.run st
    EvalLaurelBlock δ π h σ stmts h' σ' o
```

And for expressions:

```lean
theorem transformExpr_correct
    (δ : LaurelEval) (π : ProcEnv) (h : LaurelHeap) (σ : LaurelStore)
    (e : StmtExprMd) (h' : LaurelHeap) (σ' : LaurelStore) (v : LaurelValue)
    (st : LiftState)
    (Heval : EvalLaurelStmt δ π h σ e h' σ' (.normal v))
    (Hfresh : FreshFor st e)
    (Henv : EnvConsistent st.env σ)
    (Hsubst : SubstConsistent st.subst σ) :
    let (e', st') := transformExpr e |>.run st
    let prepends := st'.prependedStmts.reverse
    EvalLaurelBlock δ π h σ (prepends ++ [e']) h' σ' (.normal v)
```

**b. Internal representation**

Side conditions are predicates on `LiftState`:

- `FreshFor st s` — all names that `st` would generate (based on
  `varCounters` and `condCounter`) do not appear in `s` or in `σ`'s domain.
- `EnvConsistent st.env σ` — for every `(name, ty)` in `st.env`, if
  `σ name = some v` then `v` has type `ty`.
- `SubstConsistent st.subst σ` — for every `(x, x')` in `st.subst`,
  `σ x' = σ x` (the snapshot variable holds the same value as the
  original at the point where the substitution was created).

The substitution consistency invariant is the core of the proof. It
captures the fact that right-to-left traversal with snapshot creation
produces substitutions that, when evaluated left-to-right, yield the
same values.

**c. End-to-end correctness**

The program-level theorem composes the per-procedure results:

```lean
theorem liftImperativeExpressions_correct
    (prog : Program) (proc : Procedure)
    (Hmem : proc ∈ prog.staticProcedures)
    (Hfresh : ProgramFreshFor prog) :
    -- For any execution of the original procedure body...
    ∀ δ π h σ h' σ' o,
      EvalLaurelStmt δ π h σ (getBody proc).get h' σ' o →
      -- ...the transformed body produces the same result
      let prog' := liftImperativeExpressions prog
      let proc' := prog'.staticProcedures[indexOf proc]
      EvalLaurelStmt δ π h σ (getBody proc').get h' σ' o
```

The chain is: `transformExpr_correct` → `transformStmt_correct` →
`transformProcedureBody_correct` → `liftImperativeExpressions_correct`.

**d. Testing strategy**

- Unit tests: extend `LaurelSemanticsTest.lean` with examples that
  evaluate both source and transformed programs, checking they produce
  the same outcome. Cover: pure expressions (identity), single assignment
  in args, multiple assignments, conditional lifting, nested blocks.
- Property: for each test case, construct both the source derivation and
  the target derivation explicitly, verifying they agree.
- Limitation: the freshness condition is assumed, not checked dynamically.
  A separate test could verify that `liftImperativeExpressions` on
  concrete programs produces names that satisfy `FreshFor`.

**e. Complexity and risk**

- Files changed: 1 new file (`LiftImperativeExpressionsCorrect.lean`),
  plus additions to `LaurelSemanticsProps.lean` for helper lemmas.
- Risk: reasoning about `StateM` computations in Lean4 is verbose.
  Every `do`-notation step becomes a `bind`/`pure` that must be unfolded.
  The `modify`/`get` operations add layers of state threading.
- Risk: the mutual recursion in `transformExpr`/`transformStmt` mirrors
  the mutual recursion in `EvalLaurelStmt`/`EvalLaurelBlock`, requiring
  a mutual induction proof. Lean4's support for mutual structural
  induction on custom inductives can be fragile.
- Estimated difficulty: High. The monadic reasoning is the main bottleneck.

### Option B: Pure relational specification + refinement

**a. Implementation strategy**

Define a pure relational specification of what the lifting pass does,
independent of the monadic implementation. Then prove two things:
1. The monadic implementation refines the relational specification.
2. The relational specification preserves semantics.

The relational specification would be an inductive relation:

```lean
inductive LiftExprRel : StmtExprMd → List StmtExprMd → StmtExprMd → SubstMap → Prop where
  | pure :
    -- Expression has no effectful sub-expressions
    IsPure e →
    LiftExprRel e [] (applySubst subst e) subst
  | assign :
    -- Assignment: emit snapshot + assignment, return substituted name
    LiftExprRel
      ⟨.Assign [⟨.Identifier x, tmd⟩] val, md⟩
      [⟨.LocalVariable snap ty (some ⟨.Identifier x, md⟩), md⟩,
       ⟨.Assign [⟨.Identifier x, tmd⟩] val, md⟩]
      ⟨.Identifier (subst x), md⟩
      (subst[x ↦ snap])
  | prim_op :
    -- Process arguments right-to-left, accumulate prepends
    LiftArgsRel args prepends args' subst →
    LiftExprRel
      ⟨.PrimitiveOp op args, md⟩
      prepends
      ⟨.PrimitiveOp op args', md⟩
      subst
  -- ... more constructors
```

The correctness theorem is then:

```lean
theorem liftExprRel_correct
    (Hrel : LiftExprRel e prepends e' subst)
    (Heval : EvalLaurelStmt δ π h σ e h' σ' (.normal v))
    (Hfresh : FreshNames prepends σ)
    (Hsubst : SubstConsistent subst σ') :
    EvalLaurelBlock δ π h σ (prepends ++ [e']) h' σ' (.normal v)
```

And the refinement theorem:

```lean
theorem transformExpr_refines
    (st : LiftState) (e : StmtExprMd) :
    let (e', st') := transformExpr e |>.run st
    LiftExprRel e st'.prependedStmts.reverse e' st'.subst
```

**b. Internal representation**

Same side conditions as Option A (`FreshFor`, `SubstConsistent`), but
they are stated against the relational specification rather than the
monadic state. The relational specification makes the structure of the
transformation explicit:

- `LiftExprRel e prepends e' subst` — lifting expression `e` produces
  prepended statements `prepends`, cleaned expression `e'`, and
  substitution map `subst`.
- `LiftArgsRel args prepends args' subst` — lifting a list of arguments
  right-to-left.
- `LiftStmtRel s stmts` — lifting a statement produces a list of
  statements.

**c. End-to-end correctness**

Same as Option A, but the chain is:
`liftExprRel_correct` + `transformExpr_refines` → `transformStmt_correct`
→ `liftImperativeExpressions_correct`.

The separation means we can prove semantic preservation against the clean
relational spec, and separately verify that the monadic code implements
that spec. If the implementation changes (e.g., optimization), only the
refinement proof needs updating.

**d. Testing strategy**

Same as Option A, plus:
- Tests that the relational specification matches the monadic output on
  concrete examples (i.e., `LiftExprRel` holds for the actual output of
  `transformExpr`).
- The relational specification itself serves as documentation of the
  pass's intended behavior.

**e. Complexity and risk**

- Files changed: 1 new file for the relational spec
  (`LiftImperativeExpressionsSpec.lean`), 1 new file for the correctness
  proof (`LiftImperativeExpressionsCorrect.lean`), 1 new file for the
  refinement proof (`LiftImperativeExpressionsRefinement.lean`).
- Risk: the relational specification must faithfully capture the monadic
  implementation. If they diverge, the refinement proof fails, but this
  is caught at typecheck time.
- Risk: more total code, but each piece is simpler and more modular.
- Estimated difficulty: Medium-High. The semantic preservation proof is
  cleaner, but the refinement proof adds work.

### Option C: Phased bottom-up proof with deferred monadic reasoning

**a. Implementation strategy**

Prove correctness bottom-up, starting with the simplest cases and
building up. Defer the monadic extraction problem by initially proving
theorems about the *output* of the transformation (given as concrete
syntax) rather than about the transformation function itself.

Phase 1 — Pure expressions (no effectful sub-expressions):

```lean
theorem transformExpr_pure_identity
    (Hpure : IsPure e)
    (st : LiftState) :
    let (e', st') := transformExpr e |>.run st
    st'.prependedStmts = st.prependedStmts ∧ e'.val = applySubst st.subst e.val
```

This says: on pure expressions, `transformExpr` doesn't emit any new
prepends and just applies the current substitution. Semantic preservation
follows trivially since substitution of equal-valued variables preserves
evaluation.

Phase 2 — Single assignment in PrimitiveOp args:

Prove a lemma about the specific pattern `PrimitiveOp op [e₁, Assign [x] e₂]`
where `e₁` and `e₂` are pure. This is the simplest non-trivial case.
The proof shows that the prepended `[LocalVariable snap ty (some (Identifier x)), Assign [x] e₂]`
followed by `PrimitiveOp op [Identifier snap, Identifier x]` evaluates
to the same result.

Phase 3 — Multiple assignments:

Generalize Phase 2 to arbitrary argument lists with multiple assignments.
This requires the full substitution map invariant.

Phase 4 — Statement-level `transformStmt`:

Prove that `transformStmt` for `Assign`, `LocalVariable`, `IfThenElse`,
`While` preserves semantics, using the `transformExpr` results from
Phases 1–3.

Phase 5 (future) — Conditional and imperative call lifting.

**b. Internal representation**

Same side conditions as Options A and B. The key difference is that
each phase introduces only the invariants it needs:

- Phase 1: `IsPure e` (no assignments in sub-expressions)
- Phase 2: `SingleAssign e` (exactly one assignment, in a known position)
- Phase 3: Full `SubstConsistent` invariant
- Phase 4: Composition of expression-level results

This incremental approach means early phases can be completed and
checked before the full invariant is designed.

**c. End-to-end correctness**

The final theorem is the same as Options A and B. The difference is
that it is assembled from phase-specific lemmas rather than proved
monolithically. Each phase's lemma is independently useful:

- Phase 1 guarantees the pass is identity on pure programs (important
  for programs that don't use effectful expressions).
- Phase 2 gives confidence for the common single-assignment case.
- Phase 3 handles the general case.

**d. Testing strategy**

Each phase has its own test cases:
- Phase 1: Pure expressions (`LiteralInt`, `Identifier`, `PrimitiveOp`
  with pure args). Verify `transformExpr` output equals input (modulo
  metadata).
- Phase 2: `x + (x := 1;)` — the example from the semantics test file.
  Construct both source and target derivations.
- Phase 3: `x + (x := 1;) + x + (x := 2;)` — multiple assignments.
- Phase 4: `var y: int := x + (x := 1;);` — statement wrapping expression.

Limitation: Phases 1–2 don't cover the full generality. The proof is
only complete after Phase 3.

**e. Complexity and risk**

- Files changed: 1 new file (`LiftImperativeExpressionsCorrect.lean`),
  possibly split into `*Phase1.lean`, `*Phase2.lean` etc. if size warrants.
  Helper lemmas in `LaurelSemanticsProps.lean`.
- Risk: the phased approach may require refactoring earlier phases when
  later phases reveal the need for stronger invariants. However, this is
  mitigated by the bottom-up design — each phase is a strict generalization
  of the previous one.
- Risk: without the relational specification (Option B), the monadic
  reasoning is still present, but it's tackled incrementally on simpler
  cases first.
- Estimated difficulty: Medium. Each phase is tractable. The total work
  is comparable to Option A, but spread across independently verifiable
  milestones.

## 4. Recommendation

**Option C: Phased bottom-up proof with deferred monadic reasoning.**

Rationale:

1. **Incremental progress.** Each phase produces a checked theorem that
   provides value independently. Phase 1 (pure identity) is useful even
   without the full correctness proof — it guarantees the pass doesn't
   break programs that don't use effectful expressions. This aligns with
   the project's task structure (tasks 008–011).

2. **Risk management.** The hardest part of this proof is the interaction
   between the monadic state (substitution map, prepend stack) and the
   semantic derivation. By starting with pure expressions (where the
   monadic state is trivial), we build understanding of the proof
   structure before tackling the complex cases.

3. **Avoids premature abstraction.** Option B's relational specification
   is elegant but requires designing the full specification upfront. If
   the specification doesn't match the implementation in subtle ways
   (e.g., the exact order of prepended statements, or how the substitution
   map is reset between statements), the refinement proof becomes the
   bottleneck. Option C discovers these subtleties incrementally.

4. **Practical tractability.** The existing determinism proof in
   `LaurelSemanticsProps.lean` already required `maxHeartbeats 800000`
   for the mutual induction. Adding a correctness proof with the same
   mutual structure will be resource-intensive. Phasing lets us keep
   each file's resource usage manageable.

5. **Option B elements can be adopted later.** If Phase 3 reveals that
   a relational specification would simplify the general case, we can
   introduce it at that point with the benefit of hindsight from Phases
   1–2. The phased approach is compatible with later refactoring into a
   cleaner structure.

### Proof plan

The proof file `LiftImperativeExpressionsCorrect.lean` will contain:

**Definitions:**
- `IsPure : StmtExprMd → Prop` — no `Assign`, no imperative `StaticCall`
  in sub-expressions (mirrors `containsAssignmentOrImperativeCall`).
- `FreshFor : LiftState → StmtExprMd → LaurelStore → Prop` — generated
  names don't collide with program variables or store domain.
- `SubstConsistent : SubstMap → LaurelStore → Prop` — for each mapping
  `(x, x')`, `σ x' = σ x`.

**Phase 1 lemmas (task 008):**
- `transformExpr_pure_no_prepends` — pure expressions don't emit prepends.
- `transformExpr_pure_subst` — pure expressions just apply substitution.
- `subst_consistent_eval` — evaluating a substituted pure expression
  under a consistent substitution yields the same value.
- `transformStmt_pure_identity` — pure statements are unchanged.

**Phase 2 lemmas (task 009):**
- `single_assign_prepends` — characterize the prepended statements for
  a single assignment in argument position.
- `snapshot_preserves_value` — the snapshot variable holds the original
  value after the assignment executes.
- `transformExpr_single_assign_correct` — the prepends + cleaned
  expression evaluate to the same result as the original.

**Phase 3 lemmas (task 010):**
- `SubstConsistent_after_assign` — updating the substitution map after
  an assignment preserves consistency (with the extended store).
- `transformExpr_args_correct` — right-to-left traversal with
  left-to-right evaluation produces the same values.
- `transformExpr_correct` — general expression-level correctness.

**Phase 4 lemmas (task 011):**
- `transformStmt_assign_correct` — `Assign` statement correctness.
- `transformStmt_local_var_correct` — `LocalVariable` correctness.
- `transformStmt_ite_correct` — `IfThenElse` correctness.
- `transformStmt_while_correct` — `While` correctness.
- `transformStmt_correct` — general statement-level correctness.

**Helper lemmas (in `LaurelSemanticsProps.lean`):**
- `EvalLaurelBlock_append` — evaluating `ss₁ ++ ss₂` can be split into
  evaluating `ss₁` then `ss₂` (when `ss₁` produces `.normal`).
- `EvalLaurelBlock_singleton` — `EvalLaurelBlock δ π h σ [s] h' σ' o ↔
  EvalLaurelStmt δ π h σ s h' σ' o` (for non-void outcomes, already
  partially captured by `last_normal`).
- `InitStore_preserves_other` — initializing a fresh variable doesn't
  change the values of existing variables.
- `store_agree_on_pure` — if two stores agree on all free variables of
  a pure expression, they produce the same evaluation result.
