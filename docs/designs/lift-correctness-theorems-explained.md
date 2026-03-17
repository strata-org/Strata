# LiftImperativeExpressions Correctness — Theorems Explained

This document explains each theorem and definition in
`LiftImperativeExpressionsCorrectness.lean` in plain English,
relating the explanation to the variables in each theorem statement.

---

## Background

The `liftImperativeExpressions` pass transforms Laurel programs that
have assignments inside expressions (like `x + (x := 1;) + x`) into
equivalent programs where assignments are pulled out into preceding
statements with snapshot variables to preserve intermediate values.

The semantics evaluates `PrimitiveOp` arguments left-to-right, threading
the store through each argument (`EvalStmtArgs`). An assignment like
`x := e` updates the store and returns the assigned value.

---

## Phase 2: Single Assignment

### `lift_single_assign_correct`

```lean
theorem lift_single_assign_correct
    (δ : LaurelEval) (π : ProcEnv) (h : LaurelHeap) (σ : LaurelStore)
    (op : Operation) (x snap : Identifier)
    (e : StmtExprMd) (ty : HighTypeMd)
    (md tmd : Imperative.MetaData Core.Expression)
    (v_old v_new result : LaurelValue)
    (hx_def : σ x = some v_old)
    (hfresh : σ snap = none)
    (hne : snap ≠ x)
    (he_ext : ∀ σ', (∀ y, y ≠ snap → σ' y = σ y) →
      EvalLaurelStmt δ π h σ' e h σ' (.normal v_new))
    (hop : evalPrimOp op [v_old, v_new] = some result) :
    ∃ σ_block, EvalLaurelBlock δ π h σ
      [ ⟨.LocalVariable snap ty (some ⟨.Identifier x, md⟩), md⟩,
        ⟨.Assign [⟨.Identifier x, tmd⟩] e, md⟩,
        ⟨.PrimitiveOp op [⟨.Identifier snap, md⟩, ⟨.Identifier x, md⟩], md⟩ ]
      h σ_block (.normal result)
```

**In English:** Consider a binary operation like `op(x, x := e)` — reading
variable `x`, then assigning a new value to `x`. The lifting pass
transforms this into three statements:

```
var snap := x;          -- save x's old value
x := e;                 -- perform the assignment
op(snap, x)             -- compute using saved old value and new value
```

This theorem says: if you start in a store `σ` where `x` holds `v_old`
(`hx_def`), and you have a fresh variable name `snap` that doesn't exist
in the store (`hfresh`) and is different from `x` (`hne`), and the
expression `e` evaluates to `v_new` in any store that agrees with `σ`
on all variables except `snap` (`he_ext`), and the primitive operation
applied to `[v_old, v_new]` produces `result` (`hop`), then there exists
a final store `σ_block` such that executing the three-statement block
starting from heap `h` and store `σ` produces the value `result`.

The variables:
- `δ` — the expression evaluator (for pure sub-expressions)
- `π` — the procedure environment (for looking up function bodies)
- `h` — the heap (unchanged throughout, since the example is heap-free)
- `σ` — the initial variable store
- `op` — the binary operation (e.g., addition)
- `x` — the variable being assigned to
- `snap` — the fresh snapshot variable name (e.g., `$x_0`)
- `e` — the right-hand side of the assignment
- `ty` — the type annotation for the snapshot variable declaration
- `v_old` — the value of `x` before the assignment
- `v_new` — the value that `e` evaluates to (and that `x` gets assigned)
- `result` — the final value of `op(v_old, v_new)`

### `lift_single_assign_from_eval`

```lean
theorem lift_single_assign_from_eval
    (δ : LaurelEval) (π : ProcEnv) (h : LaurelHeap) (σ : LaurelStore)
    (op : Operation) (x snap : Identifier)
    (e : StmtExprMd) (ty : HighTypeMd)
    (md tmd : Imperative.MetaData Core.Expression)
    (h' : LaurelHeap) (σ' : LaurelStore) (result : LaurelValue)
    (v_new : LaurelValue)
    (heval : EvalLaurelStmt δ π h σ
      ⟨.PrimitiveOp op [⟨.Identifier x, md⟩,
                         ⟨.Assign [⟨.Identifier x, tmd⟩] e, md⟩], md⟩
      h' σ' (.normal result))
    (hfresh : σ snap = none)
    (hne : snap ≠ x)
    (he_pure : EvalLaurelStmt δ π h σ e h σ (.normal v_new))
    (he_ext : ∀ σ₀, (∀ y, y ≠ snap → σ₀ y = σ y) →
      EvalLaurelStmt δ π h σ₀ e h σ₀ (.normal v_new)) :
    ∃ σ_block, EvalLaurelBlock δ π h σ
      [ ⟨.LocalVariable snap ty (some ⟨.Identifier x, md⟩), md⟩,
        ⟨.Assign [⟨.Identifier x, tmd⟩] e, md⟩,
        ⟨.PrimitiveOp op [⟨.Identifier snap, md⟩, ⟨.Identifier x, md⟩], md⟩ ]
      h' σ_block (.normal result)
```

**In English:** This is the "from the original program" direction. Suppose
the *original* expression `op(x, x := e)` actually evaluates under the
extended semantics (with left-to-right store threading) to some `result`
in heap `h'` and store `σ'` (`heval`). Suppose also that `snap` is fresh
(`hfresh`, `hne`), and `e` evaluates purely to `v_new` (`he_pure`), and
`e` still evaluates to `v_new` in any store that differs from `σ` only
at `snap` (`he_ext`). Then the lifted three-statement block also evaluates
to `result`.

This theorem bridges from "the original program has a derivation" to
"the transformed program has a derivation with the same result." It works
by decomposing the original derivation (using `cases` on the `prim_op`
and `EvalStmtArgs` structure), using the determinism theorem to connect
the sub-derivation of `e` to the hypothesis `he_pure`, and then
delegating to `lift_single_assign_correct`.

The additional variables compared to the previous theorem:
- `h'` — the heap after evaluating the original expression
- `σ'` — the store after evaluating the original expression
- `heval` — the derivation that the original expression evaluates to `result`

---

## Phase 3: General PrimitiveOp with Multiple Assignments

### `ArgSpec` (definition)

```lean
inductive ArgSpec where
  | pure (ref : StmtExprMd) (val : LaurelValue)
  | assign (x snap : Identifier) (e : StmtExprMd) (ty : HighTypeMd) (val : LaurelValue)
```

**In English:** An `ArgSpec` describes one argument in a `PrimitiveOp` call.
It is either:
- `pure ref val` — a pure expression `ref` that evaluates to `val` without
  side effects (e.g., a variable read or literal), or
- `assign x snap e ty val` — an assignment `x := e` that evaluates to `val`,
  where `snap` is the fresh snapshot variable name and `ty` is its type.

### `ArgSpec.value`, `ArgSpec.cleanedArg`, `ArgSpec.prepends` (definitions)

- `value` extracts the runtime value from either kind of spec.
- `cleanedArg` produces the expression that appears in the cleaned-up
  `PrimitiveOp` after lifting. For a pure arg, it's the original expression.
  For an assignment to `x`, it's just `x` (reading the updated value).
- `prepends` produces the statements that get prepended for this argument.
  For a pure arg, nothing. For an assignment `x := e` with snapshot `snap`,
  it produces `[var snap := x; x := e;]`.

### `allPrepends`, `cleanedArgs`, `argValues` (definitions)

These collect the prepends, cleaned arguments, and values across an entire
list of `ArgSpec`s. Note that `allPrepends` concatenates in reverse order
(rest's prepends come first, then the current arg's prepends), matching
the right-to-left traversal of the pass — the rightmost argument's
prepends execute first.

### `applyArgEffect` (definition)

```lean
def applyArgEffect (σ : LaurelStore) : ArgSpec → LaurelStore
  | .pure _ _ => σ
  | .assign x snap _ _ val =>
    fun y => if y == x then some val
             else if y == snap then σ x
             else σ y
```

**In English:** Models the effect of one argument on the store. A pure
argument doesn't change the store. An assignment `x := e` with snapshot
`snap` and value `val` produces a new store where:
- `x` maps to `val` (the assigned value)
- `snap` maps to whatever `x` held before (the snapshot)
- everything else is unchanged

### `threadEffectsRL` (definition)

```lean
def threadEffectsRL (σ : LaurelStore) : List ArgSpec → LaurelStore
  | [] => σ
  | a :: as => applyArgEffect (threadEffectsRL σ as) a
```

**In English:** Applies the store effects of a list of argument specs
right-to-left. For `[a₁, a₂, a₃]`, it first applies `a₃`'s effect to
the initial store `σ`, then `a₂`'s effect to the result, then `a₁`'s
effect. This models the store state after all the prepended statements
have executed (since the rightmost argument's prepends execute first).

### `threadEffectsRL_preserves_none`

```lean
theorem threadEffectsRL_preserves_none
    {σ : LaurelStore} {name : Identifier}
    (hfresh : σ name = none)
    (hne : ∀ spec ∈ specs, match spec with
      | .assign x snap _ _ _ => name ≠ x ∧ name ≠ snap
      | .pure _ _ => True) :
    threadEffectsRL σ specs name = none
```

**In English:** If a variable `name` is not in the initial store `σ`
(`hfresh`), and `name` is different from every target variable `x` and
every snapshot variable `snap` in the spec list (`hne`), then `name` is
still not in the store after threading all effects. In other words,
threading effects doesn't conjure up bindings for unrelated variables.

### `assign_prepends_eval`

```lean
theorem assign_prepends_eval
    (δ : LaurelEval) (π : ProcEnv) (h : LaurelHeap) (σ : LaurelStore)
    (x snap : Identifier) (e : StmtExprMd) (ty : HighTypeMd)
    (md tmd : Imperative.MetaData Core.Expression)
    (v_old val : LaurelValue)
    (hx_def : σ x = some v_old)
    (hfresh : σ snap = none)
    (hne : snap ≠ x)
    (he_eval : ∀ σ₀, (∀ y, y ≠ snap → σ₀ y = σ y) →
      EvalLaurelStmt δ π h σ₀ e h σ₀ (.normal val)) :
    EvalLaurelBlock δ π h σ
      (ArgSpec.prepends md tmd (ArgSpec.assign x snap e ty val))
      h (applyArgEffect σ (ArgSpec.assign x snap e ty val)) (.normal val)
```

**In English:** The two prepended statements for a single assignment
argument actually evaluate correctly. Starting from store `σ` where `x`
holds `v_old` (`hx_def`) and `snap` is fresh (`hfresh`, `hne`), and
where `e` evaluates to `val` in any store that agrees with `σ` except
at `snap` (`he_eval`), executing:

```
var snap := x;    -- snapshot: snap gets v_old
x := e;           -- assignment: x gets val
```

produces the store `applyArgEffect σ (assign x snap e ty val)` — i.e.,
the store where `x = val`, `snap = v_old`, and everything else is
unchanged. The block's outcome is `.normal val` (the assigned value).

### `SpecsOK` (definition)

```lean
inductive SpecsOK :
    LaurelEval → ProcEnv → LaurelHeap → LaurelStore →
    Imperative.MetaData Core.Expression → Imperative.MetaData Core.Expression →
    List ArgSpec → Prop where
  | nil : SpecsOK δ π h σ md tmd []
  | cons_pure :
    SpecsOK δ π h σ md tmd rest →
    SpecsOK δ π h σ md tmd (ArgSpec.pure ref val :: rest)
  | cons_assign :
    SpecsOK δ π h σ md tmd rest →
    (σ snap = none) →
    (∀ spec ∈ rest, match spec with
      | .assign x' snap' _ _ _ => snap ≠ x' ∧ snap ≠ snap'
      | .pure _ _ => True) →
    (snap ≠ x) →
    ((threadEffectsRL σ rest x).isSome) →
    (∀ σ₀, (∀ y, y ≠ snap → σ₀ y = threadEffectsRL σ rest y) →
      EvalLaurelStmt δ π h σ₀ e h σ₀ (.normal val)) →
    SpecsOK δ π h σ md tmd (ArgSpec.assign x snap e ty val :: rest)
```

**In English:** An inductive predicate that says a list of argument specs
is "well-formed" for evaluation. It checks, for each assignment spec:
- The rest of the list is well-formed (`SpecsOK ... rest`)
- The snapshot variable `snap` doesn't exist in the initial store `σ`
- The snapshot variable doesn't collide with any target or snapshot in
  the rest of the list
- The snapshot is different from the target `x`
- The target `x` is defined in the store after threading the rest's effects
  (so the snapshot `var snap := x` can read it)
- The expression `e` evaluates to `val` in the store after threading the
  rest's effects (in any store that agrees except at `snap`)

For pure specs, only the rest needs to be well-formed.

### `allPrepends_eval`

```lean
theorem allPrepends_eval
    {δ : LaurelEval} {π : ProcEnv} {h : LaurelHeap} {σ : LaurelStore}
    {md tmd : Imperative.MetaData Core.Expression}
    {specs : List ArgSpec}
    (hok : SpecsOK δ π h σ md tmd specs) :
    ∃ v, EvalLaurelBlock δ π h σ
      (allPrepends md tmd specs)
      h (threadEffectsRL σ specs) (.normal v)
```

**In English:** If a spec list is well-formed (`hok : SpecsOK ...`), then
executing all the prepended statements (snapshots and assignments) starting
from store `σ` produces the store `threadEffectsRL σ specs`. In other
words, the prepended statements actually achieve the store state that
`threadEffectsRL` predicts.

The proof works by structural recursion on `hok`:
- Empty list: no prepends, store unchanged.
- Pure argument: no prepends for this arg, recurse on rest.
- Assignment argument: recursively evaluate the rest's prepends (which
  execute first), then evaluate this argument's prepends in the resulting
  store using `assign_prepends_eval`, and compose the two blocks using
  `EvalLaurelBlock_append`.

### `lift_multi_assign_correct`

```lean
theorem lift_multi_assign_correct
    {δ : LaurelEval} {π : ProcEnv} {h : LaurelHeap} {σ : LaurelStore}
    {op : Operation} {specs : List ArgSpec}
    {md tmd : Imperative.MetaData Core.Expression}
    {result : LaurelValue}
    (hok : SpecsOK δ π h σ md tmd specs)
    (hargs_eval : EvalStmtArgs δ π h (threadEffectsRL σ specs)
      (cleanedArgs md specs) h (threadEffectsRL σ specs) (argValues specs))
    (hop : evalPrimOp op (argValues specs) = some result) :
    ∃ σ_final, EvalLaurelBlock δ π h σ
      (allPrepends md tmd specs ++ [⟨.PrimitiveOp op (cleanedArgs md specs), md⟩])
      h σ_final (.normal result)
```

**In English:** This is the main Phase 3 theorem. Given:
- A well-formed spec list (`hok`)
- The cleaned arguments evaluate to the right values in the final store
  (`hargs_eval` — this says that after all prepends have executed, reading
  the snapshot variables and updated target variables produces the expected
  argument values)
- The primitive operation applied to those values produces `result` (`hop`)

Then there exists a final store `σ_final` such that executing:

```
[all prepended snapshots and assignments] ++ [op(cleaned_arg₁, ..., cleaned_argₙ)]
```

starting from heap `h` and store `σ` produces the value `result`.

This is the generalization of `lift_single_assign_correct` to any number
of arguments with any mix of pure expressions and assignments.

---

## Phase 4: Statement-Level Composition

### `stmt_to_block`

```lean
theorem stmt_to_block
    {δ : LaurelEval} {π : ProcEnv} {h : LaurelHeap} {σ : LaurelStore}
    {s : StmtExprMd} {h' : LaurelHeap} {σ' : LaurelStore} {o : Outcome}
    (heval : EvalLaurelStmt δ π h σ s h' σ' o) :
    EvalLaurelBlock δ π h σ [s] h' σ' o
```

**In English:** If a single statement `s` evaluates to outcome `o` (which
could be a normal value, an exit, or a return), then the singleton block
`[s]` also evaluates to outcome `o`. This is a trivial wrapper — it just
picks the right `EvalLaurelBlock` constructor based on the outcome type.

### `transformStmt_identity_correct`

```lean
theorem transformStmt_identity_correct
    {δ : LaurelEval} {π : ProcEnv} {h : LaurelHeap} {σ : LaurelStore}
    {s : StmtExprMd} {h' : LaurelHeap} {σ' : LaurelStore} {o : Outcome}
    (heval : EvalLaurelStmt δ π h σ s h' σ' o) :
    EvalLaurelBlock δ π h σ [s] h' σ' o
```

**In English:** For statements that the pass doesn't change (like `return`,
`exit`, `assert`, `assume`, literals), the transformed output is just
`[s]` — the original statement in a singleton block. This theorem says
that singleton block evaluates to the same result. It's just an alias
for `stmt_to_block`.

### `transformStmt_prepend_correct`

```lean
theorem transformStmt_prepend_correct
    {δ : LaurelEval} {π : ProcEnv}
    {h : LaurelHeap} {σ : LaurelStore}
    {prepends : List StmtExprMd} {s : StmtExprMd}
    {h₁ : LaurelHeap} {σ₁ : LaurelStore} {v₁ : LaurelValue}
    {h₂ : LaurelHeap} {σ₂ : LaurelStore} {o : Outcome}
    (hprep : EvalLaurelBlock δ π h σ prepends h₁ σ₁ (.normal v₁))
    (hstmt : EvalLaurelStmt δ π h₁ σ₁ s h₂ σ₂ o) :
    EvalLaurelBlock δ π h σ (prepends ++ [s]) h₂ σ₂ o
```

**In English:** This is the generic composition pattern used by the pass.
When the pass transforms a statement, it often produces
`prepends ++ [cleaned_statement]`. This theorem says: if the `prepends`
evaluate normally (reaching heap `h₁`, store `σ₁`, producing some value
`v₁` — `hprep`), and then the cleaned statement `s` evaluates in that
resulting state to heap `h₂`, store `σ₂`, outcome `o` (`hstmt`), then
the concatenated block `prepends ++ [s]` evaluates from the original
state `(h, σ)` to the final state `(h₂, σ₂)` with outcome `o`.

### `transformStmt_assign_correct`

```lean
abbrev transformStmt_assign_correct
    ...
    (hprep : EvalLaurelBlock δ π h σ prepends h₁ σ₁ (.normal v₁))
    (hassign : EvalLaurelStmt δ π h₁ σ₁ ⟨.Assign targets seqValue, md⟩ h₂ σ₂ o) :
    EvalLaurelBlock δ π h σ (prepends ++ [⟨.Assign targets seqValue, md⟩]) h₂ σ₂ o
```

**In English:** Specialization of `transformStmt_prepend_correct` for
assignments. If the prepends evaluate normally (`hprep`), and then
`x := seqValue` evaluates in the resulting state (`hassign`), then
`prepends ++ [x := seqValue]` evaluates correctly. This covers the case
where the pass lifts effectful sub-expressions out of an assignment's
right-hand side.

### `transformStmt_local_var_correct`

```lean
abbrev transformStmt_local_var_correct
    ...
    (hprep : EvalLaurelBlock δ π h σ prepends h₁ σ₁ (.normal v₁))
    (hlocal : EvalLaurelStmt δ π h₁ σ₁ ⟨.LocalVariable name ty (some seqInit), md⟩ h₂ σ₂ o) :
    EvalLaurelBlock δ π h σ
      (prepends ++ [⟨.LocalVariable name ty (some seqInit), md⟩]) h₂ σ₂ o
```

**In English:** Same pattern for local variable declarations with
initializers. If prepends evaluate normally and then
`var name : ty := seqInit` evaluates in the resulting state, the
concatenated block evaluates correctly.

### `transformStmt_ite_correct`

```lean
abbrev transformStmt_ite_correct
    ...
    (hprep : EvalLaurelBlock δ π h σ condPrepends h₁ σ₁ (.normal v₁))
    (hite : EvalLaurelStmt δ π h₁ σ₁ ⟨.IfThenElse seqCond seqThen seqElse, md⟩ h₂ σ₂ o) :
    EvalLaurelBlock δ π h σ
      (condPrepends ++ [⟨.IfThenElse seqCond seqThen seqElse, md⟩]) h₂ σ₂ o
```

**In English:** Same pattern for if-then-else. The pass may lift effectful
sub-expressions out of the condition, producing `condPrepends`. If those
prepends evaluate normally (reaching state `(h₁, σ₁)` — `hprep`), and
then the if-then-else with the cleaned condition evaluates in that state
(`hite`), the concatenated block evaluates correctly.

### `transformStmt_while_correct`

```lean
abbrev transformStmt_while_correct
    ...
    (hprep : EvalLaurelBlock δ π h σ condPrepends h₁ σ₁ (.normal v₁))
    (hwhile : EvalLaurelStmt δ π h₁ σ₁ ⟨.While seqCond invs dec seqBody, md⟩ h₂ σ₂ o) :
    EvalLaurelBlock δ π h σ
      (condPrepends ++ [⟨.While seqCond invs dec seqBody, md⟩]) h₂ σ₂ o
```

**In English:** Same pattern for while loops. The pass may lift effectful
sub-expressions out of the loop condition. If the condition prepends
evaluate normally, and then the while loop with the cleaned condition
evaluates in the resulting state, the concatenated block evaluates
correctly.

Note: the prepends execute only once (before the loop), while the cleaned
condition is re-evaluated on each iteration. This is correct because the
pass only lifts pure snapshot operations from the condition.

### `transformStmt_static_call_correct`

```lean
abbrev transformStmt_static_call_correct
    ...
    (hprep : EvalLaurelBlock δ π h σ prepends h₁ σ₁ (.normal v₁))
    (hcall : EvalLaurelStmt δ π h₁ σ₁ ⟨.StaticCall name seqArgs, md⟩ h₂ σ₂ o) :
    EvalLaurelBlock δ π h σ
      (prepends ++ [⟨.StaticCall name seqArgs, md⟩]) h₂ σ₂ o
```

**In English:** Same pattern for static procedure calls. If prepends
(from lifting effectful call arguments) evaluate normally, and then the
call with cleaned arguments evaluates in the resulting state, the
concatenated block evaluates correctly.

### `transformStmt_block_correct`

```lean
theorem transformStmt_block_correct
    {δ : LaurelEval} {π : ProcEnv}
    {h : LaurelHeap} {σ : LaurelStore}
    {stmts_flat : List StmtExprMd}
    {label : Option Identifier}
    {md : Imperative.MetaData Core.Expression}
    {h' : LaurelHeap} {σ' : LaurelStore} {o : Outcome}
    (hinner : EvalLaurelBlock δ π h σ stmts_flat h' σ' o)
    (hcatch : catchExit label o = o') :
    EvalLaurelBlock δ π h σ
      [⟨.Block stmts_flat label, md⟩] h' σ' o'
```

**In English:** For block statements `{ stmts... } label`, the pass
transforms each inner statement and flattens the results. This theorem
says: if the flattened inner statements `stmts_flat` evaluate to outcome
`o` (`hinner`), and applying `catchExit label` to `o` produces `o'`
(`hcatch`), then the singleton block `[{ stmts_flat } label]` evaluates
to `o'`. The `catchExit` handles the case where an inner `exit L`
matches the block's label `L`, converting it to a normal completion.

### `transformed_block_cons_normal`

```lean
theorem transformed_block_cons_normal
    ...
    {stmts₁ : List StmtExprMd} {stmts_rest : List StmtExprMd}
    {h₁ : LaurelHeap} {σ₁ : LaurelStore} {v₁ : LaurelValue}
    {h₂ : LaurelHeap} {σ₂ : LaurelStore} {o : Outcome}
    (hfirst : EvalLaurelBlock δ π h σ stmts₁ h₁ σ₁ (.normal v₁))
    (hne : stmts_rest ≠ [])
    (hrest : EvalLaurelBlock δ π h₁ σ₁ stmts_rest h₂ σ₂ o) :
    EvalLaurelBlock δ π h σ (stmts₁ ++ stmts_rest) h₂ σ₂ o
```

**In English:** If the first statement's transformation (`stmts₁`)
evaluates normally to value `v₁` in state `(h₁, σ₁)` (`hfirst`), and
the remaining transformed statements (`stmts_rest`, which must be
non-empty — `hne`) evaluate to outcome `o` in state `(h₂, σ₂)` (`hrest`),
then the concatenation `stmts₁ ++ stmts_rest` evaluates from `(h, σ)` to
`(h₂, σ₂)` with outcome `o`.

### `transformed_block_cons_exit`

```lean
theorem transformed_block_cons_exit
    ...
    {stmts₁ : List StmtExprMd} {stmts_rest : List StmtExprMd}
    {h' : LaurelHeap} {σ' : LaurelStore} {label : Identifier}
    (hfirst : EvalLaurelBlock δ π h σ stmts₁ h' σ' (.exit label)) :
    EvalLaurelBlock δ π h σ (stmts₁ ++ stmts_rest) h' σ' (.exit label)
```

**In English:** If the first statement's transformation (`stmts₁`)
evaluates to an exit with label `label` (`hfirst`), then the
concatenation `stmts₁ ++ stmts_rest` also evaluates to that exit,
regardless of what `stmts_rest` contains. The remaining statements are
skipped because exit is non-local control flow.

### `transformed_block_cons_return`

```lean
theorem transformed_block_cons_return
    ...
    {stmts₁ : List StmtExprMd} {stmts_rest : List StmtExprMd}
    {h' : LaurelHeap} {σ' : LaurelStore} {rv : Option LaurelValue}
    (hfirst : EvalLaurelBlock δ π h σ stmts₁ h' σ' (.ret rv)) :
    EvalLaurelBlock δ π h σ (stmts₁ ++ stmts_rest) h' σ' (.ret rv)
```

**In English:** Same as above but for return. If the first statement's
transformation evaluates to a return with value `rv` (`hfirst`), then
the concatenation also returns `rv`, skipping the rest.

### `TransformOK` (definition)

```lean
inductive TransformOK :
    LaurelEval → ProcEnv → LaurelHeap → LaurelStore →
    List StmtExprMd → List StmtExprMd →
    LaurelHeap → LaurelStore → Outcome → Prop where
  | nil :
    TransformOK δ π h σ [] [] h σ (.normal .vVoid)
  | last_normal :
    EvalLaurelStmt δ π h σ s h' σ' (.normal v) →
    EvalLaurelBlock δ π h σ stmts₁ h' σ' (.normal v) →
    TransformOK δ π h σ [s] stmts₁ h' σ' (.normal v)
  | last_exit : ...
  | last_return : ...
  | cons_normal :
    EvalLaurelStmt δ π h σ s h₁ σ₁ (.normal _v) →
    EvalLaurelBlock δ π h σ stmts₁ h₁ σ₁ (.normal _v') →
    rest ≠ [] → stmts_rest ≠ [] →
    TransformOK δ π h₁ σ₁ rest stmts_rest h₂ σ₂ o →
    TransformOK δ π h σ (s :: rest) (stmts₁ ++ stmts_rest) h₂ σ₂ o
  | cons_exit :
    EvalLaurelStmt δ π h σ s h' σ' (.exit label) →
    EvalLaurelBlock δ π h σ stmts₁ h' σ' (.exit label) →
    TransformOK δ π h σ (s :: _rest) (stmts₁ ++ _stmts_rest) h' σ' (.exit label)
  | cons_return : ...
```

**In English:** An inductive relation that witnesses the correctness of
transforming an entire block of statements. It relates a source block
`src` (the original statements) to a target block `tgt` (the transformed
statements), asserting they produce the same final heap `h'`, store `σ'`,
and outcome `o`.

The constructors cover all cases:
- `nil`: Both source and target are empty blocks, producing void.
- `last_normal/last_exit/last_return`: The source is a singleton `[s]`.
  The original statement `s` evaluates to some result, and the target
  block `stmts₁` evaluates to the same result.
- `cons_normal`: The first source statement `s` evaluates normally. Its
  transformation `stmts₁` also evaluates normally (possibly to a different
  intermediate value — the theorem only requires the final heap and store
  to agree). The remaining source statements `rest` and their
  transformation `stmts_rest` are related by a recursive `TransformOK`.
  The target is `stmts₁ ++ stmts_rest`.
- `cons_exit`: The first source statement exits. Its transformation also
  exits. The rest is irrelevant (skipped). Target is `stmts₁ ++ _`.
- `cons_return`: Same as exit but for return.

### `TransformOK_eval`

```lean
theorem TransformOK_eval
    {δ : LaurelEval} {π : ProcEnv}
    {h : LaurelHeap} {σ : LaurelStore}
    {src tgt : List StmtExprMd}
    {h' : LaurelHeap} {σ' : LaurelStore} {o : Outcome}
    (htok : TransformOK δ π h σ src tgt h' σ' o) :
    EvalLaurelBlock δ π h σ tgt h' σ' o
```

**In English:** If `TransformOK` holds — meaning we have a witness that
the source block `src` and target block `tgt` produce the same final
state and outcome — then the target block `tgt` actually evaluates to
that outcome. This extracts the concrete `EvalLaurelBlock` derivation
from the `TransformOK` witness.

The proof works by pattern matching on the `TransformOK` constructors:
- For `nil`, `last_*`: the target evaluation is directly available.
- For `cons_normal`: compose the first chunk's evaluation with the
  recursive result using `EvalLaurelBlock_append`.
- For `cons_exit`/`cons_return`: use `transformed_block_cons_exit` or
  `transformed_block_cons_return` to show the rest is skipped.
