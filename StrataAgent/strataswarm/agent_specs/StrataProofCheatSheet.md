# Strata Proof Cheat Sheet

## Project Context

Strata is a verified program transformation framework. Transformations operate on
Imperative programs (which may include nondeterministic operations) and produce
Imperative programs. Some transforms target specialized sublanguages (e.g.,
`DetToKleene` produces Kleene algebra programs), but the framework is generic.

Transforms include: `DetToKleene`, `CallElim`, `ANFEncoder`, `ProcedureInlining`,
`FilterProcedures`, `PrecondElim`, `LoopElim`, `ProcBodyVerify`, and others.

The main verification goal is **overapproximation** — every terminal/exiting/failing
behavior of the source program is also a behavior of the target program. Assertion
validity preservation follows from overapproximation via metatheory already proved
in the codebase (`overapproximates_triple`, `sound_assertValid`).

The proofs draw on CompCert's simulation technique and are structured around:
- Forward simulation (terminal states, exiting states, failure states)
- Mutual recursion on `Stmt`/`Block` (7 constructors for Stmt, recursive Block)
- Reflexive-transitive closure of step relations (`StepStmtStar`, `StepKleeneStar`)

---

## Table of Contents

1. [Key Types and Definitions](#key-types-and-definitions)
2. [The Specification Framework](#the-specification-framework)
3. [Common Proof Patterns](#common-proof-patterns)
4. [Transform Correctness Proofs](#transform-correctness-proofs)
5. [Semantic Correctness Proofs](#semantic-correctness-proofs)
6. [Advanced Techniques](#advanced-techniques)
7. [Finding Helper Lemmas](#finding-helper-lemmas)
8. [Proof Methodology](#proof-methodology)
9. [Anti-patterns](#anti-patterns)
10. [External References](#external-references)

---

## Key Types and Definitions

### Statement Types

| Type | Description | File |
|------|-------------|------|
| `Stmt P (Cmd P)` | Imperative statements (cmd, block, ite, loop, exit, funcDecl, typeDecl) | `DL/Imperative/Stmt.lean` |
| `KleeneStmt P (Cmd P)` | Kleene statements (cmd, seq, choice, loop, assert, block) | `DL/Imperative/KleeneStmt.lean` |
| `Block P CmdT` | `List (Stmt P CmdT)` — a block body | `DL/Imperative/Stmt.lean` |

### Configurations

| Type | Constructors | Description |
|------|--------------|-------------|
| `Config P CmdT` | `.stmt`, `.stmts`, `.terminal`, `.exiting`, `.block`, `.seq` | Det execution states |
| `KleeneConfig P CmdT` | `.stmt`, `.terminal`, `.block`, `.seq` | Kleene execution states |

### Step Relations

| Relation | Definition | Description |
|----------|------------|-------------|
| `StepStmt P EvalCmd extendEval` | inductive in `StmtSemantics.lean` | Single deterministic step |
| `StepStmtStar P EvalCmd extendEval` | `ReflTrans (StepStmt ...)` | Multi-step det execution |
| `StepKleene P EvalCmd` | inductive in `KleeneStmtSemantics.lean` | Single Kleene step |
| `StepKleeneStar P EvalCmd` | `ReflTrans (StepKleene ...)` | Multi-step Kleene execution |

### Translation Functions

Transforms are typically `Option`-valued functions: `Stmt → Option TargetStmt`.
Returning `none` signals that the input contains unsupported constructs.
Read the specific transform's definition in `Strata/Transform/` to understand
what it produces — each transform has its own file.

### Reflexive-Transitive Closure

```lean
inductive ReflTrans {A : Type} (r : Relation A) : Relation A where
  | refl : ∀ x, ReflTrans r x x
  | step : ∀ x y z, r x y → ReflTrans r y z → ReflTrans r x z
```

The `ReflTransT` variant lives in `Type` (not `Prop`), enabling:
- Pattern matching to produce data (step counts)
- `ReflTransT.len` for termination arguments
- Structural recursion keyed on trace length

### Environment

```lean
structure Env (P : PureExpr) where
  store : SemanticStore P        -- P.Ident → Option P.Expr
  eval  : SemanticEval P         -- SemanticStore P → P.Expr → Option P.Expr
  hasFailure : Bool := false
```

### Command Evaluation (`EvalCmd`)

Key constructors:
- `eval_init` — requires `σ x = none` (InitState), sets `σ' x = some v`
- `eval_set` — requires `σ x = some _` (UpdateState), sets `σ' x = some v`
- `eval_assert_pass` — expr = tt, `hasFailure = false`
- `eval_assert_fail` — expr = ff, `hasFailure = true`
- `eval_assume` — expr must be tt (otherwise stuck/no step), `hasFailure = false`
- `eval_cover` — skip (no-op)

---

## The Specification Framework

### Lang Bundle

```lean
structure Lang (P : PureExpr) where
  StmtT : Type                                 -- Statement type
  CfgT : Type                                  -- Configuration type
  star : CfgT → CfgT → Prop                   -- Multi-step relation
  stmtCfg : StmtT → Env P → CfgT              -- Initial config
  terminalCfg : Env P → CfgT                   -- Terminal config
  exitingCfg : String → Env P → CfgT           -- Exiting config
  isAtAssert : CfgT → AssertId P → Prop        -- Assert detection
  getEnv : CfgT → Env P                        -- Extract env
  initEnvWF : List String → StmtT → Env P → Prop  -- Initial WF
```

### Three Levels of Correctness

1. **`Sound`** — directly: if target's asserts valid → source's asserts valid
2. **`Overapproximates`** — simulation: source behaviors ⊆ target behaviors
3. **`OverapproximatesAggressively`** — simulation with spurious failure allowed

The hierarchy: `Overapproximates` → `OverapproximatesAggressively` → `Sound`

### Overapproximation (Full Definition)

```lean
def Overapproximates (L₁ L₂ : Lang P) (T : L₁.StmtT → Option L₂.StmtT)
    (newPrefix : String) : Prop :=
  ∀ (prefixIdents : List String) (st : L₁.StmtT) (st' : L₂.StmtT),
    T st = some st' →
    newPrefix ∈ prefixIdents →
    PrefixDisjoint newPrefix (prefixIdents.erase newPrefix) →
    ∀ (ρ₀ : Env P), L₁.initEnvWF prefixIdents st ρ₀ →
      -- (1) Terminal/exiting trace preservation
      (∀ ρ', (L₁.star (L₁.stmtCfg st ρ₀) (L₁.terminalCfg ρ') →
               L₂.star (L₂.stmtCfg st' ρ₀) (L₂.terminalCfg ρ'))
             ∧ (∀ lbl, L₁.star ... → L₂.star ...))
      -- (2) Failure preservation
      ∧ (CanFail L₁ st ρ₀ → CanFail L₂ st' ρ₀)
      -- (3) Output WF (with consumed prefix)
      ∧ L₂.initEnvWF (prefixIdents.erase newPrefix) st' ρ₀
```

### Assertion Validity

```lean
def AssertValid (s : L.StmtT) (a : AssertId P) : Prop :=
  ∀ (ρ₀ : Env P) (cfg : L.CfgT),
    L.star (L.stmtCfg s ρ₀) cfg →
    L.isAtAssert cfg a →
    (L.getEnv cfg).eval (L.getEnv cfg).store a.expr = some HasBool.tt
```

The metatheory connects overapproximation to assertion validity:
- `overapproximates_triple` — overapproximation preserves Hoare triples
- `sound_assertValid` — soundness implies assertion validity

---

## Common Proof Patterns

### 1. Case Analysis on Stmt Constructors

Most simulation proofs require matching all 7 constructors:
```lean
cases st with
| cmd c => ...
| block label ss md => ...
| ite cond tss ess md => ...
| loop guard measure inv body md => ...
| exit label md => ...       -- often contradiction if transform rejects exits
| funcDecl decl md => ...    -- often contradiction if transform rejects funcDecl
| typeDecl tc md => ...      -- often contradiction if transform rejects typeDecl
```
For cases where the translation returns `none`, `simp [TranslationFn] at hT`
closes the goal by contradiction.

### 2. Mutual Induction on Stmt/Block

`Stmt` is a nested inductive (contains `Block = List (Stmt ...)`).
Lean's `induction` tactic does NOT work on nested inductives — use mutual theorems:

```lean
private theorem sim_stmt : ∀ s ..., P s := by
  intro s; cases s with
  | cmd c => ...
  | block _ ss _ => exact sim_block ss ...
  | ...

private theorem sim_block : ∀ ss ..., Q ss := by
  intro ss; match ss with
  | [] => ...
  | s :: ss => exact ⟨sim_stmt s ..., sim_block ss ...⟩
```

### 3. Chaining Multi-step Executions (ReflTrans Transitivity)

The bread and butter of simulation proofs:
```lean
-- Chain: cfg₁ →* cfg₂ →* cfg₃
exact ReflTrans_Transitive _ _ _ _
  (step_sequence_1)
  (step_sequence_2)

-- Single step followed by refl:
exact .step _ _ _ (constructor_name args) (.refl _)

-- Single step followed by more:
exact .step _ _ _ (constructor_name args)
  (ReflTrans_Transitive _ _ _ _ more_steps final_steps)
```

### 4. Inverting Multi-step Executions

Decompose `.stmts (s :: ss) ρ₀ →* .terminal ρ'`:
```lean
-- Step 1: .stmts (s :: ss) ρ₀ → .seq (.stmt s ρ₀) ss
-- Step 2: Use seq_reaches_terminal to split
have ⟨ρ₁, hterm, htail⟩ := seq_reaches_terminal P (EvalCmd P) extendEval hrest
-- hterm : .stmt s ρ₀ →* .terminal ρ₁
-- htail : .stmts ss ρ₁ →* .terminal ρ'
```

Similarly for exiting:
```lean
have ⟨ρ₁, hexit, htail⟩ := seq_reaches_exiting P (EvalCmd P) extendEval lbl hrest
```

### 5. Proving Impossible Steps (Terminal Configs Cannot Step)

Terminal configurations don't step — use this to invert traces:
```lean
-- Pattern: a trace from .terminal must be .refl
cases hrest with
| refl => ...
| step _ _ _ hstep _ => exact absurd hstep (by intro h; cases h)
```

### 6. Translation Success Implies Properties

When a translation function returns `some`, it often implicitly guarantees
structural properties of the input (e.g., a transform that returns `none` for
unsupported constructs means success implies their absence). These facts are
proved by structural recursion on the translation definition and can be used
to discharge impossible cases in the simulation proof.

### 7. WellFormed Preservation Across Steps

Key WellFormed predicates and their preservation:
```lean
-- Preserved under execution (when no funcDecl modifies eval):
star_preserves_wfBool   -- WellFormedSemanticEvalBool
star_preserves_wfVal    -- WellFormedSemanticEvalVal
star_preserves_wfVar    -- WellFormedSemanticEvalVar

-- The workhorse for arbitrary step sequences:
smallStep_noFuncDecl_preserves_eval  -- no funcDecl → eval unchanged
```

### 8. hasFailure Monotonicity

The `hasFailure` flag is monotone: once set, stays set:
```lean
StepStmtStar_hasFailure_monotone
-- ρ₀.hasFailure = true → ρ'.hasFailure = true (for any ρ' reachable)
```

Proof pattern for CanFail:
```lean
-- Case split on ρ₀.hasFailure
cases h_fail : ρ₀.hasFailure with
| true => -- Trivial: initial state already failing
| false => -- Find the step that causes failure (e.g., assert_fail)
```

### 9. Store/Eval Independence from hasFailure

```lean
EvalStmtSmall_hasFailure_irrel
-- Terminal store and eval are the same regardless of initial hasFailure value
smallStep_hasFailure_irrel
-- Same but for arbitrary multi-step
```

---

## Transform Correctness Proofs

### Structure of a Transform Correctness Proof

A typical overapproximation proof has this structure:

```lean
theorem myTransform_overapproximates :
    Specification.Overapproximates L₁ L₂ myTransform "prefix" := by
  intro prefixIdents st st' hT hMem hPD ρ₀ hWF
  -- hT : myTransform st = some st'
  -- Goal: trace preservation ∧ CanFail preservation ∧ WF preservation
  refine ⟨?_, ?_, ?_⟩
  -- Subgoal 1: ∀ ρ', (terminal preservation) ∧ (exiting preservation)
  · intro ρ'
    constructor
    · intro hstar  -- source reaches terminal
      -- Simulate: build target trace reaching same terminal
      ...
    · intro lbl hstar  -- source reaches exiting
      ...
  -- Subgoal 2: CanFail preservation
  · intro ⟨ρ', hstar, hfail⟩
    ...
  -- Subgoal 3: WF preservation
  · ...
```

### The Embedding Pattern

When proving that a sub-trace can be embedded into a larger context
(e.g., showing a body trace lifts through surrounding block/seq wrappers):
```lean
-- Key insight: build the full trace layer by layer, inside-out
-- Use the lifting lemmas (block_inner_star, seq_inner_star) to push
-- an inner trace through each enclosing wrapper, then use the
-- "done" steps (step_block_done, step_seq_done) to complete.
exact ReflTrans_Transitive _ _ _ _
  (enter_outer_wrapper ...)
  (lift_inner_star ...
    (ReflTrans_Transitive _ _ _ _
      (execute_prefix ...)
      (lift_through_next_wrapper ...
        (actual_inner_trace))))
```

### Compositional Soundness

Compose two sound transforms:
```lean
sound_comp
-- If T₁ is sound and T₂ is sound, then T₂ ∘ T₁ is sound

-- Lift statement-level to list-level:
overapproximates_stmts
-- If f overapproximates per-statement, then mapM f overapproximates for lists
```

---

## Semantic Correctness Proofs

### Proving Command-Level Properties

For single commands, invert `EvalCmd`:
```lean
-- Pattern: prove property after single command execution
intro heval
cases heval with
| eval_init h_none h_val => ...
| eval_set h_some h_val => ...
| eval_assert_pass h_tt => ...
| eval_assert_fail h_ff => ...
| eval_assume h_tt h_wf => ...
```

### Proving Store Preservation

Many commands preserve the store (asserts, assumes, covers):
```lean
theorem eval_assert_store_cst :
    EvalCmd P δ σ (.assert l e md) σ' f → σ = σ' := by
  intros Heval; cases Heval with
  | eval_assert_pass _ => rfl
  | eval_assert_fail _ => rfl
```

### Proving Eval Preservation

```lean
-- If no funcDecl executes, the evaluator is unchanged:
smallStep_noFuncDecl_preserves_eval
-- Stronger: WF properties preserved under multi-step:
star_preserves_wfBool / star_preserves_wfVal / star_preserves_wfVar
```

### Determinism of Store After Execution

```lean
-- Key property: given same initial env, if execution terminates,
-- the terminal store depends only on the program and initial store
-- (not on hasFailure)
EvalStmtSmall_hasFailure_irrel
```

---

## Advanced Techniques

### Loop Simulation via Well-Founded Induction on Trace Length

Loops require induction on the length of the source execution trace:

```lean
-- Step 1: Convert Prop trace to Type trace (for structural recursion)
have hstarT := reflTrans_to_T hstar

-- Step 2: Induct on trace length
induction hstarT with
| refl => ...  -- loop never entered (immediate exit)
| step cfg mid final hstep hrest ih =>
  -- hstep : single step (either loop_enter or loop_exit)
  cases hstep with
  | step_loop_enter hcond => ...  -- guard true → body executes → recurse
  | step_loop_exit hcond => ...   -- guard false → terminate
```

Alternative: use `termination_by` with `ReflTransT.len`:
```lean
theorem loop_sim (hstarT : ReflTransT (StepStmt ...) cfg terminal) : ... := by
  ...
  exact loop_sim (smaller_trace)
termination_by hstarT.len
```

### Config Accessor Simplification

Use `simp` with config accessors to normalize goals involving environment extraction:
```lean
simp [Config.getEnv, Config.getEval, Config.getStore]
```

### isAtAssert Propagation Through Wrappers

Assert detection is defined recursively through config wrappers:
```lean
-- isAtAssert is transparent through .block and .seq wrappers:
-- i.e., isAtAssert (.block lbl σ inner) a ↔ isAtAssert inner a
-- This is used to show wrapped configs preserve assert detection
simp only [coreIsAtAssert]  -- unfolds through all wrapper layers
```

### Dealing with Option-valued Translations

When the translation function `T` returns `Option` and you have `hT : T st = some st'`:
```lean
-- Unfold the translation to expose its structure:
simp [myTranslation] at hT
-- For monadic (do-notation) translations, split the Option.bind:
obtain ⟨intermediate, h1, h2⟩ := Option.bind_eq_some.mp hT
-- For case-producing translations, use match/split:
split at hT
· simp at hT  -- impossible case (returns none) → contradiction
· simp at hT; obtain ⟨...⟩ := hT  -- possible case
```

### Prefix Freshness and PrefixDisjoint

Transforms introduce fresh variables with a designated prefix. Prove freshness:
```lean
-- PrefixDisjoint is typically vacuous or follows from the precondition:
have hpd : PrefixDisjoint newPrefix ([newPrefix].erase newPrefix) := by
  intro p hp; simp [List.erase_cons_head] at hp
```

### Induction on ReflTrans Derivations

```lean
-- Pattern: induct on the multi-step derivation
induction hstar with
| refl =>
  -- Base: no steps taken, cfg = initial config
  ...
| step cfg₁ cfg₂ cfg₃ hstep hrest ih =>
  -- hstep : single step cfg₁ → cfg₂
  -- hrest : multi-step cfg₂ →* cfg₃
  -- ih : property holds for cfg₂ →* cfg₃
  cases hstep with
  | step_cmd heval => ...
  | step_ite_true hcond => ...
  | ...
```

### Lifting Inner Traces Through Wrappers

When a sub-configuration executes inside a wrapper (block, seq), you need
lifting lemmas to propagate the inner trace to the outer config. Look for
lemmas named `*_inner_star` (lift multi-step) and `*_terminal` (complete
from inner terminal to outer terminal) in the relevant `SemanticsProps` file.

```lean
-- General pattern:
-- 1. Lift inner steps: inner →* inner'  ⟹  wrapper(inner) →* wrapper(inner')
-- 2. Complete wrapper: wrapper(terminal ρ') → terminal (project ρ')
-- Chain them with ReflTrans_Transitive
```

### CanFail Proofs

```lean
-- CanFail L s ρ₀ means: ∃ ρ', L.star (L.stmtCfg s ρ₀) (L.terminalCfg ρ') ∧ ρ'.hasFailure = true

-- To prove CanFail for the target:
exact ⟨ρ', target_trace, failure_flag⟩

-- Common strategy: reuse the source trace, simulate it in target
```

### Store Projection in Block Exit

When a block terminates, the store is projected (local vars removed):
```lean
-- block_done produces:
-- .terminal { ρ' with store := projectStore σ_parent ρ'.store }
-- where projectStore keeps only variables that existed at block entry
```

---

## Finding Helper Lemmas

### Where to Look

| What you need | Where to find it |
|---------------|-----------------|
| ReflTrans properties (transitivity, conversion) | `Strata/DL/Util/Relations.lean` |
| Imperative step-relation helpers (lifting, inversion) | `Strata/DL/Imperative/SemanticsProps.lean` |
| Kleene step-relation helpers | `Strata/DL/Imperative/KleeneSemanticsProps.lean` |
| Command-level properties (store/eval preservation) | `Strata/DL/Imperative/CmdSemantics.lean` |
| Specification metatheory (soundness composition) | `Strata/Transform/Specification.lean` |
| WellFormed predicates | `Strata/DL/Imperative/CmdSemantics.lean`, `StmtSemantics.lean` |

### How to Discover Lemmas

1. **Read the relevant `*Props.lean` file** — these contain pre-proved helpers
2. **Use `exact?` / `apply?`** — Lean's tactic search finds applicable lemmas
3. **Use `#check` with partial names** — e.g., `#check seq_reaches` to find inversion lemmas
4. **Search for patterns** — lifting lemmas are named `*_inner_star`,
   inversion lemmas are named `*_reaches_terminal` / `*_reaches_exiting`,
   completion lemmas are named `*_terminal`

### Key Utility Lemmas (always needed)

These are from `Relations.lean` and used in virtually every simulation proof:

| Lemma | Usage |
|-------|-------|
| `ReflTrans_Transitive` | Chain traces: `ReflTrans_Transitive _ _ _ _ h1 h2` |
| `ReflTrans.refl` | Zero-step trace: `.refl _` |
| `ReflTrans.step` | Single step + rest: `.step _ _ _ hstep hrest` |
| `reflTrans_to_T` | Convert Prop trace to Type (for structural recursion) |
| `ReflTransT.len` | Step count (for `termination_by`) |

### What Kinds of Helpers Exist

The semantics helper files typically provide:

- **Lifting lemmas** — propagate inner multi-step through wrappers (seq, block)
- **Inversion lemmas** — decompose a trace reaching terminal/exiting into sub-traces
- **Monotonicity lemmas** — `hasFailure` is monotone, WF predicates preserved
- **Store/eval constancy** — certain commands don't modify store or eval
- **Composition lemmas** — combine sub-proofs into a full overapproximation proof

---

## Proof Methodology

### The Three-Step Process

1. **Write informal hierarchical proof** (as Lean comments)
2. **Create Lean template with sorry's** for key intermediate results
3. **Fill in the sorry's** to complete the formal proof

### The Four-Step Process (for complex intermediate results)

1. **Write informal proof** — identify which steps need induction
2. **Create initial template** — mark where separate lemmas are needed
3. **Add separate lemmas** — create lemmas for facts requiring induction
4. **Fill in all sorry's** — complete helper lemmas and main theorem

### When to Extract Separate Lemmas

| Use `have` when... | Use separate lemma when... |
|-------------------|---------------------------|
| Follows by definition | Requires induction |
| Simple rewrite | Complex case analysis |
| Direct application of existing lemma | Reusable across multiple proofs |
| One-line proof | Well-founded recursion needed |
| Only used once in this proof | General fact worth naming |

### Proof Decomposition for Transforms

A transform correctness proof typically decomposes into:

1. **Translation structure lemma** — show what the translation produces
   (e.g., `procToVerifyStmt_structure`)
2. **Embedding helper** — show source traces embed into target contexts
3. **Property preservation** — show properties (isAtAssert, getEnv) transfer
4. **Main theorem** — compose the above

### Using `plausible` for Early Validation (Limited)

`plausible` often won't work on Strata types (they lack `Repr`/`Shrinkable`
instances), but when it does work it can catch false assertions early:
```lean
-- Try plausible — if it finds a counterexample, your assertion is WRONG:
have h : some_property := by plausible
-- Fall back to sorry when plausible times out or isn't applicable (common)
```

### Structured Proof Template

```lean
/-
Theorem: [English statement]

Proof:
  1. [First major step]
     by [justification]
  2. [Second major step]
     2.1. [Substep]
     2.2. [Substep]
  3. done
     by 1 and 2
-/
theorem name : statement := by
  -- Step 1
  have h1 : ... := by ...
  -- Step 2
  have h2 : ... := by ...
  -- Conclude
  exact ...
```

---

## Anti-patterns (Things That DON'T Work)

| Anti-pattern | Why it fails | What to do instead |
|--------------|--------------|-------------------|
| `induction st` on Stmt | "nested inductive type" error | Use `cases` + mutual theorem pattern |
| `lean_build` for verification | Takes forever | Use `lean_verify` per file |
| `axiom` keyword | Unsound | Use `theorem ... := by sorry` for stubs |
| Importing from parent workspace | Circular dependencies | Keep imports within the library |
| Multi-theorem files in decomposed/ | File organization constraint | One theorem per file |
| `induction hstar` without converting | `ReflTrans` lives in Prop | Convert to `ReflTransT` first for structural recursion |
| `omega` on non-arithmetic goals | Only works on Nat/Int linear arithmetic | Use `simp`, `exact`, or `cases` |
| `simp` with too many lemmas | Non-termination / unexpected rewrites | Be precise: `simp only [lemma1, lemma2]` |
| `decide` on infinite types | Loops / times out | Use `cases` or `exact` |
| Unfolding step relations manually | Verbose and fragile | Use the helper lemmas (seq_reaches_terminal, etc.) |

---

## External References

### Simulation and Compiler Verification

- **CompCert** — https://compcert.org/
  - Xavier Leroy, "A formally verified compiler back-end" (2006)
  - Chapter 4: "Semantic preservation" — forward simulation, plus/star distinction
  - Measure-based termination for loops (CompCert uses Nat measures)
  - "Simulation diagrams" pattern: match source steps with target steps

- **CertiCoq** — https://github.com/CertiCoq/certicoq
  - Verified compiler from Gallina (Coq) to C
  - Multi-pass pipeline correctness via simulation composition

- **Vellvm** — https://github.com/vellvm/vellvm
  - Verified LLVM IR semantics in Coq
  - Interaction trees for denotational semantics + simulation

### Lean 4 Proof Engineering

- **Mathematics in Lean** — https://leanprover-community.github.io/mathematics_in_lean/
  - Chapter 6: Structures and type classes
  - Chapter 7: Inductive types (including mutual/nested)

- **Theorem Proving in Lean 4** — https://lean-lang.org/theorem_proving_in_lean4/
  - Chapter 7: Inductive Types — the definitive reference for nested inductives
  - Chapter 8: Tactics

- **Lean4 Metaprogramming Book** — https://leanprover-community.github.io/lean4-metaprogramming-book/
  - Custom tactics, simp lemmas, macro development

- **Mathlib4** — https://github.com/leanprover-community/mathlib4
  - `Mathlib.Order.RelClasses` — reflexive-transitive closure patterns
  - `Mathlib.Computability.Language` — formal language theory
  - `Mathlib.Tactic` — advanced tactic reference (omega, positivity, etc.)

- **Lean4 Docs: Well-Founded Recursion** — https://lean-lang.org/lean4/doc/well_founded_recursion.html
  - `termination_by`, `decreasing_by`, WF proof techniques

### Program Semantics and Simulation

- **Software Foundations** (Coq, but concepts transfer) — https://softwarefoundations.cis.upenn.edu/
  - Volume 1 (LF): Induction, lists, basic tactics
  - Volume 2 (PLF): Small-step semantics, simulation proofs
  - Volume 3 (VFA): Verified functional algorithms

- **Concrete Semantics** (Isabelle/HOL) — https://concrete-semantics.org/
  - Part II: Operational semantics, Hoare logic, compiler correctness
  - Chapter 7: IMP compiler and its correctness proof

- **Formal Reasoning About Programs** — http://adam.chlipala.net/frap/
  - Adam Chlipala (Coq-based)
  - Chapter on compiler correctness and simulation relations
  - Bisimulation and trace equivalence

### Kleene Algebra and Program Algebra

- **Kleene Algebra with Tests (KAT)** — Dexter Kozen
  - "Kleene Algebra with Tests" (1997): https://www.cs.cornell.edu/~kozen/Papers/kat.pdf
  - Axiomatization of while programs as algebraic structures
  - NetKAT and extensions for network verification

- **Demonic Refinement Algebra** — https://link.springer.com/chapter/10.1007/11874683_26
  - Jules Desharnais, Georg Struth — extends KAT with nondeterminism

### Relevant Lean 4 Projects

- **lean4-samples** — https://github.com/leanprover/lean4-samples
  - Official examples including verified data structures

- **Verified Functional Programming in Agda** — https://github.com/stoughton/vfpa
  - While in Agda, covers similar verification patterns (simulation, bisimulation)

- **LeanSAT** — https://github.com/leanprover/leansat
  - Verified SAT solving in Lean 4 — example of large-scale verification

- **Batteries** (std4) — https://github.com/leanprover-community/batteries
  - List, Array, HashMap utilities that Lean proofs commonly use

### Relevant Coq/Rocq Projects

- **CompCert Source** — https://github.com/AbsInt/CompCert
  - `backend/Simulations.v` — canonical simulation diagram library
  - `common/Smallstep.v` — generic small-step semantics framework
  - `common/Events.v` — trace semantics

- **Iris** — https://iris-project.org/ / https://gitlab.mpi-sws.org/iris/iris
  - Higher-order concurrent separation logic in Coq
  - Foundational verification of concurrent programs

- **VST (Verified Software Toolchain)** — https://github.com/PrincetonUniversity/VST
  - Hoare-logic-based verification of C programs in Coq
  - Floyd tactic library for separation logic proofs

- **RefinedC** — https://plv.mpi-sws.org/refinedc/
  - Refinement-type-based verification of C against Iris specs

- **Interaction Trees** — https://github.com/DeepSpec/InteractionTrees
  - Monadic representation of effectful computations
  - Enables equational reasoning about programs via coinduction

### Books on Formal Verification

- **"Certified Programming with Dependent Types"** (Chlipala)
  - http://adam.chlipala.net/cpdt/
  - Advanced Coq techniques: reflection, proof by computation

- **"Program Logics for Certified Compilers"** (Andrew Appel)
  - Cambridge University Press, 2014
  - The theoretical foundation behind VST
  - Chapters on operational semantics and Hoare logic soundness

- **"The Formal Semantics of Programming Languages"** (Winskel)
  - MIT Press — classic reference for denotational/operational/axiomatic semantics

- **"Types and Programming Languages"** (Pierce)
  - MIT Press — type systems, operational semantics foundations

---

## Tips for Proof Writers

1. **Always search existing lemmas first** — the codebase has many helper lemmas
   already proved. Use `#check`, `exact?`, `apply?`.
2. **Check if `simp` lemmas exist** — many rewrites are tagged `@[simp]`
3. **Read the `*Props.lean` files** — `SemanticsProps.lean` and
   `KleeneSemanticsProps.lean` contain the lifting/inversion/completion helpers
4. **For contradiction cases**: `simp [TranslationFn] at hT` closes cases where the translation returns `none`
5. **For loop cases**: need well-founded recursion on trace length
6. **Don't try `induction` on Stmt** — use `cases` + mutual theorem pattern
7. **Use `ReflTrans_Transitive _ _ _ _`** for chaining — always provide 4 underscores
   for the implicit args
8. **Terminal configs cannot step** — use `exact absurd hstep (by intro h; cases h)`
9. **`simp only [...]`** is safer than bare `simp` — avoids unexpected rewrites
10. **Custom tactic `term_by_mem`** — solves termination goals for rose-tree recursion
11. **`generalize_lhs_last_arg`** — useful for generalizing the last argument of the
    LHS when the goal is an equality

---

## Quick Reference: Proof Skeletons

### Skeleton: Overapproximation Proof

```lean
theorem myTransform_correct :
    Specification.Overapproximates L₁ L₂ myTransform "my_prefix" := by
  intro prefixIdents st st' hT hMem hPD ρ₀ hWF
  -- Analyze the translation
  simp [myTransform] at hT
  -- Split into three goals
  refine ⟨fun ρ' => ⟨?_, ?_⟩, ?_, ?_⟩
  -- Terminal preservation
  · intro hstar
    sorry
  -- Exiting preservation
  · intro lbl hstar
    sorry
  -- CanFail preservation
  · intro ⟨ρ', hstar, hfail⟩
    sorry
  -- WF preservation
  · sorry
```

### Skeleton: Multi-step Trace Construction

```lean
-- Goal: build a multi-step trace in the target language
-- Pattern: chain together individual steps/sub-traces via transitivity
exact ReflTrans_Transitive _ _ _ _
  (first_sub_trace)   -- source → intermediate config
  (ReflTrans_Transitive _ _ _ _
    (second_sub_trace)  -- intermediate → another intermediate
    (final_sub_trace))  -- → terminal

-- For single step + rest:
exact .step _ _ _ (single_step_constructor args) (rest_of_trace)
```

### Skeleton: Structural Inversion of a Trace

```lean
-- Given: hstar : StepStmtStar ... (.stmts (s :: ss) ρ₀) (.terminal ρ')
-- Step into the seq
match hstar with
| .step _ _ _ .step_stmts_cons hrest =>
  -- hrest : ... (.seq (.stmt s ρ₀) ss) →* (.terminal ρ')
  have ⟨ρ₁, h_s_term, h_rest_term⟩ := seq_reaches_terminal _ _ _ hrest
  -- h_s_term : (.stmt s ρ₀) →* (.terminal ρ₁)
  -- h_rest_term : (.stmts ss ρ₁) →* (.terminal ρ')
  ...
```

### Skeleton: Loop Simulation with Decreasing Measure

```lean
-- Generic pattern: induction on trace length for loop constructs
noncomputable def loop_sim
    (hstarT : ReflTransT (StepStmt ...) (.stmt (.loop ...) ρ) (.terminal ρ'))
    : TargetStar ... (.stmt target_loop ρ) (.terminal ρ') := by
  match hstarT with
  | .step _ _ _ (.step_loop_exit hcond) hrest =>
    -- Guard false → exit immediately
    cases hrest with | refl => exact ...
  | .step _ _ _ (.step_loop_enter hcond) hrest =>
    -- Guard true → body executes → recurse on smaller trace
    have smaller : ReflTransT ... := extract_smaller_trace hrest
    exact ReflTrans_Transitive _ _ _ _
      (target_enter_step)
      (loop_sim smaller)
termination_by hstarT.len
```
