# Design: Formal Semantics for Laurel IR

**Date:** 2026-03-03
**Status:** Proposal

## 1. Problem Statement

Laurel is Strata's common intermediate representation for front-end languages like Java, Python, and JavaScript. It is translated to Strata Core for verification. However, Laurel currently lacks its own formal operational semantics — its meaning is defined only implicitly through the translation in `LaurelToCoreTranslator.lean` and the partial interpreter in `LaurelEval.lean`.

This creates several problems:

1. **No independent specification.** If the translator has a bug, there is no reference semantics to detect it. The translator *is* the semantics, so any behavior it produces is "correct" by definition.

2. **No formal properties.** We cannot state or prove determinism, progress, or type preservation for Laurel programs directly.

3. **No translation correctness.** Without Laurel semantics, we cannot prove that `LaurelToCoreTranslator` preserves program meaning — the central correctness property for the entire verification pipeline.

4. **Laurel-specific constructs have no formal account.** Constructs like labeled `Block`/`Exit` (modeling break/continue), `StmtExpr` unification (expressions that are also statements), `Return`, type operations (`IsType`, `AsType`), and object-oriented features (`InstanceCall`, `FieldSelect`, `New`) need precise semantic definitions.

### Concrete example: labeled Exit

```
// Laurel source (pseudocode)
var x: int := 0;
outer: {
  inner: {
    x := 1;
    exit outer;   // break out of outer block
    x := 2;       // dead code
  }
  x := 3;         // also dead code
}
assert x == 1;
```

The translator converts `exit outer` into Core's `goto` mechanism, but there is no formal proof that this translation preserves the intended semantics. A direct Laurel semantics would define `Exit` as non-local control flow that unwinds to the matching labeled `Block`, and we could then prove the translation correct.

### Concrete example: expression-statement duality

```
// Laurel: if-then-else as expression returning a value
var y: int := if (x > 0) { x } else { 0 - x };
```

Laurel's `StmtExpr` type unifies statements and expressions. The "last expression as block value" convention means blocks can produce values. This needs a formal account — Core has no such concept (it separates expressions from statements).

## 2. Background

### 2.1 Core Semantics (existing)

Core's formal semantics is defined in three layers:

**Generic framework** (`Strata/DL/Imperative/StmtSemantics.lean`):
- `SemanticStore P` — variable store: `P.Ident → Option P.Expr`
- `SemanticEval P` — expression evaluator: `Store → Expr → Option Expr`
- `EvalCmd` — inductive relation for atomic commands (init, set, havoc, assert, assume)
- `EvalStmt` / `EvalBlock` — mutually inductive relations for statements and statement lists
- Judgment form: `δ, σ, stmt ⊢ σ', δ'` (evaluator and store are threaded)

**Core instantiation** (`Strata/Languages/Core/StatementSemantics.lean`):
- `Value` predicate for irreducible Core expressions
- `WellFormedCoreEvalDefinedness`, `WellFormedCoreEvalCong` — well-formedness conditions
- `EvalCommand` — extends `EvalCmd` with procedure calls (`call_sem`)
- `EvalStatement` / `EvalStatements` — type aliases for the instantiated generic framework
- `EvalCommandContract` — contract-based call semantics (havoc + assume postconditions)

**Properties** (`Strata/Languages/Core/StatementSemanticsProps.lean`):
- Store monotonicity theorems (`InitStateDefMonotone`, `UpdateStateDefMonotone`, etc.)
- Injective store operations (`InitStateInjective`, `ReadValuesInjective`)
- `EvalStmtRefinesContract` / `EvalBlockRefinesContract` — body execution refines contract semantics
- Substitution and invariant store theorems

Key design patterns:
- Stores are abstract functions, not concrete data structures
- `InitState` requires the variable was previously unmapped; `UpdateState` requires it was mapped
- The evaluator `δ` is threaded as state to support `funcDecl` extending it
- Commands don't modify `δ`; only `funcDecl` does

### 2.2 Laurel AST (existing)

Defined in `Strata/Languages/Laurel/Laurel.lean`:

`StmtExpr` is a single mutual inductive covering both statements and expressions:
- **Control flow:** `IfThenElse`, `Block` (with optional label), `While` (with invariants/decreases), `Exit` (labeled break), `Return`
- **Expressions:** `LiteralInt`, `LiteralBool`, `LiteralString`, `Identifier`, `PrimitiveOp`, `StaticCall`, `FieldSelect`, `Forall`, `Exists`
- **Assignments:** `Assign`, `LocalVariable`
- **OO features:** `New`, `This`, `InstanceCall`, `AsType`, `IsType`, `ReferenceEquals`, `PureFieldUpdate`
- **Verification:** `Assert`, `Assume`, `Old`, `Fresh`, `Assigned`, `ProveBy`, `ContractOf`

All nodes are wrapped in `WithMetadata` carrying source locations.

`Procedure` has inputs, outputs, preconditions, determinism, optional decreases, and a `Body` (Transparent/Opaque/Abstract).

### 2.3 Translation pipeline (existing)

`LaurelToCoreTranslator.lean` implements:
1. `heapParameterization` — makes heap explicit as a parameter
2. `typeHierarchyTransform` — encodes type hierarchy
3. `modifiesClausesTransform` — infers modifies clauses
4. `liftImperativeExpressions` — lifts assignments out of expression positions
5. `translateExpr` — Laurel expressions → Core expressions
6. `translateStmt` — Laurel statements → Core statements
7. `translateProcedure` — Laurel procedures → Core procedures

### 2.4 Existing Laurel evaluator

`LaurelEval.lean` defines a `partial def eval` interpreter in `HighLevel` namespace. It uses a different AST (`HighLevel.StmtExpr`) with constructs like `StaticInvocation`, `Closure`, `DynamicFieldAccess` that differ from the main `Laurel.StmtExpr`. This evaluator:
- Is `partial` (no termination proof)
- Uses a monadic `Eval` type with `EvalResult` (Success/Return/Exitting/TypeError/VerficationError)
- Has many `panic!` stubs for unimplemented features
- Operates on a different type hierarchy than the main Laurel AST

This evaluator cannot serve as a formal semantics because it is partial, uses a different AST, and lacks any formal properties.

## 3. Design Options

### Option A: Direct Operational Semantics

Define `EvalLaurelStmt` as a standalone inductive relation on `Laurel.StmtExpr`, independent of Core semantics.

#### a. Implementation strategy

Create new files in `Strata/Languages/Laurel/`:

| File | Purpose |
|------|---------|
| `LaurelSemantics.lean` | Core semantic definitions: store, evaluator, `EvalLaurelStmt`/`EvalLaurelBlock` |
| `LaurelSemanticsProps.lean` | Determinism, progress, store monotonicity theorems |
| `LaurelTranslationCorrect.lean` | Bisimulation between Laurel and Core semantics |

The semantic judgment has the form:

```lean
-- Laurel semantic store maps identifiers to Laurel values
abbrev LaurelStore := Laurel.Identifier → Option LaurelValue

-- Laurel values (distinct from Core values)
inductive LaurelValue where
  | vInt : Int → LaurelValue
  | vBool : Bool → LaurelValue
  | vString : String → LaurelValue
  | vVoid : LaurelValue
  | vRef : Nat → LaurelValue  -- heap reference

-- Outcome captures non-local control flow
inductive Outcome where
  | normal : LaurelValue → Outcome    -- normal completion with value
  | exit : Identifier → Outcome       -- exit to labeled block
  | ret : Option LaurelValue → Outcome -- return from procedure

-- Expression evaluator
abbrev LaurelEval := LaurelStore → StmtExpr → Option LaurelValue

-- Main judgment: store, expression/statement ⊢ store', outcome
mutual
inductive EvalLaurelStmt :
    LaurelEval → LaurelStore → StmtExprMd → LaurelStore → Outcome → Prop where
  | literal_int :
    EvalLaurelStmt δ σ ⟨.LiteralInt i, md⟩ σ (.normal (.vInt i))
  | literal_bool :
    EvalLaurelStmt δ σ ⟨.LiteralBool b, md⟩ σ (.normal (.vBool b))
  | ite_true :
    EvalLaurelStmt δ σ cond σ₁ (.normal (.vBool true)) →
    EvalLaurelStmt δ σ₁ thenBr σ₂ outcome →
    EvalLaurelStmt δ σ ⟨.IfThenElse cond thenBr (some elseBr), md⟩ σ₂ outcome
  | block_sem :
    EvalLaurelBlock δ σ stmts σ' outcome →
    -- If outcome is exit targeting this label, catch it
    catchExit label outcome = outcome' →
    EvalLaurelStmt δ σ ⟨.Block stmts label, md⟩ σ' outcome'
  | exit_sem :
    EvalLaurelStmt δ σ ⟨.Exit target, md⟩ σ (.exit target)
  | while_true :
    EvalLaurelStmt δ σ cond σ₁ (.normal (.vBool true)) →
    EvalLaurelStmt δ σ₁ body σ₂ (.normal _) →
    EvalLaurelStmt δ σ₂ ⟨.While cond invs dec body, md⟩ σ₃ outcome →
    EvalLaurelStmt δ σ ⟨.While cond invs dec body, md⟩ σ₃ outcome
  -- ... more constructors
inductive EvalLaurelBlock :
    LaurelEval → LaurelStore → List StmtExprMd → LaurelStore → Outcome → Prop where
  | nil : EvalLaurelBlock δ σ [] σ (.normal .vVoid)
  | cons_normal :
    EvalLaurelStmt δ σ s σ' (.normal v) →
    EvalLaurelBlock δ σ' rest σ'' outcome →
    EvalLaurelBlock δ σ (s :: rest) σ'' outcome
  | cons_exit :
    EvalLaurelStmt δ σ s σ' (.exit label) →
    EvalLaurelBlock δ σ (s :: rest) σ' (.exit label)
  | cons_return :
    EvalLaurelStmt δ σ s σ' (.ret v) →
    EvalLaurelBlock δ σ (s :: rest) σ' (.ret v)
end
```

Key design decisions:
- `Outcome` type handles non-local control flow (Exit, Return) explicitly, rather than using Core's goto mechanism
- `EvalLaurelBlock` propagates Exit/Return outcomes, skipping remaining statements
- Labeled `Block` catches matching `Exit` outcomes via `catchExit`
- The "last expression as block value" convention: the final `Outcome.normal v` in a block becomes the block's value

#### b. Internal representation

**Laurel values** are a separate type from Core expressions. This is necessary because:
- Laurel has heap references (`vRef`) that Core encodes differently (via map operations)
- Laurel's type system (nominal types, interfaces) requires runtime type tags
- The value domain must support `IsType`/`AsType` operations

**Store** is `Identifier → Option LaurelValue` (string-keyed, matching Laurel's `abbrev Identifier := String`).

**Heap** is modeled as a separate component `Nat → Option (Identifier × (Identifier → Option LaurelValue))` mapping references to (type-tag, field-store) pairs. This supports `New`, `FieldSelect`, and `ReferenceEquals`.

**Expression evaluation** is a parameter `δ : LaurelEval` following Core's pattern, allowing different instantiations for different analysis modes.

#### c. End-to-end correctness

Translation correctness is stated as a simulation relation:

```lean
-- Value correspondence
def valueCorr : LaurelValue → Core.Expression.Expr → Prop := ...

-- Store correspondence (after heap parameterization)
def storeCorr : LaurelStore → LaurelHeap → CoreStore → Prop := ...

-- Main theorem: if Laurel evaluates, the translated Core program
-- evaluates to a corresponding result
theorem translate_correct :
  EvalLaurelStmt δL σL stmt σL' outcome →
  storeCorr σL heap σC →
  let (_, coreStmts) := translateStmt env outputs ⟨stmt, md⟩ |>.run initState
  ∃ σC' δC',
    EvalStatements π φ δC σC coreStmts σC' δC' ∧
    storeCorr σL' heap' σC'
```

The proof must account for the translation pipeline stages:
1. `heapParameterization` — relate Laurel heap to explicit heap parameter
2. `liftImperativeExpressions` — show lifting preserves semantics
3. `translateStmt` — show statement translation preserves semantics

Each stage needs its own correctness lemma, composed for the full pipeline.

#### d. Testing strategy

| Test type | Location | Purpose |
|-----------|----------|---------|
| Concrete evaluation | `StrataTest/Languages/Laurel/LaurelSemanticsTest.lean` | `#guard_msgs` tests showing specific evaluations |
| Determinism examples | Same file | Show unique outcomes for concrete programs |
| Exit/Return propagation | Same file | Test non-local control flow |
| Translation correspondence | `StrataTest/Languages/Laurel/TranslationCorrectTest.lean` | Concrete examples where both semantics agree |

Limitations:
- `While` semantics is coinductive in nature; the inductive relation only captures terminating executions
- OO features (heap, dynamic dispatch) significantly increase complexity
- Full translation correctness proof requires reasoning about 5+ pipeline stages

#### e. Complexity and risk

**Files changed:** 3 new files, 0 modified
**Estimated LOC:** ~800 (semantics) + ~500 (properties) + ~1500+ (translation correctness)
**Risk:**
- High: Laurel's `StmtExpr` has ~35 constructors; defining semantics for all is substantial
- High: Translation correctness proof must reason about heap parameterization, expression lifting, and statement translation simultaneously
- Medium: `Outcome` type adds complexity to every induction over the semantics
- The Laurel value domain and Core expression domain are very different, making `valueCorr` non-trivial

---

### Option B: Shallow Embedding via Translation

Define Laurel's semantics as "the semantics of the translated Core program." No new inductive relation — Laurel's meaning is Core's meaning after translation.

#### a. Implementation strategy

Create minimal new files:

| File | Purpose |
|------|---------|
| `LaurelSemanticsViaCore.lean` | Definitions composing translation with Core semantics |
| `LaurelTranslationProps.lean` | Properties of the translation (well-typedness preservation, etc.) |

The "semantics" is a definition, not an inductive:

```lean
-- Laurel program evaluates iff its Core translation evaluates
def LaurelEvaluatesTo (program : Laurel.Program) (σ σ' : CoreStore) (δ δ' : CoreEval) : Prop :=
  match translate program with
  | .ok (coreProgram, _) =>
    ∃ π φ, EvalStatements π φ δ σ coreProgram.body σ' δ'
  | .error _ => False

-- Per-procedure semantics
def LaurelProcEvaluatesTo (proc : Laurel.Procedure) (σ σ' : CoreStore) : Prop :=
  let (coreProc, _) := runTranslateM initState (translateProcedure proc)
  ∃ δ δ' π φ, EvalStatements π φ δ σ coreProc.body σ' δ'
```

#### b. Internal representation

No new value types or store types. Everything uses Core's representation:
- Values are `Core.Expression.Expr` satisfying `Core.Value`
- Store is `CoreStore` = `Core.Expression.Ident → Option Core.Expression.Expr`
- Evaluation uses `EvalStatement` / `EvalStatements` from Core

Laurel identifiers are mapped to Core identifiers via `⟨name, ()⟩`.

#### c. End-to-end correctness

Translation correctness is trivial by construction — Laurel's semantics *is* Core's semantics after translation. There is nothing to prove.

However, we can still prove useful properties:

```lean
-- The translation produces well-typed Core programs
theorem translate_well_typed :
  laurelTypeChecks program →
  coreTypeChecks (translate program)

-- The translation preserves procedure structure
theorem translate_preserves_procedures :
  program.staticProcedures.length = (translate program).procedures.length

-- Specific construct correctness (e.g., Exit → goto)
theorem exit_translates_correctly :
  -- Exit to label L in Laurel becomes goto L in Core
  ...
```

Properties like determinism and progress are inherited from Core automatically — if Core's semantics is deterministic, and the translation is a function, then Laurel's derived semantics is deterministic.

#### d. Testing strategy

| Test type | Location | Purpose |
|-----------|----------|---------|
| Translation output | `StrataTest/Languages/Laurel/TranslationTest.lean` | `#guard_msgs` showing translated Core for each Laurel construct |
| Round-trip verification | Existing `Examples/` | Verify Laurel programs produce expected SMT results |
| Regression tests | Same | Ensure translation changes don't break verification |

Limitations:
- Cannot reason about Laurel programs independently of Core
- Cannot state properties about Laurel constructs that are erased by translation (e.g., type assertions in an erasure model)
- If the translation has a bug, the "semantics" has the same bug — no independent check
- Cannot compare alternative translations (e.g., optimized vs. reference)

#### e. Complexity and risk

**Files changed:** 2 new files, 0 modified
**Estimated LOC:** ~200 (definitions) + ~300 (properties)
**Risk:**
- Low implementation risk — very little new code
- High conceptual risk — this doesn't actually define Laurel semantics, it just names the composition of translation + Core semantics
- Medium: Properties we can prove are limited to translation structure, not semantic content
- The approach provides no defense against translator bugs

---

### Option C: Hybrid — Direct Semantics for Core Constructs, Desugaring for High-Level Constructs

Define direct operational semantics for the "imperative core" of Laurel (assignments, control flow, expressions), and define high-level constructs (OO features, type operations) via desugaring to this core.

#### a. Implementation strategy

Create files in two phases:

**Phase 1 — Imperative core semantics:**

| File | Purpose |
|------|---------|
| `LaurelSemantics.lean` | `EvalLaurelStmt`/`EvalLaurelBlock` for imperative subset |
| `LaurelSemanticsProps.lean` | Determinism, progress, monotonicity for imperative subset |

**Phase 2 — High-level construct desugaring + translation correctness:**

| File | Purpose |
|------|---------|
| `LaurelDesugar.lean` | Laurel-to-Laurel desugaring (OO → imperative core) |
| `LaurelDesugarCorrect.lean` | Desugaring preserves semantics |
| `LaurelTranslationCorrect.lean` | Imperative core → Core translation correctness |

The imperative core covers these `StmtExpr` constructors:
- `LiteralInt`, `LiteralBool`, `LiteralString`, `Identifier` — values/variables
- `PrimitiveOp` — arithmetic and boolean operations
- `Assign`, `LocalVariable` — variable mutation
- `IfThenElse`, `While`, `Block`, `Exit`, `Return` — control flow
- `Assert`, `Assume` — verification constructs
- `StaticCall` — procedure calls (without OO dispatch)
- `Forall`, `Exists` — quantifiers (in specification contexts)

High-level constructs handled by desugaring:
- `New`, `FieldSelect`, `PureFieldUpdate`, `InstanceCall`, `This` → desugared using heap parameterization (already exists as `heapParameterization`)
- `IsType`, `AsType` → desugared using type hierarchy encoding (already exists as `typeHierarchyTransform`)
- `ReferenceEquals` → desugared to equality on references
- `Old`, `Fresh`, `Assigned` → desugared to two-state predicates

This aligns with the existing translation pipeline, which already performs these transformations before `translateStmt`.

#### b. Internal representation

**Values** for the imperative core:

```lean
inductive LaurelValue where
  | vInt : Int → LaurelValue
  | vBool : Bool → LaurelValue
  | vString : String → LaurelValue
  | vFloat64 : Float → LaurelValue
  | vVoid : LaurelValue
```

No heap references in the core — those are introduced by desugaring (heap parameterization makes the heap an explicit map variable).

**Store** is `Identifier → Option LaurelValue`.

**Outcome** type for non-local control flow (same as Option A):

```lean
inductive Outcome where
  | normal : LaurelValue → Outcome
  | exit : Identifier → Outcome
  | ret : Option LaurelValue → Outcome
```

**Semantic judgment:**

```lean
mutual
inductive EvalLaurelStmt :
    LaurelEval → LaurelStore → StmtExprMd → LaurelStore → Outcome → Prop
inductive EvalLaurelBlock :
    LaurelEval → LaurelStore → List StmtExprMd → LaurelStore → Outcome → Prop
end
```

The key difference from Option A: the inductive only has constructors for the imperative core (~18 constructors instead of ~35). OO and type-level constructs are excluded — they must be desugared first.

#### c. End-to-end correctness

The correctness argument is modular, matching the existing pipeline:

```
Laurel (full)
  ──[heapParameterization]──→ Laurel (no heap/OO)     -- LaurelDesugarCorrect.lean
  ──[typeHierarchyTransform]──→ Laurel (no types)      -- LaurelDesugarCorrect.lean
  ──[liftImperativeExpressions]──→ Laurel (imp. core)  -- LaurelDesugarCorrect.lean
  ──[translateStmt]──→ Core                            -- LaurelTranslationCorrect.lean
```

Each arrow has its own correctness theorem:

```lean
-- Desugaring preserves semantics (Laurel → Laurel)
theorem heapParam_correct :
  EvalLaurelStmt_full δ σ stmt σ' outcome →
  ∃ σC σC',
    storeCorr σ σC ∧
    EvalLaurelStmt δC σC (heapParam stmt) σC' outcomeC ∧
    storeCorr σ' σC'

-- Core translation preserves semantics (Laurel imperative core → Core)
theorem translateStmt_correct :
  EvalLaurelStmt δL σL stmt σL' (.normal v) →
  storeCorr σL σC →
  let coreStmts := (translateStmt env outputs ⟨stmt, md⟩ |>.run s).1.2
  ∃ σC' δC',
    EvalStatements π φ δC σC coreStmts σC' δC' ∧
    storeCorr σL' σC'
```

The full pipeline correctness composes these lemmas.

#### d. Testing strategy

| Test type | Location | Purpose |
|-----------|----------|---------|
| Core semantics | `StrataTest/Languages/Laurel/LaurelSemanticsTest.lean` | Concrete evaluations of imperative core |
| Exit/Return | Same | Non-local control flow examples |
| Desugaring | `StrataTest/Languages/Laurel/LaurelDesugarTest.lean` | Show desugaring output for OO constructs |
| Translation | `StrataTest/Languages/Laurel/TranslationCorrectTest.lean` | End-to-end correspondence examples |
| Property tests | `StrataTest/Languages/Laurel/LaurelSemanticsPropsTest.lean` | Determinism, monotonicity on concrete examples |

Limitations:
- Desugaring correctness proofs for heap parameterization are complex (the existing `heapParameterization` function is ~600 lines)
- The boundary between "imperative core" and "desugared" constructs is a design choice that may need revision
- `While` still only captures terminating executions

#### e. Complexity and risk

**Files changed:** 4-5 new files, 0 modified
**Estimated LOC:** ~500 (core semantics) + ~300 (properties) + ~400 (desugaring correctness) + ~600 (translation correctness)
**Risk:**
- Medium: Imperative core is well-scoped (~18 constructors), manageable
- Medium: Desugaring correctness for heap parameterization is the hardest part, but can be deferred
- Low: Core semantics and properties can be developed and tested independently
- The modular structure means each piece can be verified in isolation

## 4. Recommendation

**Option C (Hybrid)** is recommended.

### Rationale

1. **Matches the existing architecture.** The translation pipeline already performs Laurel→Laurel desugaring (heap parameterization, type hierarchy, expression lifting) before Laurel→Core translation. Option C formalizes this existing structure rather than fighting it.

2. **Incremental development.** We can deliver value in phases:
   - Phase 1: Imperative core semantics + determinism/progress proofs (~800 LOC). This is immediately useful for reasoning about control flow, assignments, and verification constructs.
   - Phase 2: Translation correctness for the imperative core → Core (~600 LOC). This validates `translateStmt` for the most common constructs.
   - Phase 3: Desugaring correctness for individual passes (can be done per-pass, in any order).

3. **Right level of abstraction.** Option A tries to formalize everything at once (including OO features that are already desugared away before Core translation). Option B provides no independent semantics at all. Option C gives us a real semantics for the constructs that matter most (control flow, assignments, verification) while deferring the complexity of OO encoding.

4. **Manageable proof obligations.** The imperative core has ~18 constructors (vs. ~35 for full StmtExpr). Determinism and progress proofs scale with constructor count. The `Outcome` type adds some complexity but is essential for modeling `Exit`/`Return` correctly.

5. **Reuses existing infrastructure.** The `Outcome` type mirrors `EvalResult` from `LaurelEval.lean`. The store model follows Core's `SemanticStore` pattern. The modular correctness structure follows the existing `EvalStmtRefinesContract` pattern.

### Suggested implementation order

1. Define `LaurelValue`, `LaurelStore`, `Outcome` types
2. Define `EvalLaurelStmt` / `EvalLaurelBlock` for imperative core
3. Write concrete evaluation tests
4. Prove determinism for the imperative core
5. Prove store monotonicity
6. Define store correspondence `LaurelStore ↔ CoreStore`
7. Prove `translateStmt` correctness for simple constructs (Assign, LocalVariable, IfThenElse)
8. Extend to While, Block/Exit, Return
9. (Later) Prove desugaring correctness for heap parameterization
10. (Later) Prove desugaring correctness for expression lifting
