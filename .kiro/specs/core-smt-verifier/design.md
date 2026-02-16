# Design Document: CoreSMT Verifier

## Overview

The CoreSMT Verifier is a streaming verification component for Strata Core programs that translates a well-defined subset of Core statements directly to SMT for verification. It processes statements incrementally, enabling immediate feedback and automatic diagnosis of failures.

The verifier operates on the `isCoreSMT` subset of Strata Core, which includes only constructs that map 1-1 with SMT-LIB:
- `assume` → SMT `assert`
- `init x := e` → SMT `define-fun`
- `init x` (no expr) → SMT `declare-fun`
- `assert`/`check` → SMT `check-sat` (of negation)
- `cover` → SMT `check-sat` (of expression)
- `block` → SMT `push`/`pop`
- `funcDecl` → SMT `declare-fun`/`define-fun`

Expressions are supported including immediately applied abstractions (translated to SMT `let`). Standalone abstractions that aren't immediately applied are not supported.

For statements outside this subset (if-then-else, loops, goto, procedure calls), the verifier returns an error, allowing callers to use alternative verification approaches.

### Key Design Decisions

1. **Streaming Architecture**: Statements are verified immediately as they are processed, allowing the SMT solver to accumulate knowledge from asserts and assumes.

2. **SMT Solver Interface as Structure**: The solver interface is a structure (not a type class) to allow runtime selection of different solver backends.

3. **State Reuse**: The verifier returns updated state that can be reused for subsequent verifications, enabling prelude processing and state sharing.

4. **Reuse Existing Types**: VCResult, Outcome, and Env are reused from the existing Core verifier for compatibility.

5. **Diagnosis Migration**: The diagnosis functionality from B3 verifier is migrated to work with Core expressions.

## Prerequisites

Before implementing the CoreSMT Verifier, the following changes to the existing codebase are required:

### Extend `Cmd.init` to Support Optional RHS

The current `Cmd.init` in `Strata/DL/Imperative/Cmd.lean` requires an expression:

```lean
-- Current definition (requires expression)
| init (name : P.Ident) (ty : P.Ty) (e : P.Expr) (md : (MetaData P) := .empty)
```

This needs to be extended to support optional RHS:

```lean
-- New definition (optional expression)
| init (name : P.Ident) (ty : P.Ty) (e : Option P.Expr) (md : (MetaData P) := .empty)
```

This change will require updates to:
- `Statement.init` pattern in `Statement.lean`
- All places that construct `Cmd.init` (search for `Cmd.init` and `Statement.init`)
- Type checking in `CmdType.lean`
- Evaluation in `CmdEval.lean`
- Semantics in `CmdSemantics.lean`

The semantics of `init x : T` (without RHS) is equivalent to `havoc x` - it declares an unconstrained variable.

## Architecture

```
┌─────────────────────────────────────────────────────────────────┐
│                     CoreSMT_Verifier                            │
├─────────────────────────────────────────────────────────────────┤
│  Public Interface                                               │
│    verify : SMTSolverInterface → CoreSMTState → List Statement  │
│           → IO (CoreSMTState × Array VCResult)                  │
├─────────────────────────────────────────────────────────────────┤
│  Internal Components                                            │
│  ┌─────────────────┐  ┌─────────────────┐  ┌────────────────┐  │
│  │ Statement       │  │ Expression      │  │ Diagnosis      │  │
│  │ Processor       │  │ Translator      │  │ Engine         │  │
│  └────────┬────────┘  └────────┬────────┘  └───────┬────────┘  │
│           │                    │                    │           │
│           └────────────────────┼────────────────────┘           │
│                                │                                │
│  ┌─────────────────────────────┴─────────────────────────────┐  │
│  │              SMT Solver Interface                          │  │
│  │  (structure with push/pop/assert/checkSat/getModel)        │  │
│  └────────────────────────────────────────────────────────────┘  │
└─────────────────────────────────────────────────────────────────┘
```

### Data Flow

1. **Input**: List of Core.Statement
2. **isCoreSMT Check**: Each statement is checked against the isCoreSMT predicate
3. **Translation**: CoreSMT statements are translated to SMT commands
4. **Verification**: Proof/cover checks are performed via the SMT solver
5. **Diagnosis**: Failed checks are diagnosed if enabled
6. **Output**: List of VCResult

## Components and Interfaces

### SMT Solver Interface

The SMT solver interface is a structure that abstracts over different SMT solver backends. It uses the existing `Strata.SMT.Term` type which can be converted to SMT-LIB strings via `SMTDDM.toString`:

```lean
/-- Abstract interface for SMT solvers.
    Uses Strata.SMT.Term which can be converted to SMT-LIB strings via SMTDDM.toString -/
structure SMTSolverInterface where
  /-- Push a new scope onto the solver stack -/
  push : IO Unit
  /-- Pop the top scope from the solver stack -/
  pop : IO Unit
  /-- Declare an uninterpreted sort -/
  declareSort : String → Nat → IO Unit
  /-- Declare an uninterpreted function -/
  declareFun : String → List SMT.TermType → SMT.TermType → IO Unit
  /-- Define a function with a body -/
  defineFun : String → List (String × SMT.TermType) → SMT.TermType → SMT.Term → IO Unit
  /-- Assert a term -/
  assert : SMT.Term → IO Unit
  /-- Check satisfiability -/
  checkSat : IO SMT.Decision
  /-- Check satisfiability with assumptions (check-sat-assuming) -/
  checkSatAssuming : List SMT.Term → IO SMT.Decision
  /-- Get model values for variables -/
  getModel : List String → IO (List (String × String))
  /-- Reset the solver state -/
  reset : IO Unit
```

The implementation will use `SMTDDM.toString` to convert `SMT.Term` to SMT-LIB strings before sending to the solver.

### Key Design Patterns from B3 Verifier

The B3 verifier implementation provides several important patterns that should be followed:

#### 1. Streaming Symbolic Execution (NOT Batch VCG)

Statements are translated and symbolically executed immediately, not batched:
- `assert e` - prove e, then add to solver state (assumes e regardless of proof result)
- `check e` - prove e using push/pop (doesn't affect state)
- `assume e` - add to solver state
- `cover e` (reach in B3) - check satisfiability using push/pop

This allows the solver to learn from asserts, making later checks easier. Key advantage: O(n) not O(n²), solver accumulates lemmas.

#### 2. Assert Does NOT Add to State (Unlike B3)

Critical difference from B3: Strata Core's `assert` is equivalent to B3's `check` - it does NOT modify solver state:
- `assert e` - proof check using push/pop (doesn't affect state)
- `assume e` - add to solver state
- `cover e` - check satisfiability using push/pop

However, during diagnosis, when checking the RHS of a conjunction `A ∧ B`, we DO temporarily assume the LHS `A` to provide context.

#### 3. Proof vs Reachability Checks

Two different check types with different semantics:
- **Proof check** (assert/check): `check-sat(¬e)` - unsat means proved, sat means counterexample
- **Reachability check** (cover/reach): `check-sat(e)` - sat means reachable, unsat means unreachable

The diagnosis strategies differ:
- For proof failures: diagnose all conjuncts
- For reachability failures: stop after first unreachable conjunct (subsequent are trivially unreachable)

#### 4. Push/Pop for Non-Destructive Checks

Use push/pop around checks that shouldn't modify state:
```lean
def prove (state : CoreSMTState) (term : SMT.Term) : IO VerificationReport := do
  state.solver.push
  state.solver.assert (SMT.Term.app .not [term] .bool)
  let decision ← state.solver.checkSat
  state.solver.pop
  return mkResult decision
```

#### 5. Verification Result Types

The B3 verifier distinguishes between:
- **VerificationError**: counterexample (sat), unknown, refuted (unsat when checking reachability)
- **VerificationSuccess**: verified (unsat when proving), reachable (sat), reachabilityUnknown

This distinction is important for diagnosis - "refuted" means provably false, not just unprovable.

#### 6. Path Condition Tracking

Track path conditions (accumulated assumptions) for debugging:
```lean
structure VerificationContext where
  stmt : Statement
  pathCondition : List Expression.Expr  -- Accumulated assertions for debugging
```

This helps users understand what was assumed when a check failed.

### Verification Context

The verification context tracks configuration and accumulated state. The state is returned from verify calls to enable reuse:

```lean
/-- Configuration for CoreSMT verification -/
structure CoreSMTConfig where
  /-- Enable automatic diagnosis of failures -/
  diagnosisEnabled : Bool := true
  /-- Continue verification after errors (accumulate all errors) -/
  accumulateErrors : Bool := true
  /-- Verbosity level for reporting -/
  verbose : VerboseMode := .normal

/-- A context item represents something added to the SMT solver state -/
inductive ContextItem where
  /-- An assumed expression -/
  | assumption : Expression.Expr → ContextItem
  /-- A declared sort (name, arity) -/
  | sortDecl : String → Nat → ContextItem
  /-- A declared function (name, arg types, return type) -/
  | funcDecl : String → List SMT.TermType → SMT.TermType → ContextItem
  /-- A defined function (name, args, return type, body) -/
  | funcDef : String → List (String × SMT.TermType) → SMT.TermType → SMT.Term → ContextItem
  /-- A declared variable (name, type) -/
  | varDecl : String → SMT.TermType → ContextItem
  /-- A defined variable (name, type, value) -/
  | varDef : String → SMT.TermType → SMT.Term → ContextItem

/-- A scope is a list of context items added at the same push level -/
abbrev ContextScope := List ContextItem

/-- Context stack: a stack of scopes, where each scope corresponds to a push level.
    The head of the list is the current (innermost) scope. -/
abbrev ContextStack := List ContextScope

/-- Verification state that can be reused across calls -/
structure CoreSMTState where
  /-- The SMT solver interface -/
  solver : SMTSolverInterface
  /-- Configuration -/
  config : CoreSMTConfig
  /-- Stack of context scopes (for push/pop support) -/
  contextStack : ContextStack
  /-- Accumulated verification results -/
  results : Array VCResult

/-- Create initial state from a solver interface -/
def CoreSMTState.init (solver : SMTSolverInterface) (config : CoreSMTConfig := {}) : CoreSMTState :=
  { solver, config, contextStack := [[]], results := #[] }

/-- Push a new scope onto the context stack -/
def CoreSMTState.push (state : CoreSMTState) : IO CoreSMTState := do
  state.solver.push
  return { state with contextStack := [] :: state.contextStack }

/-- Pop the top scope from the context stack -/
def CoreSMTState.pop (state : CoreSMTState) : IO CoreSMTState := do
  state.solver.pop
  match state.contextStack with
  | [] => return state  -- Should not happen
  | _ :: rest => return { state with contextStack := rest }

/-- Add an item to the current scope -/
def CoreSMTState.addItem (state : CoreSMTState) (item : ContextItem) : CoreSMTState :=
  match state.contextStack with
  | [] => { state with contextStack := [[item]] }
  | scope :: rest => { state with contextStack := (item :: scope) :: rest }

/-- Get all context items (flattened from all scopes) for error reporting -/
def CoreSMTState.allContextItems (state : CoreSMTState) : List ContextItem :=
  state.contextStack.flatten

/-- Verify statements and return updated state with results -/
def verify (state : CoreSMTState) (stmts : List Statement) : IO (CoreSMTState × Array VCResult)
```

### isCoreSMT Predicate

The isCoreSMT predicate characterizes the subset of Core that maps 1-1 with SMT-LIB constructs.

Core's `Statement` type is `Imperative.Stmt Expression Command` where `Command = CmdExt Expression`. The `@match_pattern` abbreviations in `Statement.lean` provide convenient patterns like `Statement.assume`, `Statement.assert`, etc.

```lean
/-- Predicate for statements that map 1-1 with SMT-LIB constructs.
    Uses the @match_pattern abbreviations from Statement.lean -/
def Statement.isCoreSMT : Statement → Bool
  -- Commands with direct SMT-LIB equivalents (using @match_pattern abbreviations):
  | Statement.assume _ _ _ => true        -- maps to SMT assert
  | Statement.assert _ _ _ => true        -- maps to SMT check-sat (negation)
  | Statement.cover _ _ _ => true         -- maps to SMT check-sat
  | Statement.init _ _ _ _ => true        -- maps to SMT define-fun or declare-fun
  | Statement.havoc _ _ => true           -- maps to SMT declare-fun (fresh)
  -- Structured constructs:
  | .block _ stmts _ => stmts.all Statement.isCoreSMT  -- maps to SMT push/pop
  | .funcDecl _ _ => true                 -- maps to SMT declare-fun or define-fun
  -- Constructs WITHOUT direct SMT-LIB equivalents:
  | .ite _ _ _ _ => false                 -- no direct SMT-LIB equivalent
  | .loop _ _ _ _ _ => false              -- no direct SMT-LIB equivalent
  | .goto _ _ => false                    -- no direct SMT-LIB equivalent
  | Statement.call _ _ _ _ => false       -- no direct SMT-LIB equivalent
  | Statement.set _ _ _ => false          -- assignment requires symbolic execution
  | _ => false                            -- catch-all for any other cases

/-- Predicate for expressions that map to SMT terms.
    Abstractions are supported ONLY when immediately applied (translates to SMT let). -/
def Expression.isCoreSMT : Expression.Expr → Bool
  | .const _ _ _ => true
  | .fvar _ _ _ => true
  | .bvar _ _ _ => true  -- bound variables within quantifiers
  | .app _ op args _ => 
      -- Check if this is an immediately applied abstraction
      match op with
      | .abs _ _ _ body => body.isCoreSMT && args.all Expression.isCoreSMT
      | _ => args.all Expression.isCoreSMT
  | .ite _ cond thenE elseE _ => 
      cond.isCoreSMT && thenE.isCoreSMT && elseE.isCoreSMT
  | .quant _ _ _ _ body _ => body.isCoreSMT
  | .abs _ _ _ _ => false  -- Standalone abstractions NOT supported (must be immediately applied)
```

The key insight is that `isCoreSMT` is NOT about "what requires partial evaluation" but about "what has a direct SMT-LIB equivalent". For example:
- `if-then-else` statements don't have a direct SMT-LIB equivalent (SMT has `ite` for expressions, not statements)
- `loop` statements don't have a direct SMT-LIB equivalent
- `goto` statements don't have a direct SMT-LIB equivalent
- `call` statements don't have a direct SMT-LIB equivalent

### Statement Processor

The statement processor handles each CoreSMT statement type. It uses the `@match_pattern` abbreviations from `Statement.lean`.

**Note**: The patterns below assume `Cmd.init` has been extended to support optional RHS (see Prerequisites section). After the extension, `Statement.init` will have signature:
```lean
abbrev Statement.init (name : Expression.Ident) (ty : Expression.Ty) (expr : Option Expression.Expr)
    (md : MetaData Expression := .empty) := ...
```

```lean
/-- Process a single CoreSMT statement -/
def processStatement (state : CoreSMTState) (stmt : Statement) 
    : IO (CoreSMTState × Option VCResult) := do
  if !stmt.isCoreSMT then
    return (state, some <| mkErrorResult "Statement not in CoreSMT subset")
  
  match stmt with
  | Statement.assume label expr _ =>
      -- Add expression to solver state and track in context
      let term ← translateExpr expr
      state.solver.assert term
      let state' := state.addItem (.assumption expr)
      return (state', none)
  
  | Statement.init name ty (some expr) _ =>
      -- Emit define-fun and track in context
      let term ← translateExpr expr
      let smtTy ← translateType ty
      state.solver.defineFun name.name [] smtTy term
      let state' := state.addItem (.varDef name.name smtTy term)
      return (state', none)
  
  | Statement.init name ty none _ =>
      -- Emit declare-fun (unconstrained) and track in context
      let smtTy ← translateType ty
      state.solver.declareFun name.name [] smtTy
      let state' := state.addItem (.varDecl name.name smtTy)
      return (state', none)
  
  | Statement.assert label expr md =>
      -- Proof check using push/pop (does NOT modify solver state)
      let result ← proveCheck state label expr md
      return (state.addResult result, some result)
  
  | Statement.cover label expr md =>
      -- Cover check (reachability)
      let result ← coverCheck state label expr md
      return result
  
  | Statement.havoc name _ =>
      -- Declare fresh unconstrained variable
      let smtTy ← lookupVarType state name
      state.solver.declareFun name.name [] smtTy
      let state' := state.addItem (.varDecl name.name smtTy)
      return (state', none)
  
  | .block label stmts _ =>
      -- Push/pop around block
      let state' ← state.push
      let (state'', results) ← processStatements state' stmts
      let state''' ← state''.pop
      return (state''', results)
  
  | .funcDecl decl _ =>
      -- Function declaration - track in context
      processFuncDecl state decl
  
  | _ => return (state, some <| mkErrorResult "Unexpected statement type")
```

### Expression Translator

The expression translator converts Core expressions to SMT terms. Immediately applied abstractions are translated to SMT `let`:

```lean
/-- Translate a Core expression to an SMT term.
    Returns error for unsupported constructs (e.g., standalone abstractions) -/
def translateExpr (expr : Expression.Expr) : IO (Except String SMT.Term) := do
  if !expr.isCoreSMT then
    return .error "Expression contains unsupported constructs (e.g., standalone abstraction)"
  
  match expr with
  | .const _ c _ => translateConst c
  | .fvar _ name ty => return .ok <| SMT.Term.var ⟨name.name, ← translateType ty⟩
  | .bvar _ idx _ => return .error "Unexpected unbound de Bruijn index in CoreSMT"
  | .app _ op args _ => 
      -- Check for immediately applied abstraction: (λx. body) arg → (let ((x arg)) body)
      match op with
      | .abs _ name ty body => 
          -- Translate to SMT let
          match args with
          | [arg] => do
              let argTerm ← translateExpr arg
              let bodyTerm ← translateExpr body
              match argTerm, bodyTerm with
              | .ok a, .ok b => return .ok <| SMT.Term.let_ name.name a b
              | .error e, _ | _, .error e => return .error e
          | _ => return .error "Abstraction applied to wrong number of arguments"
      | _ => translateApp op args
  | .abs _ _ _ _ => return .error "Standalone abstractions not supported in CoreSMT (must be immediately applied)"
  | .ite _ cond thenE elseE _ => do
      let cond' ← translateExpr cond
      let then' ← translateExpr thenE
      let else' ← translateExpr elseE
      match cond', then', else' with
      | .ok c, .ok t, .ok e => return .ok <| SMT.Term.app .ite [c, t, e] .bool
      | .error e, _, _ | _, .error e, _ | _, _, .error e => return .error e
  | .quant _ qk vars trigger body _ =>
      translateQuantifier qk vars trigger body
```

### Diagnosis Engine

The diagnosis engine identifies root causes of verification failures:

```lean
/-- Diagnosis result for a failed verification -/
structure DiagnosedFailure where
  /-- The sub-expression that failed -/
  expression : Expression.Expr
  /-- Whether the failure is refuted (provably false) vs unprovable -/
  isRefuted : Bool
  /-- The verification result for this sub-expression -/
  result : VCResult

/-- Diagnosis result containing all diagnosed failures -/
structure DiagnosisResult where
  /-- The original failed check -/
  originalCheck : VCResult
  /-- List of diagnosed sub-failures -/
  diagnosedFailures : List DiagnosedFailure

/-- Diagnose a failed verification by splitting conjunctions -/
partial def diagnoseFailure (state : CoreSMTState) (expr : Expression.Expr) 
    (isReachCheck : Bool) : IO DiagnosisResult := do
  -- Check if expression is a conjunction
  match splitConjunction expr with
  | none => 
      -- Atomic expression - check if refuted
      let isRefuted ← checkRefuted state expr
      return { originalCheck := ..., diagnosedFailures := [{ expression := expr, isRefuted, ... }] }
  | some (lhs, rhs) =>
      -- Diagnose left conjunct
      let lhsResult ← diagnoseConjunct state lhs isReachCheck
      
      -- For cover checks, stop after first unreachable
      if isReachCheck && lhsResult.any (·.isRefuted) then
        return { originalCheck := ..., diagnosedFailures := lhsResult }
      
      -- Diagnose right conjunct with left as context
      state.solver.push
      let lhsTerm ← translateExpr lhs
      state.solver.assert lhsTerm
      let rhsResult ← diagnoseConjunct state rhs isReachCheck
      state.solver.pop
      
      return { originalCheck := ..., diagnosedFailures := lhsResult ++ rhsResult }

/-- Check if an expression is provably false (refuted) -/
def checkRefuted (state : CoreSMTState) (expr : Expression.Expr) : IO Bool := do
  state.solver.push
  let term ← translateExpr expr
  state.solver.assert term
  let decision ← state.solver.checkSat
  state.solver.pop
  return decision == .unsat
```

## Data Models

### Verification Results

The verifier reuses existing Core types with extensions - adding a "refuted" outcome and optional diagnosis:

```lean
-- Extended from Core.Verifier to include "refuted" for provably false assertions
inductive Outcome where
  | pass                        -- Proved (unsat when checking negation)
  | fail                        -- Counterexample found (sat when checking negation)
  | unknown                     -- Solver couldn't determine
  | refuted                     -- NEW: Provably false (unsat when checking the assertion itself)
  | implementationError (e : String)

-- Extended from Core.Verifier to include optional diagnosis
structure VCResult where
  obligation : ProofObligation Expression
  smtResult : SMT.Result := .unknown
  result : Outcome := .unknown
  estate : EncoderState := EncoderState.init
  verbose : VerboseMode := .normal
  diagnosis : Option DiagnosisResult := none  -- NEW: Optional diagnosis for failed checks
```

The "refuted" outcome is important because it distinguishes between:
- `fail` - The assertion might not hold (counterexample found, but could be spurious)
- `refuted` - The assertion is provably ALWAYS false (we can prove ¬e holds)

This distinction helps users understand whether they have a logic error (refuted) vs a missing assumption (fail).

### SMT Types

```lean
-- From SMT dialect (reused)
inductive TermType where
  | bool
  | int
  | real
  | string
  | bitvec (n : Nat)
  | option (ty : TermType)
  | constr (name : String) (args : List TermType)

inductive Decision where
  | sat
  | unsat
  | unknown
```

## Correctness Properties

*A property is a characteristic or behavior that should hold true across all valid executions of a system—essentially, a formal statement about what the system should do. Properties serve as the bridge between human-readable specifications and machine-verifiable correctness guarantees.*

### Property 1: Assume adds to solver state
*For any* CoreSMT assume statement with expression `e`, after processing the statement, the SMT solver state SHALL contain `e` as an assertion.
**Validates: Requirements 1.1**

### Property 2: Init with expression emits define-fun
*For any* CoreSMT init statement with variable `x`, type `T`, and expression `e`, processing SHALL emit an SMT define-fun command for `x` with body `e`.
**Validates: Requirements 1.2**

### Property 3: Init without expression emits declare-fun
*For any* CoreSMT init statement with variable `x` and type `T` but no expression, processing SHALL emit an SMT declare-fun command for `x`.
**Validates: Requirements 1.3**

### Property 4: Assert performs proof check without state modification
*For any* CoreSMT assert statement with expression `e`, processing SHALL perform a proof check (check-sat of ¬e) using push/pop, WITHOUT modifying the solver state afterward.
**Validates: Requirements 1.4**

### Property 5: Cover performs reachability check
*For any* CoreSMT cover statement with expression `e`, processing SHALL perform a reachability check (check-sat of `e`) where sat means reachable and unsat means unreachable.
**Validates: Requirements 1.5**

### Property 6: Block emits push/pop and processes inner statements
*For any* CoreSMT block statement containing statements `[s1, s2, ...]`, processing SHALL emit push before, process each inner statement sequentially, and emit pop after.
**Validates: Requirements 1.6, 6.2**

### Property 7: Function declaration without body emits declare-fun
*For any* function declaration without a body, processing SHALL emit an SMT declare-fun command with the function's signature.
**Validates: Requirements 1.7**

### Property 8: Function declaration with body emits define-fun
*For any* function declaration with a body, processing SHALL emit an SMT define-fun command (or equivalent axiom) with the function's definition.
**Validates: Requirements 1.8**

### Property 9: Function calls translate to SMT applications
*For any* expression containing a function call `f(args)`, translation SHALL produce an SMT function application `(f args)`.
**Validates: Requirements 1.9**

### Property 10: Non-CoreSMT input returns error
*For any* statement or expression that does not satisfy the isCoreSMT predicate, the verifier SHALL return Except.error.
**Validates: Requirements 1.10, 2.3**

### Property 11: VCResult contains correct information
*For any* verification check (assert, cover), the resulting VCResult SHALL contain the original obligation, the SMT result, and the interpreted outcome.
**Validates: Requirements 1.12**

### Property 12: Error accumulation collects all errors
*For any* list of statements where multiple verification checks fail, if error accumulation is enabled, the verifier SHALL return results for ALL checks (not just the first failure).
**Validates: Requirements 3.3**

### Property 13: Diagnosis applies when enabled and proof fails
*For any* failed proof check where diagnosis is enabled, the verifier SHALL apply diagnosis strategies to identify root causes.
**Validates: Requirements 4.2**

### Property 14: Conjunction splitting diagnoses both conjuncts
*For any* failed proof check on a conjunction `A ∧ B`, diagnosis SHALL recursively check both `A` and `B` to identify which conjunct(s) fail.
**Validates: Requirements 4.3**

### Property 15: Right conjunct diagnosis assumes left conjunct
*For any* conjunction `A ∧ B` being diagnosed, when checking the right conjunct `B`, the left conjunct `A` SHALL be temporarily added to the solver state as context.
**Validates: Requirements 4.4**

### Property 16: Refuted detection distinguishes provably false
*For any* sub-expression that is provably false (SMT returns unsat when the expression is asserted), the diagnosis SHALL mark it as "refuted" rather than just "unprovable".
**Validates: Requirements 4.5**

### Property 17: Cover diagnosis stops after first unreachable
*For any* failed cover check on a conjunction, diagnosis SHALL stop after finding the first unreachable conjunct (since subsequent conjuncts are trivially unreachable).
**Validates: Requirements 4.6**

### Property 18: Diagnosed failures include context
*For any* diagnosed failure, the result SHALL include the sub-expression, whether it's refuted, and the path conditions for debugging.
**Validates: Requirements 4.7**

### Property 19: Refuted outcome in VCResult
*For any* assertion that is provably always false (check-sat of the assertion itself returns unsat), the VCResult SHALL have outcome "refuted" to distinguish from "fail" (counterexample found but assertion might hold on other paths).
**Validates: Requirements 3.2**

### Property 20: Equivalent results via B3 to Core conversion
*For any* B3 verifier test, verification via B3→Core→CoreSMT SHALL produce equivalent results to the original B3→SMT direct path.
**Validates: Requirements 5.5**

### Property 21: State reuse preserves correctness
*For any* state returned from a verify call, using that state for subsequent verify calls SHALL produce correct results as if verification started fresh with all prior statements.
**Validates: Requirements 6.2, 6.3**

### Property 22: Prelude state reuse
*For any* prelude processed via `processPrelude`, the resulting state SHALL be reusable for multiple subsequent `verify` calls, each producing correct results as if the prelude were processed fresh.
**Validates: Requirements 6.5, 6.6, 6.7**

### Property 23: Push/pop preserves solver correctness
*For any* sequence of push/pop operations, the solver state after pop SHALL be equivalent to the state before the corresponding push.
**Validates: Requirements 7.6**

### Property 24: Model extraction on sat/unknown
*For any* check-sat that returns sat or unknown, the solver interface SHALL support extracting model values for declared variables.
**Validates: Requirements 7.7**
**Validates: Requirements 7.7**

## Error Handling

### Error Types

1. **Non-CoreSMT Error**: Statement or expression not in the isCoreSMT subset
2. **Translation Error**: Failed to translate expression to SMT
3. **Solver Error**: SMT solver returned an error
4. **Implementation Error**: Internal error in the verifier

### Error Accumulation

When `accumulateErrors` is enabled:
- Verification continues after errors
- All errors are collected and returned
- Useful for batch verification of multiple assertions

When `accumulateErrors` is disabled:
- Verification stops on first error
- Useful for interactive debugging

### Error Context

Each error includes:
- The statement/expression that caused the error
- The path conditions at the point of failure
- Source location metadata (if available)

## Testing Strategy

### Unit Tests

Unit tests verify specific examples and edge cases:

1. **Statement handling**: Each statement type (assume, init, assert, check, cover, block, funcDecl)
2. **Expression translation**: Constants, variables, operations, quantifiers
3. **Error cases**: Non-CoreSMT inputs, translation failures
4. **Diagnosis**: Conjunction splitting, refuted detection

### Property-Based Tests

Property tests verify universal properties across generated inputs. Each property test runs minimum 100 iterations.

**Testing Framework**: Use Plausible for property-based testing in Lean.

**Test Organization**:
- Tests use DDM syntax to construct Strata Core AST
- Tests are placed in `StrataTest/Languages/Core/CoreSMTVerifier/`
- Each property from the Correctness Properties section has a corresponding test

### Test Migration via B3 to Core Conversion

Instead of rewriting B3 tests in Core syntax, we keep the B3 syntax and add a B3 AST → Core AST converter. This allows:
- Existing B3 tests to remain unchanged
- Validation that CoreSMT produces equivalent results to the original B3 verifier
- Clean removal of the direct B3→SMT path once migration is complete

#### B3 to Core Converter

```lean
/-- Convert B3 AST to Core AST -/
namespace B3ToCore

/-- Convert B3 expression to Core expression -/
def convertExpr (expr : B3AST.Expression M) : Core.Expression.Expr :=
  match expr with
  | .literal _ (.intLit _ n) => .const () (.intConst n) none
  | .literal _ (.boolLit _ b) => .const () (.boolConst b) none
  | .id _ idx => .bvar () idx none  -- de Bruijn index
  | .binaryOp _ op lhs rhs => 
      let lhs' := convertExpr lhs
      let rhs' := convertExpr rhs
      convertBinaryOp op lhs' rhs'
  | .unaryOp _ op arg => 
      let arg' := convertExpr arg
      convertUnaryOp op arg'
  | .ite _ cond thn els =>
      .ite () (convertExpr cond) (convertExpr thn) (convertExpr els) none
  | .functionCall _ name args =>
      let args' := args.val.toList.map convertExpr
      -- Create function application
      mkFunctionApp name.val args'
  | .quantifierExpr _ qkind vars patterns body =>
      convertQuantifier qkind vars patterns body
  | .letExpr _ var value body =>
      -- Convert to immediately applied abstraction
      let value' := convertExpr value
      let body' := convertExpr body
      .app () (.abs () ⟨var.val, .public⟩ .int body') [value'] none
  | .labeledExpr _ _ expr => convertExpr expr

/-- Convert B3 statement to Core statement -/
def convertStmt (stmt : B3AST.Statement M) : Core.Statement :=
  match stmt with
  | .check m expr => 
      -- B3 check → Core assert (proof check without state modification)
      Statement.assert "" (convertExpr expr)
  | .assert m expr => 
      -- B3 assert → Core assert (same semantics in Core)
      Statement.assert "" (convertExpr expr)
  | .assume _ expr => 
      Statement.assume "" (convertExpr expr)
  | .reach m expr => 
      -- B3 reach → Core cover
      Statement.cover "" (convertExpr expr)
  | .blockStmt _ stmts =>
      .block "" (stmts.val.toList.map convertStmt) {}

/-- Convert B3 function declaration to Core function declaration -/
def convertFuncDecl (decl : B3AST.FunctionDecl M) : Core.Statement :=
  let inputs := decl.params.val.toList.map (fun p => (⟨p.name.val, .public⟩, convertType p.ty))
  let body := decl.body.map convertExpr
  .funcDecl { 
    name := ⟨decl.name.val, .public⟩
    inputs := inputs
    output := convertType decl.returnType
    body := body
    axioms := []
  } {}

end B3ToCore
```

#### Verification Pipeline

```
B3 Program (DDM syntax)
      ↓
   Parse (existing B3 DDM parser)
      ↓
  B3 AST
      ↓
B3ToCore.convert (NEW)
      ↓
  Core AST (Statements)
      ↓
CoreSMT_Verifier.verify (NEW)
      ↓
  VCResult (with optional diagnosis)
```

#### Test Example

```lean
-- Existing B3 test - NO CHANGES NEEDED
#eval testB3ViaCoreVerification $ #strata program B3CST;
  function f(x : int) : int { x + 1 }
  procedure test() {
    check 8 == 8 && f(5) == 6
  }
#end

-- The test harness:
-- 1. Parses B3 DDM syntax to B3 AST
-- 2. Converts B3 AST to Core AST via B3ToCore
-- 3. Verifies Core AST via CoreSMT_Verifier
-- 4. Returns VCResult with diagnosis
```

#### Migration Completion

Once all B3 tests pass through the B3→Core→CoreSMT pipeline:
1. Remove `Strata/Languages/B3/Verifier/Expression.lean` (B3→SMT conversion)
2. Remove `Strata/Languages/B3/Verifier/Statements.lean` (B3 statement processing)
3. Keep `Strata/Languages/B3/Verifier/State.lean` types if needed for compatibility
4. Update B3 verifier entry point to use B3→Core→CoreSMT pipeline

### Integration Tests

Integration tests verify end-to-end behavior:

1. **B3 via Core verification**: All B3 tests pass through B3→Core→CoreSMT pipeline
2. **Solver backends**: Test with cvc5 and Z3
3. **Diagnosis**: Full diagnosis workflow on complex assertions
