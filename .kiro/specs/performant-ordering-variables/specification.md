# Performant Ordering Variable Numbering Specification

## Executive Summary

This specification describes the migration of Strata's variable representation from the current system to **Performant Ordering** - a unified variable numbering scheme using globally unique natural numbers. This change affects both lambda calculus (bound variables) and imperative layer (free variables), replacing all relative indexing schemes with a single, transformation-friendly approach.

**Key Change:** All variables (lambda-bound and imperative-declared) are identified by unique natural numbers assigned from a global counter, with no relative counting or context-dependent indexing.

## Table of Contents

1. [Introduction](#introduction)
2. [Glossary](#glossary)
3. [Requirements](#requirements)
4. [Architecture](#architecture)
5. [Design](#design)
6. [Implementation Strategy](#implementation-strategy)
7. [Testing Strategy](#testing-strategy)
8. [Migration Plan](#migration-plan)

---

## Introduction

### Current State

Strata currently uses different variable representation schemes across its layers:
- **Lambda calculus**: Uses De Bruijn indices for bound variables (bvar) - relative counting from binding site
- **Imperative layer**: Uses string-based identifiers for free variables (fvar)
- **Mixed approach**: Leads to complex index shifting, weakening, and lifting operations

### Problems with Current Approach

1. **Complexity**: Index shifting logic is error-prone and difficult to prove correct
2. **Transformation friction**: Variables change identity during transformations
3. **Dual reasoning**: Different proof strategies for lambda-bound vs imperative variables
4. **Boundary cases**: Complex interactions between bvar and fvar
5. **Canonicity overhead**: De Bruijn requires normalization, but Strata prioritizes semantic equivalence

### Proposed Solution: Performant Ordering

**Core Concept**: All variables are identified by globally unique natural numbers assigned from a monotonically increasing counter.


**Benefits**:
- **Simplicity**: No index shifting, no relative counting
- **Stability**: Variables maintain identity across all transformations
- **Unified reasoning**: Single proof strategy for all variables
- **Transformation-friendly**: Fresh variable generation is trivial and local
- **Strata-optimized**: Perfect for multi-stage transformation pipelines

**Trade-off Accepted**: Loss of canonical representation (alpha-equivalent terms may differ syntactically), but semantic equivalence is what matters for verification.

---

## Glossary

- **Performant Ordering**: Variable numbering scheme using globally unique natural numbers
- **nextFree**: Counter representing the next available fresh variable number
- **Program α**: Generic program structure containing content of type α and a nextFree counter
- **FreshM**: State monad for generating fresh variable numbers
- **bvar**: Bound variable (lambda-bound, quantifier-bound) - now uses Performant Ordering
- **fvar**: Free variable (imperative-declared) - now uses Performant Ordering
- **LExpr**: Lambda expressions in the Lambda dialect
- **Cmd**: Commands in the Imperative dialect
- **VarContext**: Mapping from variable numbers to metadata (name, type) for display/debugging
- **Unified numbering**: Single numbering space shared by both bvar and fvar

---

## Requirements

### Requirement 1: Unified Variable Representation

**User Story**: As a language designer, I want all variables to use a single numbering scheme, so that there's no distinction between lambda-bound and imperative variable numbering.

#### Acceptance Criteria

1.1. WHEN a variable is represented in the AST, THE System SHALL use a natural number as its unique identifier

1.2. WHEN a lambda parameter is declared, THE System SHALL assign it a unique number from nextFree

1.3. WHEN an imperative variable is declared, THE System SHALL assign it a unique number from nextFree

1.4. WHEN a quantifier binds a variable, THE System SHALL assign it a unique number from nextFree

1.5. WHERE variables are used, THE System SHALL reference them by their assigned number


### Requirement 2: Program Structure with Fresh Counter

**User Story**: As a compiler developer, I want programs to track the next available variable number, so that fresh variable generation is guaranteed to be unique.

#### Acceptance Criteria

2.1. WHEN a Program is defined, THE System SHALL include a nextFree field of type Nat

2.2. WHEN a Program is created, THE System SHALL initialize nextFree to 0 (or to the next available number if continuing from a previous context)

2.3. WHEN a fresh variable is needed, THE System SHALL use the current nextFree value and increment it

2.4. WHERE multiple types of variables exist (lambda-bound, imperative, quantifier-bound), THE System SHALL use the same nextFree counter for all of them

2.4. WHERE all variables in a program, THE System SHALL maintain the invariant that all variable numbers are strictly less than nextFree

### Requirement 3: Fresh Variable Generation

**User Story**: As a transformation developer, I want to generate fresh variables using a state monad, so that uniqueness is guaranteed by construction.

#### Acceptance Criteria

3.1. WHEN generating a fresh variable, THE System SHALL provide a FreshM monad that returns the current nextFree and increments it

3.2. WHEN multiple fresh variables are needed, THE System SHALL thread the state through all generations

3.3. WHEN a transformation completes, THE System SHALL return an updated Program with the new nextFree value

3.4. WHERE fresh variable generation occurs, THE System SHALL guarantee that the returned number was not previously used in the program

### Requirement 4: Lambda Calculus Operations

**User Story**: As a lambda calculus implementer, I want substitution and beta reduction to work without index shifting, so that operations are simpler and proofs are easier.

#### Acceptance Criteria

4.1. WHEN performing beta reduction (λ x₄₂. body) arg, THE System SHALL substitute all occurrences of variable 42 in body with arg, without any index adjustment

4.2. WHEN performing substitution body[x₄₂ := arg], THE System SHALL replace all occurrences of variable 42 with arg, without shifting any other variables

4.3. WHEN performing alpha conversion, THE System SHALL generate a fresh variable number and replace the old parameter number with the new one, without any index adjustment

4.4. WHERE lambda expressions are evaluated, THE System SHALL NOT perform any index shifting, weakening, or lifting operations


### Requirement 5: Imperative Operations

**User Story**: As an imperative language implementer, I want variable declarations and assignments to use unique numbers, so that shadowing is impossible and variable tracking is unambiguous.

#### Acceptance Criteria

5.1. WHEN an init command declares a variable, THE System SHALL assign it a unique number from nextFree

5.2. WHEN a set command modifies a variable, THE System SHALL reference it by its unique number

5.3. WHEN a havoc command randomizes a variable, THE System SHALL reference it by its unique number

5.4. WHERE multiple variables with the same display name exist, THE System SHALL distinguish them by their unique numbers

5.5. WHEN inlining procedures, THE System SHALL generate fresh numbers for all parameters and locals

### Requirement 6: Pretty Printing and Display

**User Story**: As a developer debugging programs, I want variable numbers to be resolved to readable names, so that output is human-friendly.

#### Acceptance Criteria

6.1. WHEN displaying a variable, THE System SHALL resolve its number to a display name using VarContext

6.2. WHEN a variable number cannot be resolved, THE System SHALL display it as %N (e.g., %42)

6.3. WHEN multiple variables share the same display name, THE System SHALL disambiguate using @N suffix (e.g., x, x@1, x@2)

6.4. WHERE shadowing does not occur, THE System SHALL display variables with their plain names (no suffix)

6.5. WHEN formatting expressions, THE System SHALL use VarContext to make output readable

### Requirement 7: Scope and Shadowing

**User Story**: As a language designer, I want shadowing to be impossible by construction, so that variable references are always unambiguous.

#### Acceptance Criteria

7.1. WHEN a new variable is declared, THE System SHALL assign it a unique number that has never been used

7.2. WHERE two variables have the same display name, THE System SHALL distinguish them by their unique numbers

7.3. WHEN a variable goes out of scope, THE System SHALL NOT reuse its number

7.4. WHERE variable lookup occurs, THE System SHALL use the unique number, not the display name


### Requirement 8: Transformation Correctness

**User Story**: As a verification engineer, I want transformations to preserve program semantics, so that verification results are trustworthy.

#### Acceptance Criteria

8.1. WHEN a transformation generates fresh variables, THE System SHALL prove that the fresh numbers are not in the original program

8.2. WHEN a transformation preserves variables, THE System SHALL prove that variable numbers remain unchanged

8.3. WHEN a transformation performs substitution, THE System SHALL prove that semantics are preserved

8.4. WHERE transformations compose, THE System SHALL prove that the composition preserves semantics

8.5. WHEN a transformation completes, THE System SHALL prove that all variables in the result are below the new nextFree

### Requirement 9: Type System Integration

**User Story**: As a type system maintainer, I want type checking to work with variable numbers, so that type safety is preserved.

#### Acceptance Criteria

9.1. WHEN type checking a variable reference, THE System SHALL look up its type using the variable number

9.2. WHEN a variable is declared, THE System SHALL associate its number with its type

9.3. WHEN type checking lambda expressions, THE System SHALL track parameter types by their numbers

9.4. WHERE type environments are maintained, THE System SHALL map variable numbers to types

### Requirement 10: Evaluation and Semantics

**User Story**: As a semantics implementer, I want evaluation to work with variable numbers, so that runtime behavior is correct.

#### Acceptance Criteria

10.1. WHEN evaluating a variable reference, THE System SHALL look up its value using the variable number

10.2. WHEN a variable is assigned, THE System SHALL update the value at its number

10.3. WHEN evaluating lambda application, THE System SHALL substitute using variable numbers without shifting

10.4. WHERE evaluation environments are maintained, THE System SHALL map variable numbers to values


### Requirement 11: SMT Backend Integration

**User Story**: As a verification backend developer, I want SMT encoding to generate unique variable names, so that verification conditions are correct.

#### Acceptance Criteria

11.1. WHEN encoding a variable to SMT, THE System SHALL generate a unique SMT identifier

11.2. WHEN multiple variables share a display name, THE System SHALL use @N suffixes in SMT (e.g., x, x@1, x@2)

11.3. WHEN encoding expressions, THE System SHALL resolve variable numbers to SMT identifiers

11.4. WHERE SMT variable names are generated, THE System SHALL maintain a mapping from variable numbers to SMT identifiers

### Requirement 12: Compilation and Testing

**User Story**: As a project maintainer, I want the refactored code to compile and pass all tests, so that the system remains functional.

#### Acceptance Criteria

12.1. WHEN all changes are complete, THE System SHALL compile without errors using `lake build`

12.2. WHEN tests are run, THE System SHALL pass all existing tests using `lake test`

12.3. WHERE proofs are affected, THE System SHALL restore all proofs to working state

12.4. WHEN the migration is complete, THE System SHALL have no remaining `sorry` placeholders

---

## Architecture

### High-Level Overview

```
┌─────────────────────────────────────────────────────────────┐
│                     Program Structure                        │
│  ┌────────────────────────────────────────────────────────┐ │
│  │  structure Program (α : Type) where                    │ │
│  │    content : α                                         │ │
│  │    nextFree : Nat                                      │ │
│  └────────────────────────────────────────────────────────┘ │
└─────────────────────────────────────────────────────────────┘
                              │
                              ├─────────────────────────────────┐
                              │                                 │
                              ▼                                 ▼
┌──────────────────────────────────────┐    ┌──────────────────────────────────┐
│      Lambda Calculus Layer           │    │     Imperative Layer             │
│  ┌────────────────────────────────┐  │    │  ┌────────────────────────────┐ │
│  │  LExpr:                        │  │    │  │  Cmd:                      │ │
│  │    bvar (index: Nat)           │  │    │  │    init (name: String)     │ │
│  │    abs (param: Nat) (body)     │  │    │  │    set (var: Nat) (expr)   │ │
│  │    app (fn) (arg)              │  │    │  │    havoc (var: Nat)        │ │
│  │    fvar (index: Nat)           │  │    │  └────────────────────────────┘ │
│  └────────────────────────────────┘  │    └──────────────────────────────────┘
└──────────────────────────────────────┘
                              │
                              ▼
┌─────────────────────────────────────────────────────────────┐
│                   Fresh Variable Monad                       │
│  ┌────────────────────────────────────────────────────────┐ │
│  │  def FreshM (α : Type) : Type := StateM Nat α         │ │
│  │                                                        │ │
│  │  def freshVar : FreshM Nat := do                      │ │
│  │    let n ← get                                        │ │
│  │    set (n + 1)                                        │ │
│  │    return n                                           │ │
│  └────────────────────────────────────────────────────────┘ │
└─────────────────────────────────────────────────────────────┘
```


### Key Architectural Principles

1. **Unified Numbering**: All variables (bvar, fvar, parameters, locals) share the same numbering space
2. **Global Uniqueness**: Each variable number is used exactly once across the entire program
3. **Monotonic Counter**: nextFree only increases, never decreases
4. **Stable Identity**: Variable numbers never change during transformations
5. **Display Separation**: Variable numbers (for semantics) are separate from display names (for humans)

### Component Relationships

```
Program
  ├── content (AST with variable numbers)
  └── nextFree (fresh variable counter)

VarContext (for display/debugging)
  └── Map Nat (String × Type)  -- number → (display name, type)

FreshM Monad (for transformations)
  └── StateM Nat  -- threads nextFree through operations

Evaluation Environment
  └── Map Nat Value  -- number → runtime value

Type Environment
  └── Map Nat Type  -- number → type
```

---

## Design

### 1. Program Structure

All program entry points (expressions, statements, procedures, etc.) are wrapped in a `Program` structure:

```lean
structure Program (α : Type) where
  content : α
  nextFree : Nat

namespace Program

def empty (content : α) : Program α :=
  ⟨content, 0⟩

def withFreshCounter (content : α) (nextFree : Nat) : Program α :=
  ⟨content, nextFree⟩

-- Primary invariant: all variables in content are below nextFree
def wellFormed (p : Program α) : Prop :=
  ∀ v ∈ allVars p.content, v < p.nextFree

end Program
```


### 2. Fresh Variable Monad

```lean
def FreshM (α : Type) : Type := StateM Nat α

namespace FreshM

def freshVar : FreshM Nat := do
  let n ← get
  set (n + 1)
  return n

def freshVars (count : Nat) : FreshM (List Nat) := do
  let mut vars := []
  for _ in [0:count] do
    vars := (← freshVar) :: vars
  return vars.reverse

def run (m : FreshM α) (initialNextFree : Nat) : α × Nat :=
  m.run initialNextFree

def runProgram (m : FreshM α) (p : Program β) : Program α :=
  let (content, nextFree) := m.run p.nextFree
  ⟨content, nextFree⟩

end FreshM
```

**Key Lemma**:
```lean
theorem freshVar_is_fresh (s : Nat) :
  let (n, s') := freshVar.run s
  n = s ∧ s' = s + 1 ∧ n < s'
```

### 3. Lambda Calculus with Performant Ordering

#### LExpr Definition

```lean
inductive LExpr (T : LExprParamsT) : Type where
  | bvar (m : T.base.Metadata) (index : Nat) (hint : String) (ty : Option T.TypeType)
  | fvar (m : T.base.Metadata) (index : Nat) (hint : String) (ty : Option T.TypeType)
  | abs (m : T.base.Metadata) (param : Nat) (hint : String) (body : LExpr T) (ty : Option T.TypeType)
  | app (m : T.base.Metadata) (fn : LExpr T) (arg : LExpr T) (ty : Option T.TypeType)
  | quant (m : T.base.Metadata) (kind : QuantKind) (vars : List (Nat × String)) 
          (body : LExpr T) (ty : Option T.TypeType)
  -- ... other constructors
```

**Key Changes**:
- `bvar` uses `Nat` for unique identity + `String` hint for display
- `fvar` uses `Nat` for unique identity + `String` hint for display
- `abs` stores parameter number + hint for the parameter name
- `quant` stores list of (number, hint) pairs for bound variables

**Design Principle**: Every variable node stores both:
1. **Semantic identity** (Nat) - used for all operations (substitution, lookup, etc.)
2. **Display hint** (String) - used only for pretty printing and debugging


#### Substitution (Simplified)

```lean
def substitute (e : LExpr T) (var : Nat) (replacement : LExpr T) : LExpr T :=
  match e with
  | .bvar m index ty => if index == var then replacement else e
  | .fvar m index ty => if index == var then replacement else e
  | .abs m param body ty => 
      .abs m param (substitute body var replacement) ty
  | .app m fn arg ty =>
      .app m (substitute fn var replacement) (substitute arg var replacement) ty
  | .quant m kind vars body ty =>
      .quant m kind vars (substitute body var replacement) ty
  -- ... other cases
```

**No index shifting needed!** Simple replacement throughout.

#### Beta Reduction (Simplified)

```lean
def betaReduce (e : LExpr T) : LExpr T :=
  match e with
  | .app _ (.abs _ param body _) arg _ =>
      substitute body param arg
  | _ => e
```

**No index adjustment!** Just substitute the parameter number with the argument.

#### Alpha Conversion (Simplified)

```lean
def alphaConvert (abs : LExpr T) : FreshM (LExpr T) :=
  match abs with
  | .abs m param body ty => do
      let newParam ← freshVar
      let newBody := substitute body param (.bvar m newParam ty)
      return .abs m newParam newBody ty
  | _ => return abs
```

**No index adjustment!** Just generate a fresh number and substitute.

### 4. Imperative Layer with Performant Ordering

#### Cmd Definition

```lean
inductive Cmd (P : PureExpr) : Type where
  | init (hint : String) (var : Nat) (ty : P.Ty) (e : Option P.Expr) (md : MetaData P := .empty)
  | set (var : Nat) (e : P.Expr) (md : MetaData P := .empty)
  | havoc (var : Nat) (md : MetaData P := .empty)
  | assert (label : String) (b : P.Expr) (md : MetaData P := .empty)
  | assume (label : String) (b : P.Expr) (md : MetaData P := .empty)
```

**Key Points**:
- `init` stores both hint (String) for display AND var (Nat) for semantic identity
- `init` has optional expression: `some e` for initialized, `none` for havoc
- `set` and `havoc` reference variables by number only (hint is in VarContext)
- Variable numbers are assigned when `init` is executed
- **All constructors have `md : MetaData P` parameter** with default `.empty`

**Rationale for Optional Init**:
- `init "x" 42 ty (some e)` - declares variable 42 with initial value e
- `init "x" 42 ty none` - declares variable 42 with havoc/uninitialized value
- Eliminates pattern of `init` followed by immediate `havoc`
- More concise and clearer intent

**Design Principle**: 
- Declaration nodes (`init`, `abs`, `quant`) store hints directly
- Reference nodes (`bvar`, `fvar`, `set`, `havoc`) use numbers only
- VarContext maintains the mapping for display purposes
- Metadata is preserved throughout all operations


#### Variable Context for Display

```lean
structure VarContext (P : PureExpr) where
  vars : Map Nat (String × P.Ty)  -- number → (display name, type)

namespace VarContext

def empty : VarContext P := ⟨Map.empty⟩

def insert (ctx : VarContext P) (num : Nat) (name : String) (ty : P.Ty) : VarContext P :=
  ⟨ctx.vars.insert num (name, ty)⟩

def lookup (ctx : VarContext P) (num : Nat) : Option (String × P.Ty) :=
  ctx.vars.find? num

def lookupName (ctx : VarContext P) (num : Nat) : Option String :=
  (ctx.lookup num).map (·.1)

def lookupType (ctx : VarContext P) (num : Nat) : Option P.Ty :=
  (ctx.lookup num).map (·.2)

end VarContext
```

#### Evaluation with Performant Ordering

```lean
def Cmd.eval [EC : EvalContext P S] (σ : S) (c : Cmd P) : Cmd P × S :=
  match c with
  | .init name ty (some e) md => do
      let varNum := EC.nextVar σ
      let e := EC.eval σ e
      let σ := EC.addVar σ varNum ty e
      let σ := EC.incrementNextVar σ
      return (.init name ty (some e) md, σ)
  
  | .init name ty none md => do
      let varNum := EC.nextVar σ
      let (e, σ) := EC.genFreeVar σ ty
      let σ := EC.addVar σ varNum ty e
      let σ := EC.incrementNextVar σ
      return (.init name ty none md, σ)
  
  | .set varNum e md =>
      match EC.lookupVar σ varNum with
      | none => return (c, EC.updateError σ (.VarNotFound varNum))
      | some (ty, _) =>
          let e := EC.eval σ e
          let σ := EC.updateVar σ varNum ty e
          return (.set varNum e md, σ)
  
  | .havoc varNum md =>
      match EC.lookupVar σ varNum with
      | none => return (c, EC.updateError σ (.VarNotFound varNum))
      | some (ty, _) =>
          let (e, σ) := EC.genFreeVar σ ty
          let σ := EC.updateVar σ varNum ty e
          return (.havoc varNum md, σ)
```


### 5. Pretty Printing

```lean
def formatVar (ctx : VarContext P) (varNum : Nat) : String :=
  match ctx.lookupName varNum with
  | none => s!"%{varNum}"
  | some name =>
      if name.isEmpty then s!"%{varNum}"
      else
        -- Count how many other variables share this name
        let sameNameVars := ctx.vars.toList.filter (fun (_, (n, _)) => n == name)
        if sameNameVars.length == 1 then name
        else
          -- Find position of this var among same-named vars
          let sorted := sameNameVars.map (·.1) |>.sort
          let pos := sorted.indexOf varNum
          s!"{name}@{pos}"

def formatCmd (ctx : VarContext P) (c : Cmd P) : String :=
  match c with
  | .init name ty (some e) _ =>
      s!"init ({name} : {ty}) := {formatExpr ctx e}"
  | .init name ty none _ =>
      s!"init ({name} : {ty})"
  | .set varNum e _ =>
      s!"{formatVar ctx varNum} := {formatExpr ctx e}"
  | .havoc varNum _ =>
      s!"havoc {formatVar ctx varNum}"
  | .assert label b _ =>
      s!"assert {label}: {formatExpr ctx b}"
  | .assume label b _ =>
      s!"assume {label}: {formatExpr ctx b}"
```

### 6. SMT Encoding

```lean
structure SMTContext where
  varNames : Map Nat String  -- variable number → unique SMT name
  nameCounters : Map String Nat  -- base name → occurrence count

namespace SMTContext

def empty : SMTContext := ⟨Map.empty, Map.empty⟩

def addVar (ctx : SMTContext) (varNum : Nat) (baseName : String) : SMTContext × String :=
  let counter := ctx.nameCounters.findD baseName 0
  let smtName := if counter == 0 then baseName else s!"{baseName}@{counter}"
  let ctx' := {
    varNames := ctx.varNames.insert varNum smtName,
    nameCounters := ctx.nameCounters.insert baseName (counter + 1)
  }
  (ctx', smtName)

def lookupVar (ctx : SMTContext) (varNum : Nat) : Option String :=
  ctx.varNames.find? varNum

end SMTContext
```


### 7. Key Invariants

#### Primary Invariant: All Variables Below nextFree

```lean
def Program.allVarsBelow (p : Program α) : Prop :=
  ∀ v ∈ allVars p.content, v < p.nextFree
```

**Theorem**: All well-formed programs satisfy this invariant.

#### Uniqueness Invariant: All Variables Distinct

```lean
def Program.allVarsUnique (p : Program α) : Prop :=
  ∀ v₁ v₂ ∈ allVars p.content, v₁ ≠ v₂ → v₁ ≠ v₂
```

**Theorem**: Fresh variable generation preserves uniqueness.

#### Well-formedness Invariant: All Uses Have Declarations

```lean
def Program.allUsesHaveDecls (p : Program α) : Prop :=
  ∀ use ∈ varUses p.content, ∃ decl ∈ varDecls p.content, use = decl
```

**Theorem**: Type checking ensures this invariant.

### 8. Handling Source-Level Shadowing

**Problem**: Source languages (Boogie, C_Simp) allow shadowing, but Performant Ordering makes it impossible.

**Solution**: During parsing/translation, assign fresh numbers to all variables, even if they have the same source name.

#### Example: Boogie Source with Shadowing

```boogie
procedure Example() {
  var x: int;
  x := 1;
  {
    var x: int;  // Shadows outer x
    x := 2;      // Refers to inner x
  }
  assert x == 1;  // Refers to outer x
}
```

#### Translation to Performant Ordering

```lean
-- During translation, maintain a scope stack
-- Outer scope: x → 42
-- Inner scope: x → 73

init "x" 42 int (some 1)     -- Outer x gets number 42
set 42 (const 1)
-- Enter inner scope
init "x" 73 int (some 2)     -- Inner x gets number 73 (fresh!)
set 73 (const 2)             -- Refers to 73
-- Exit inner scope
assert "outer_x" (42 == 1)   -- Refers to 42
```

#### Scope Stack During Translation

```lean
structure ScopeStack where
  scopes : List (Map String Nat)  -- Stack of name → number mappings

namespace ScopeStack

def empty : ScopeStack := ⟨[Map.empty]⟩

def pushScope (s : ScopeStack) : ScopeStack :=
  ⟨Map.empty :: s.scopes⟩

def popScope (s : ScopeStack) : ScopeStack :=
  ⟨s.scopes.tail⟩

def lookup (s : ScopeStack) (name : String) : Option Nat :=
  -- Search from innermost to outermost scope
  s.scopes.findSome? (fun scope => scope.find? name)

def insert (s : ScopeStack) (name : String) (num : Nat) : ScopeStack :=
  match s.scopes with
  | [] => ⟨[Map.empty.insert name num]⟩
  | scope :: rest => ⟨scope.insert name num :: rest⟩

end ScopeStack
```

#### Translation Algorithm

```lean
def translateStmt (stmt : BoogieStmt) : FreshM (ScopeStack → Cmd × ScopeStack) :=
  match stmt with
  | .varDecl name ty init =>
      fun scopes => do
        let varNum ← freshVar
        let scopes' := scopes.insert name varNum
        let cmd := .init name varNum ty (translateExpr init scopes)
        return (cmd, scopes')
  
  | .assign name expr =>
      fun scopes =>
        match scopes.lookup name with
        | none => error s!"Variable {name} not found"
        | some varNum =>
            let cmd := .set varNum (translateExpr expr scopes)
            return (cmd, scopes)
  
  | .block stmts =>
      fun scopes => do
        let scopes' := scopes.pushScope
        let (cmds, scopes'') ← translateStmts stmts scopes'
        let scopes''' := scopes''.popScope
        return (.block cmds, scopes''')
```

**Key Insight**: Source-level shadowing is resolved during translation by assigning different numbers to variables with the same name. The Performant Ordering representation has no shadowing - each variable has a unique number.

#### User-Facing Syntax for Referring to Shadowed Variables

**Problem**: How does a user refer to a specific variable when multiple have the same hint?

**Solution**: Use disambiguation syntax in source code (if needed):

```boogie
// Option 1: Explicit numbering (for debugging/advanced use)
var x: int;      // Gets number 42
x := 1;
{
  var x: int;    // Gets number 73
  x := 2;
  x@42 := 3;     // Explicitly refer to outer x (rare, for debugging)
}

// Option 2: Standard scoping (normal case)
// Users write normal code, translator handles numbering
var x: int;
x := 1;
{
  var x: int;
  x := 2;        // Translator knows this is the inner x
}
assert x == 1;   // Translator knows this is the outer x
```

**Implementation Note**: The `@N` syntax is optional and primarily for:
1. Debugging output (showing which variable is which)
2. Advanced users who want explicit control
3. Generated code that needs to be precise

Normal users write standard scoped code, and the translator handles the numbering automatically.

### 9. Names vs Indices Design Principle

**Core Principle**: Commands use indices for implementation, specifications use names for user interface.

#### When to Use Names

1. **Variable declarations** (`init` hint parameter) - For display and debugging
2. **Procedure specifications** (`modifies` clauses) - Users write names
3. **Error messages** - Display names to users
4. **Pretty printing** - Show names to users
5. **Source code** - Users write names

#### When to Use Indices

1. **Variable references** (`set`, `havoc`, `bvar`, `fvar`) - For semantics
2. **modifiedVars return value** - Returns list of indices
3. **Evaluation** - Look up values by index
4. **Type checking** - Look up types by index
5. **Transformations** - Track variables by index

#### Resolution Pattern

When specifications (names) need to interact with implementation (indices):

```lean
-- Pattern 1: Validate procedure modifies clause
def validateModifies (proc : Procedure) (body : Cmd) (ctx : VarContext) : Bool :=
  let modifiedIndices := body.modifiedVars
  let modifiedNames := modifiedIndices.filterMap (ctx.lookupName ·)
  modifiedNames.all (fun name => name ∈ proc.modifies ∨ name ∈ proc.outputs)

-- Pattern 2: Generate havoc statements for loop elimination
def generateLoopHavocs (body : Cmd) (ctx : VarContext) : FreshM (List Cmd) := do
  let modifiedIndices := body.modifiedVars
  return modifiedIndices.map (fun idx => .havoc idx)

-- Pattern 3: Error messages with names
def formatError (err : Error) (ctx : VarContext) : String :=
  match err with
  | .VarNotFound idx =>
      match ctx.lookupName idx with
      | some name => s!"Variable '{name}' (#{idx}) not found"
      | none => s!"Variable #{idx} not found"
```

### 10. modifiedVars and definedVars

**Critical Feature**: Track which variables are modified by commands.

#### modifiedVars Implementation

```lean
def Cmd.modifiedVars (c : Cmd P) : List Nat :=
  match c with
  | .init _ _ _ _ _ => []
  | .set var _ _ => [var]
  | .havoc var _ => [var]
  | .assert _ _ _ => []
  | .assume _ _ _ => []

def Cmds.modifiedVars (cs : List (Cmd P)) : List Nat :=
  cs.flatMap Cmd.modifiedVars
```

**Key Points**:
- Returns **indices**, not names
- `init` returns empty list (declares, doesn't modify)
- `set` and `havoc` return the modified variable's index
- Consumers resolve indices to names when needed

#### definedVars Implementation

```lean
def Cmd.definedVars (c : Cmd P) : List String :=
  match c with
  | .init hint _ _ _ _ => [hint]
  | .set _ _ _ => []
  | .havoc _ _ => []
  | .assert _ _ _ => []
  | .assume _ _ _ => []
```

**Key Points**:
- Returns **names** (hints), not indices
- Only `init` defines new variables
- Used for tracking variable declarations

#### Use Cases

1. **Loop Elimination**:
```lean
def eliminateLoop (loop : Loop) (ctx : VarContext) : FreshM Cmd := do
  let modifiedIndices := loop.body.modifiedVars
  let havocs := modifiedIndices.map (fun idx => .havoc idx)
  -- Generate havoc statements for all modified variables
  return .block havocs
```

2. **Procedure Validation**:
```lean
def validateProcedure (proc : Procedure) (ctx : VarContext) : Bool :=
  let modifiedIndices := proc.body.modifiedVars
  let modifiedNames := modifiedIndices.filterMap (ctx.lookupName ·)
  -- Check that all modified variables are in modifies clause or outputs
  modifiedNames.all (fun name => 
    name ∈ proc.modifies ∨ name ∈ proc.outputs)
```

3. **Definedness Checking**:
```lean
def isDefinedOver (cmd : Cmd) (store : Store) : Bool :=
  let modifiedIndices := cmd.modifiedVars
  modifiedIndices.all (fun idx => store.contains idx)
```

### 11. Global Variables and VarContext Initialization

**Problem**: Global variables need to be accessible in all procedures.

**Solution**: Initialize VarContext with globals before translating procedures.

#### Global Variable Initialization

```lean
structure VarContext (P : PureExpr) where
  vars : Map Nat (String × P.Ty)  -- number → (hint, type)

namespace VarContext

def empty : VarContext P := ⟨Map.empty⟩

def insert (ctx : VarContext P) (num : Nat) (hint : String) (ty : P.Ty) : VarContext P :=
  ⟨ctx.vars.insert num (hint, ty)⟩

def lookup (ctx : VarContext P) (num : Nat) : Option (String × P.Ty) :=
  ctx.vars.find? num

def lookupName (ctx : VarContext P) (num : Nat) : Option String :=
  (ctx.lookup num).map (·.1)

def lookupType (ctx : VarContext P) (num : Nat) : Option P.Ty :=
  (ctx.lookup num).map (·.2)

-- Initialize VarContext with global variables
def fromGlobals (globals : List (String × P.Ty)) : FreshM (VarContext P) := do
  let mut ctx := empty
  for (name, ty) in globals do
    let varNum ← freshVar
    ctx := ctx.insert varNum name ty
  return ctx

end VarContext
```

#### Program Translation with Globals

```lean
def translateProgram (prog : BoogieProgram) : FreshM StrataProgram := do
  -- Step 1: Assign numbers to globals
  let globalVars := prog.globals.map (fun g => (g.name, g.type))
  let ctx ← VarContext.fromGlobals globalVars
  
  -- Step 2: Translate procedures with global context
  let procedures ← prog.procedures.mapM (translateProcedure ctx)
  
  return {
    globals := globalVars,
    procedures := procedures
  }
```

**Key Insight**: Globals get fresh numbers first, then procedures can reference them by those numbers.

---

## Implementation Strategy

**Implementation Order**: We will implement changes to the **Lambda Calculus layer first**, then the Imperative layer, then translations and backends. This order is chosen because:
1. Lambda calculus is the foundation - both bvar and fvar changes happen here
2. Imperative layer depends on fvar being updated
3. Translations depend on both layers being complete

### Phase 1: Core Infrastructure (Foundation)

**Goal**: Establish the basic structures and monad without breaking existing code.

**Tasks**:
1. Define `Program α` structure
2. Implement `FreshM` monad
3. Prove basic lemmas about `freshVar`
4. Create `VarContext` structure
5. No changes to existing AST yet

**Success Criteria**: New code compiles, existing code unchanged.

### Phase 2: Lambda Calculus Migration (FIRST IMPLEMENTATION PHASE)

**Goal**: Update LExpr to use Performant Ordering.

**Why First**: Lambda calculus is the foundation. Both `bvar` (lambda-bound variables) and `fvar` (imperative variables) are defined in LExpr, so we must update this layer before the imperative layer can use the new fvar representation.

**Tasks**:
1. Change `LExpr.bvar` to use `Nat` + hint (remove De Bruijn relative indexing)
2. Change `LExpr.fvar` to use `Nat` + hint (remove `Identifier`)
3. Update `LExpr.abs` to store parameter number + hint
4. Update `LExpr.quant` to store bound variable numbers + hints
5. Remove all index shifting functions
6. Simplify substitution (no shifting)
7. Simplify beta reduction (no adjustment)
8. Update evaluation to use number-based lookup
9. Update type checking to use number-based lookup

**Success Criteria**: Lambda calculus layer compiles with simplified operations.

### Phase 3: Imperative Layer Migration (SECOND IMPLEMENTATION PHASE)

**Goal**: Update Cmd to use Performant Ordering.

**Why Second**: Imperative layer uses `fvar` from LExpr, so it must be updated after the lambda calculus layer is complete.

**Tasks**:
1. Update `Cmd.init` to store hint + var number + optional expression
2. Update `Cmd.set` to use `Nat` variable number
3. Update `Cmd.havoc` to use `Nat` variable number
4. Update `Cmd.modifiedVars` to return `List Nat`
5. Update evaluation to track nextFree
6. Update type checking to use number-based lookup
7. Update semantics to use number-based operations
8. Implement pretty printing with VarContext

**Success Criteria**: Imperative layer compiles with number-based variables.

### Phase 4: Translation and Backend Updates (THIRD IMPLEMENTATION PHASE)

**Goal**: Update all language frontends and backends.

**Why Third**: Translations depend on both lambda calculus and imperative layers being complete.

**Tasks**:
1. Update Boogie translation to assign fresh numbers
2. Update C_Simp translation to assign fresh numbers
3. Update SMT encoding to use SMTContext
4. Update all transformations to use FreshM
5. Update loop elimination to use fresh numbers
6. Update procedure inlining to use fresh numbers

**Success Criteria**: All translations and backends compile.

### Phase 5: Proof Restoration (FINAL PHASE)

**Goal**: Restore all proofs to working state.

**Tasks**:
1. Remove all De Bruijn shifting lemmas
2. Prove freshness lemmas for FreshM
3. Prove substitution correctness (simplified)
4. Prove transformation correctness
5. Prove invariant preservation
6. Update all semantic proofs

**Success Criteria**: All proofs compile, no `sorry` remains.

### Phase 6: Testing and Validation

**Goal**: Ensure all tests pass.

**Tasks**:
1. Run `lake build` - must succeed
2. Run `lake test` - must pass all tests
3. Update test expectations if needed
4. Verify examples still work
5. Performance testing

**Success Criteria**: Full test suite passes.

---

## Testing Strategy

### Unit Testing

**Approach**: Update existing tests to use Performant Ordering.

**Test Categories**:
1. **Fresh variable generation**: Verify uniqueness
2. **Substitution**: Verify correctness without shifting
3. **Beta reduction**: Verify correctness without adjustment
4. **Evaluation**: Verify number-based lookup works
5. **Type checking**: Verify number-based type lookup works
6. **Pretty printing**: Verify display names are correct


### Property-Based Testing

**Properties to Test**:

1. **Freshness Property**:
   ```lean
   ∀ (p : Program α) (m : FreshM β),
     let (_, nextFree') := m.run p.nextFree
     ∀ v ∈ allVars p.content, v < nextFree'
   ```

2. **Uniqueness Property**:
   ```lean
   ∀ (p : Program α),
     p.allVarsUnique → (transform p).allVarsUnique
   ```

3. **Substitution Property**:
   ```lean
   ∀ (e : LExpr) (v : Nat) (arg : LExpr),
     semantics (substitute e v arg) = semantics e [v ↦ semantics arg]
   ```

4. **Beta Reduction Property**:
   ```lean
   ∀ (param : Nat) (body arg : LExpr),
     semantics (betaReduce (.app (.abs param body) arg)) =
     semantics (substitute body param arg)
   ```

### Integration Testing

**Test Scenarios**:
1. Parse Boogie program → Translate → Verify
2. Complex transformations (call elimination, loop elimination)
3. Multi-stage transformation pipelines
4. SMT encoding and solving

### Regression Testing

**Approach**: All existing tests must pass with same semantics.

**Test Files to Update**:
- `StrataTest/DL/Lambda/*.lean`
- `StrataTest/DL/Imperative/*.lean`
- `StrataTest/Languages/Boogie/*.lean`
- `StrataTest/Transform/*.lean`

---

## Migration Plan

### Compiler-Driven Approach

**Principle**: Make breaking changes, then fix what the compiler complains about.

### Step 1: Create Infrastructure (No Breaking Changes)

1. Create `Strata/Core/Program.lean` with `Program α` structure
2. Create `Strata/Core/FreshM.lean` with monad and lemmas
3. Create `Strata/Core/VarContext.lean` with display context
4. Verify these compile independently

### Step 2: Break Lambda Calculus (Controlled Break)

1. Update `LExpr.bvar` to use `Nat`
2. Update `LExpr.fvar` to use `Nat`
3. Update `LExpr.abs` to store parameter number
4. Run `lake build` to identify all broken files
5. Create `broken-files-lambda.md` to track them


### Step 3: Fix Lambda Calculus Files

For each broken file:
1. Remove index shifting logic
2. Simplify substitution to direct replacement
3. Update evaluation to use number lookup
4. Update type checking to use number lookup
5. If proofs break, add `sorry --TODO: Restore proof` and document in `broken-proofs.md`
6. Continue until `lake build` succeeds for lambda layer

### Step 4: Break Imperative Layer (Controlled Break)

1. Update `Cmd.set` to use `Nat`
2. Update `Cmd.havoc` to use `Nat`
3. Run `lake build` to identify broken files
4. Create `broken-files-imperative.md` to track them

### Step 5: Fix Imperative Layer Files

For each broken file:
1. Update evaluation to track nextFree
2. Update type checking to use number lookup
3. Update semantics to use number operations
4. If proofs break, add `sorry --TODO: Restore proof` and document
5. Continue until `lake build` succeeds for imperative layer

### Step 6: Update Translations and Backends

1. Update Boogie translation to use FreshM
2. Update C_Simp translation to use FreshM
3. Update SMT encoding to use SMTContext
4. Update all transformations to use FreshM
5. Fix compilation errors as they arise

### Step 7: Restore Proofs

1. Review `broken-proofs.md`
2. For each broken proof:
   - Remove `sorry`
   - Prove freshness using FreshM lemmas
   - Prove substitution correctness (simpler than before)
   - Prove transformation correctness
3. Continue until no `sorry` remains

### Step 8: Test and Validate

1. Run `lake build` - must succeed
2. Run `lake test` - fix any failures
3. Update test expectations if needed
4. Verify all examples work
5. Final validation

---

## Success Criteria

### Compilation

- [ ] `lake build` succeeds with no errors
- [ ] No compilation warnings related to variable numbering
- [ ] All modules compile successfully

### Testing

- [ ] `lake test` passes all tests
- [ ] No test failures
- [ ] Test coverage maintained or improved


### Proofs

- [ ] No `sorry` placeholders remain
- [ ] All freshness lemmas proven
- [ ] All substitution lemmas proven
- [ ] All transformation correctness proofs restored
- [ ] All invariant preservation proofs complete

### Code Quality

- [ ] All De Bruijn index shifting code removed
- [ ] All De Bruijn weakening code removed
- [ ] All De Bruijn lifting code removed
- [ ] Code is simpler and more maintainable
- [ ] Documentation updated

### Functionality

- [ ] All examples work correctly
- [ ] Boogie translation works
- [ ] C_Simp translation works
- [ ] SMT encoding works
- [ ] Verification produces correct results

---

## Appendix A: Key Differences from De Bruijn Indices

| Aspect | De Bruijn Indices | Performant Ordering |
|--------|-------------------|---------------------|
| **Variable Identity** | Relative (distance from binder) | Absolute (unique number) |
| **Substitution** | Requires index shifting | Simple replacement |
| **Beta Reduction** | Requires index adjustment | Simple substitution |
| **Alpha Conversion** | Requires index renormalization | Generate fresh number |
| **Shadowing** | Possible (same relative index) | Impossible (unique numbers) |
| **Transformation** | Variables change identity | Variables stable |
| **Proof Complexity** | High (shifting lemmas) | Low (freshness lemmas) |
| **Canonical Form** | Yes (unique representation) | No (alpha-equivalent terms differ) |
| **Strata Fit** | Poor (transformation-heavy) | Excellent (transformation-friendly) |

---

## Appendix B: Example Transformations

### Example 1: Beta Reduction

**De Bruijn Approach**:
```lean
-- (λ. body[0]) arg
-- Need to shift arg's free variables up by 1
-- Then substitute 0 with shifted arg
-- Then shift result's free variables down by 1
betaReduce (.app (.abs body) arg) =
  let shiftedArg := shift arg 1
  let substituted := subst body 0 shiftedArg
  shift substituted (-1)
```

**Performant Ordering Approach**:
```lean
-- (λ x₄₂. body) arg
-- Just substitute 42 with arg, no shifting!
betaReduce (.app (.abs 42 body) arg) =
  substitute body 42 arg
```


### Example 2: Procedure Inlining

**De Bruijn Approach**:
```lean
-- Inline: call y := f(x)
-- Need to:
-- 1. Shift all indices in f's body
-- 2. Substitute parameters with shifted arguments
-- 3. Shift result back
-- 4. Handle variable capture carefully
inlineProcedure (call y f [x]) =
  let body := f.body
  let shiftedBody := shiftIndices body (currentDepth)
  let substituted := substParams shiftedBody f.params [x]
  let result := shiftIndices substituted (-currentDepth)
  result
```

**Performant Ordering Approach**:
```lean
-- Inline: call y := f(x)
-- Just generate fresh numbers for f's locals and substitute!
inlineProcedure (call y f [x]) : FreshM Stmt := do
  let freshLocals ← freshVars f.locals.length
  let body := f.body
  let substituted := substParams body f.params [x]
  let renamed := renameLocals substituted f.locals freshLocals
  return renamed
```

### Example 3: Loop Elimination

**De Bruijn Approach**:
```lean
-- Eliminate: while guard { body }
-- Need to track which indices are modified
-- Shift indices when generating havoc statements
-- Complex index management
eliminateLoop (while guard body) =
  let modifiedIndices := getModifiedIndices body
  let shiftedIndices := shiftIndices modifiedIndices (currentDepth)
  let havocs := generateHavocs shiftedIndices
  -- ... complex index management
```

**Performant Ordering Approach**:
```lean
-- Eliminate: while guard { body }
-- Modified variables have stable numbers, just havoc them!
eliminateLoop (while guard body) =
  let modifiedVars := getModifiedVars body  -- Returns List Nat
  let havocs := modifiedVars.map (fun v => .havoc v)
  -- ... simple, no index management needed
```

---

## Appendix C: Proof Strategy Examples

### Freshness Proof Pattern

```lean
theorem transform_preserves_freshness (p : Program α) :
  p.allVarsBelow →
  (transform p).allVarsBelow := by
  intro h
  unfold transform
  -- Show that FreshM generates variables >= p.nextFree
  have fresh : ∀ v ∈ newVars, v >= p.nextFree := by
    apply freshVar_generates_above
  -- Show that old variables are unchanged
  have old : ∀ v ∈ oldVars, v < p.nextFree := by
    apply h
  -- Combine to show all variables below new nextFree
  omega
```


### Substitution Correctness Proof Pattern

```lean
theorem substitute_preserves_semantics (e : LExpr) (v : Nat) (arg : LExpr) :
  semantics (substitute e v arg) = semantics e [v ↦ semantics arg] := by
  induction e with
  | bvar m index ty =>
      simp [substitute]
      split
      · -- index == v, substitution happens
        simp [semantics]
      · -- index != v, no substitution
        simp [semantics]
  | abs m param body ty ih =>
      simp [substitute, semantics]
      -- No index shifting needed!
      apply ih
  | app m fn arg ty ih_fn ih_arg =>
      simp [substitute, semantics]
      rw [ih_fn, ih_arg]
  -- ... other cases, all straightforward
```

**Key Insight**: No shifting lemmas needed! Each case is simple.

### Uniqueness Preservation Proof Pattern

```lean
theorem transform_preserves_uniqueness (p : Program α) :
  p.allVarsUnique →
  (transform p).allVarsUnique := by
  intro h
  unfold transform
  -- Show that fresh variables are distinct from old variables
  have fresh_distinct : ∀ v₁ ∈ newVars, ∀ v₂ ∈ oldVars, v₁ ≠ v₂ := by
    intros v₁ h₁ v₂ h₂
    have : v₁ >= p.nextFree := freshVar_generates_above h₁
    have : v₂ < p.nextFree := h h₂
    omega
  -- Show that fresh variables are distinct from each other
  have fresh_unique : ∀ v₁ v₂ ∈ newVars, v₁ ≠ v₂ → v₁ ≠ v₂ := by
    apply freshVars_generates_unique
  -- Combine
  intros v₁ v₂ h_in₁ h_in₂ h_neq
  cases h_in₁ <;> cases h_in₂
  · apply h  -- both old
  · apply fresh_distinct  -- one old, one new
  · apply fresh_distinct.symm  -- one new, one old
  · apply fresh_unique  -- both new
```

---

## Appendix D: File-by-File Migration Checklist

### Core Files

- [ ] `Strata/Core/Program.lean` - Create new
- [ ] `Strata/Core/FreshM.lean` - Create new
- [ ] `Strata/Core/VarContext.lean` - Create new

### Lambda Calculus Layer

- [ ] `Strata/DL/Lambda/LExpr.lean` - Update bvar, fvar, abs, quant
- [ ] `Strata/DL/Lambda/LExprEval.lean` - Remove shifting, simplify substitution
- [ ] `Strata/DL/Lambda/LExprType.lean` - Update type checking
- [ ] `Strata/DL/Lambda/LExprWF.lean` - Remove shifting lemmas
- [ ] `Strata/DL/Lambda/Semantics.lean` - Update semantics
- [ ] `Strata/DL/Lambda/Scopes.lean` - Update scope handling


### Imperative Layer

- [ ] `Strata/DL/Imperative/Cmd.lean` - Update set, havoc
- [ ] `Strata/DL/Imperative/CmdEval.lean` - Update evaluation
- [ ] `Strata/DL/Imperative/CmdType.lean` - Update type checking
- [ ] `Strata/DL/Imperative/CmdSemantics.lean` - Update semantics
- [ ] `Strata/DL/Imperative/Stmt.lean` - Update statement handling
- [ ] `Strata/DL/Imperative/StmtSemantics.lean` - Update statement semantics
- [ ] `Strata/DL/Imperative/SemanticsProps.lean` - Update semantic properties

### Boogie Language

- [ ] `Strata/Languages/Boogie/Statement.lean` - Update translation
- [ ] `Strata/Languages/Boogie/Procedure.lean` - Update procedure handling
- [ ] `Strata/Languages/Boogie/Program.lean` - Update program structure
- [ ] `Strata/Languages/Boogie/Verifier.lean` - Update verification
- [ ] `Strata/Languages/Boogie/SMTEncoder.lean` - Update SMT encoding
- [ ] `Strata/Languages/Boogie/BoogieGen.lean` - Update code generation

### Transformations

- [ ] `Strata/Transform/CallElim.lean` - Use FreshM
- [ ] `Strata/Transform/CallElimCorrect.lean` - Update proofs
- [ ] `Strata/Transform/LoopElim.lean` - Use FreshM
- [ ] `Strata/Transform/DetToNondet.lean` - Use FreshM
- [ ] `Strata/Transform/DetToNondetCorrect.lean` - Update proofs
- [ ] `Strata/Transform/ProcedureInlining.lean` - Use FreshM

### Tests

- [ ] `StrataTest/DL/Lambda/*.lean` - Update all lambda tests
- [ ] `StrataTest/DL/Imperative/*.lean` - Update all imperative tests
- [ ] `StrataTest/Languages/Boogie/*.lean` - Update all Boogie tests
- [ ] `StrataTest/Transform/*.lean` - Update all transformation tests

---

## Appendix E: Common Pitfalls and Solutions

### Pitfall 1: Forgetting to Thread nextFree

**Problem**: Generating multiple fresh variables without threading state.

**Wrong**:
```lean
def transform (e : Expr) : Expr :=
  let v1 := freshVar  -- Wrong! No state threading
  let v2 := freshVar  -- Wrong! Will get same number
  ...
```

**Right**:
```lean
def transform (e : Expr) : FreshM Expr := do
  let v1 ← freshVar  -- Correct! State threaded
  let v2 ← freshVar  -- Correct! Gets next number
  ...
```


### Pitfall 2: Mixing Variable Numbers and Display Names

**Problem**: Using display names for semantic operations.

**Wrong**:
```lean
def lookupVar (env : Env) (name : String) : Option Value :=
  env.find? name  -- Wrong! Names are for display only
```

**Right**:
```lean
def lookupVar (env : Env) (varNum : Nat) : Option Value :=
  env.find? varNum  -- Correct! Use numbers for semantics
```

### Pitfall 3: Not Updating nextFree After Fresh Generation

**Problem**: Generating fresh variable but not incrementing counter.

**Wrong**:
```lean
def addVar (p : Program α) : Program α :=
  let varNum := p.nextFree
  ⟨addVarToContent p.content varNum, p.nextFree⟩  -- Wrong! nextFree not updated
```

**Right**:
```lean
def addVar (p : Program α) : Program α :=
  let varNum := p.nextFree
  ⟨addVarToContent p.content varNum, p.nextFree + 1⟩  -- Correct!
```

### Pitfall 4: Trying to Shift Indices

**Problem**: Old habits from De Bruijn indices.

**Wrong**:
```lean
def substitute (e : Expr) (v : Nat) (arg : Expr) : Expr :=
  match e with
  | .abs param body =>
      let shiftedArg := shift arg 1  -- Wrong! No shifting needed
      .abs param (substitute body v shiftedArg)
```

**Right**:
```lean
def substitute (e : Expr) (v : Nat) (arg : Expr) : Expr :=
  match e with
  | .abs param body =>
      .abs param (substitute body v arg)  -- Correct! Just recurse
```

---

## Appendix F: Performance Considerations

### Variable Lookup

**Concern**: Map lookup by number vs. by name.

**Analysis**:
- Number lookup: O(log n) with balanced tree
- Name lookup: O(log n) with balanced tree
- **No performance difference**

**Benefit**: Numbers are smaller (Nat vs String), better cache locality.

### Fresh Variable Generation

**Concern**: Incrementing counter vs. generating unique names.

**Analysis**:
- Counter increment: O(1)
- Unique name generation: O(n) to check uniqueness
- **Performant Ordering is faster**


### Substitution

**Concern**: Traversing entire AST for substitution.

**Analysis**:
- De Bruijn: O(n) traversal + O(n) shifting = O(n)
- Performant Ordering: O(n) traversal = O(n)
- **Performant Ordering is faster** (no shifting overhead)

### Memory Usage

**Concern**: Storing numbers vs. storing names.

**Analysis**:
- Numbers: 8 bytes per variable (Nat)
- Names: 8+ bytes per variable (String pointer + data)
- **Performant Ordering uses less memory**

**Conclusion**: Performant Ordering is equal or better in all performance aspects.

---

## Appendix G: Frequently Asked Questions

### Q1: Why not use De Bruijn indices?

**A**: De Bruijn indices are great for canonical representation, but Strata is transformation-heavy. Variables changing identity during transformations makes proofs complex. Performant Ordering keeps variables stable, simplifying everything.

### Q2: What about alpha-equivalence?

**A**: We lose syntactic canonicity, but we don't need it. Strata cares about semantic equivalence, not syntactic uniqueness. For verification, semantic equivalence is what matters.

### Q3: How do we handle variable capture?

**A**: Variable capture is impossible by construction! All variables have unique numbers, so there's nothing to capture. This is a huge simplification.

### Q4: What about pretty printing?

**A**: We maintain a VarContext that maps numbers to display names. Pretty printing resolves numbers to names. Users see readable names, but semantics use numbers.

### Q5: How do we handle globals?

**A**: Globals are just variables that get assigned numbers first. Start with nextFree = 0, assign globals numbers 0, 1, 2, ... using freshVar, then continue with nextFree at N (where N is the number of globals). All subsequent variables (locals, parameters, lambda-bound) get numbers >= N using the same counter.

### Q6: What about procedure parameters?

**A**: When declaring a procedure, assign fresh numbers to all parameters. When calling a procedure, substitute arguments for parameter numbers. When inlining, generate fresh numbers for all locals.

### Q7: How do we handle quantifiers?

**A**: Quantifiers store the list of bound variable numbers. When evaluating, bind those numbers in the environment. No relative indexing needed.

### Q8: What about performance?

**A**: Performant Ordering is equal or better in all aspects: lookup speed, generation speed, memory usage, and substitution speed.


---

## Appendix H: References and Related Work

### Performant Ordering in Other Systems

- **SSA Form**: Static Single Assignment uses unique variable numbers
- **ANF**: Administrative Normal Form uses unique names
- **CPS**: Continuation-Passing Style uses unique names
- **LLVM IR**: Uses numbered registers (%0, %1, %2, ...)

### Why Strata Needs Performant Ordering

1. **Multi-stage transformations**: Boogie → Imperative → SMT → Solver
2. **Transformation-heavy**: Call elimination, loop elimination, inlining
3. **Verification focus**: Semantic equivalence matters, not syntactic canonicity
4. **Proof engineering**: Simpler proofs = more maintainable system

### Academic References

- Pierce, B. C. (2002). *Types and Programming Languages*. MIT Press.
  - Chapter on De Bruijn indices and their limitations
- Appel, A. W. (1998). *Modern Compiler Implementation in ML*. Cambridge University Press.
  - Chapter on SSA form and unique naming
- Leroy, X. (2009). "Formal verification of a realistic compiler". *Communications of the ACM*.
  - CompCert uses unique names for intermediate representations

---

## Conclusion

This specification describes the migration of Strata to **Performant Ordering** - a unified variable numbering scheme using globally unique natural numbers. This change simplifies the entire system:

- **Lambda calculus**: No more index shifting, weakening, or lifting
- **Imperative layer**: Unambiguous variable references
- **Transformations**: Variables maintain stable identity
- **Proofs**: Simpler freshness lemmas replace complex shifting lemmas
- **Strata-optimized**: Perfect fit for transformation-heavy verification pipelines

The migration follows a compiler-driven approach: make breaking changes, fix what breaks, restore proofs, validate tests. The result is a simpler, more maintainable, and more transformation-friendly system.

**Next Steps**: Begin implementation with Phase 1 (Core Infrastructure).

---

## Document History

| Version | Date | Author | Changes |
|---------|------|--------|---------|
| 1.0 | 2026-01-19 | Kiro AI | Initial specification |

---

## Approval

This specification requires review and approval before implementation begins.

- [ ] Technical Lead Review
- [ ] Architecture Review
- [ ] Implementation Team Review
- [ ] Approved for Implementation

---

*End of Specification*
