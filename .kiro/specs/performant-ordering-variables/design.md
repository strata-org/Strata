# Performant Ordering Variable Numbering - Design

## Architecture

### High-Level Overview

```
┌─────────────────────────────────────────────────────────────┐
│                     NextFree Structure                       │
│  ┌────────────────────────────────────────────────────────┐ │
│  │  structure NextFree (α : Type) where                   │ │
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
NextFree
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

## Design Details

### 1. NextFree Structure

All program entry points (expressions, statements, procedures, etc.) are wrapped in a `NextFree` structure:

```lean
-- Generic typeclass for types that contain variables
-- This abstracts over HasVarsPure and HasVarsImp
class HasVars (α : Type) where
  vars : α → List Nat

structure NextFree (α : Type) [HasVars α] where
  content : α
  nextFree : Nat

namespace NextFree

def empty (content : α) : NextFree α :=
  ⟨content, 0⟩

def withFreshCounter (content : α) (nextFree : Nat) : NextFree α :=
  ⟨content, nextFree⟩

-- Primary invariant: all variables in content are below nextFree
def wellFormed (p : NextFree α) : Prop :=
  ∀ v ∈ HasVars.vars p.content, v < p.nextFree

-- Alternative formulation: nextFree and above are not in the variable list
def wellFormed' (p : NextFree α) : Prop :=
  ∀ v ≥ p.nextFree, v ∉ HasVars.vars p.content

-- These are equivalent
theorem wellFormed_iff_wellFormed' (p : NextFree α) :
  p.wellFormed ↔ p.wellFormed' := by
  constructor
  · intro h v hge
    by_contra hin
    have : v < p.nextFree := h v hin
    omega
  · intro h v hin
    by_contra hge
    have : v ∉ HasVars.vars p.content := h v (Nat.le_of_not_lt hge)
    contradiction

end NextFree
```

**Integration with Existing HasVars Typeclasses**: 

The existing typeclasses in `Strata/DL/Imperative/HasVars.lean` are:
- `HasVarsPure P α` - provides `getVars : α → List P.Ident`
- `HasVarsImp P α` - provides `definedVars`, `modifiedVars`, `touchedVars : α → List P.Ident`
- `HasVarsTrans P α PT` - for procedure-aware variable lookup

Since `P.Ident` will become `Nat` as part of this migration, we add a generic `HasVars` typeclass that abstracts over both pure and imperative cases:

```lean
-- Generic HasVars typeclass (add to Strata/DL/Imperative/HasVars.lean or new file)
class HasVars (α : Type) where
  vars : α → List Nat

-- Default instance for types with HasVarsPure
instance [HasVarsPure P α] : HasVars α where
  vars := HasVarsPure.getVars

-- Default instance for types with HasVarsImp
instance [HasVarsImp P α] : HasVars α where
  vars := HasVarsImp.touchedVars
```

This way, `NextFree` works uniformly for both expressions (via `HasVarsPure`) and imperative constructs (via `HasVarsImp`) without needing to know which one is being used.

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

def runProgram (m : FreshM α) (p : NextFree β) : NextFree α :=
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
  | bvar (m : T.base.Metadata) (index : Nat) (ty : Option T.TypeType)
  | fvar (m : T.base.Metadata) (index : Nat) (ty : Option T.TypeType)
  | abs (m : T.base.Metadata) (param : Nat) (name : String) (body : LExpr T) (ty : Option T.TypeType)
  | app (m : T.base.Metadata) (fn : LExpr T) (arg : LExpr T) (ty : Option T.TypeType)
  | quant (m : T.base.Metadata) (kind : QuantKind) (var : Nat) (name : String)
          (body : LExpr T) (ty : Option T.TypeType)
  -- ... other constructors
```

**Key Changes**:
- `bvar` uses only `Nat` for unique identity (no string stored)
- `fvar` uses only `Nat` for unique identity (no string stored)
- `abs` stores parameter number + `name` for the parameter name
- `quant` stores variable number + `name` for the bound variable

**Design Principle**: 
1. **Variable references** (`bvar`, `fvar`) store only the semantic identity (Nat)
2. **Variable declarations** (`abs`, `quant`) store both identity (Nat) and display name (String)
3. **VarContext** provides display names for variable references during pretty printing

#### Substitution (Simplified)

```lean
def substitute (e : LExpr T) (var : Nat) (replacement : LExpr T) : LExpr T :=
  match e with
  | .bvar m index ty => if index == var then replacement else e
  | .fvar m index ty => if index == var then replacement else e
  | .abs m param name body ty => 
      .abs m param name (substitute body var replacement) ty
  | .app m fn arg ty =>
      .app m (substitute fn var replacement) (substitute arg var replacement) ty
  | .quant m kind qvar name body ty =>
      .quant m kind qvar name (substitute body var replacement) ty
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
  | .abs m param name body ty => do
      let newParam ← freshVar
      let newBody := substitute body param (.bvar m newParam ty)
      return .abs m newParam name newBody ty
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
  declOrder : List Nat              -- variables in declaration order

namespace VarContext

def empty : VarContext P := ⟨Map.empty, []⟩

def insert (ctx : VarContext P) (num : Nat) (name : String) (ty : P.Ty) : VarContext P :=
  ⟨ctx.vars.insert num (name, ty), ctx.declOrder ++ [num]⟩

def lookup (ctx : VarContext P) (num : Nat) : Option (String × P.Ty) :=
  ctx.vars.find? num

def lookupName (ctx : VarContext P) (num : Nat) : Option String :=
  (ctx.lookup num).map (·.1)

def lookupType (ctx : VarContext P) (num : Nat) : Option P.Ty :=
  (ctx.lookup num).map (·.2)

-- Get unambiguous display name for a variable
-- If multiple variables share the same name, use @N suffix where N is the shadowing count
def getDisplayName (ctx : VarContext P) (varNum : Nat) : String :=
  match ctx.lookupName varNum with
  | none => s!"@{varNum}"  -- Unknown variable, show raw number with @
  | some name =>
      if name.isEmpty then s!"@{varNum}"
      else
        -- Find position of this variable in declaration order
        match ctx.declOrder.indexOf varNum with
        | none => s!"@{varNum}"  -- Not in declaration order (shouldn't happen)
        | some pos =>
            -- Count how many variables with the same name were declared AFTER this one
            let laterVarsWithSameName := 
              ctx.declOrder.drop (pos + 1)
                |>.filter (fun v => ctx.lookupName v == some name)
                |>.length
            
            if laterVarsWithSameName == 0 then
              name  -- No shadowing, use plain name
            else
              s!"{name}@{laterVarsWithSameName}"  -- Shadowed, add suffix

-- Initialize VarContext with global variables
def fromGlobals (globals : List (String × P.Ty)) : FreshM (VarContext P) := do
  let mut ctx := empty
  for (name, ty) in globals do
    let varNum ← freshVar
    ctx := ctx.insert varNum name ty
  return ctx

end VarContext
```

**Shadowing Example**:

```lean
-- Source code with shadowing:
init x := 3  -- Gets number 10
init x := 2  -- Gets number 11 (shadows 10)
assert x < (previous x)  -- 11 < 10

-- VarContext state:
vars: {10 → ("x", int), 11 → ("x", int)}
declOrder: [10, 11]

-- Display names:
getDisplayName ctx 10 = "x@1"  -- 1 variable named x declared after this
getDisplayName ctx 11 = "x"    -- 0 variables named x declared after this (most recent)

-- Pretty printed output:
assert x < x@1
```

**Key Points**:
- `declOrder` tracks variables in the order they were declared
- `getDisplayName` counts how many variables with the same name were declared AFTER the target variable
- The most recent variable with a given name gets the plain name (no suffix)
- Earlier variables get `@N` suffix where N is the shadowing count
- This makes it clear which variable is which in the presence of shadowing

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
  ctx.getDisplayName varNum

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

**Example with Shadowing**:

```lean
-- AST:
init "x" 10 int (some 3)
init "x" 11 int (some 2)
assert "check" (11 < 10)

-- Pretty printed (with VarContext):
init (x : int) := 3
init (x : int) := 2
assert check: x < x@1

-- The most recent 'x' (variable 11) displays as 'x'
-- The earlier 'x' (variable 10) displays as 'x@1' (1 shadowing variable after it)
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
def NextFree.wellFormed (p : NextFree α) : Prop :=
  ∀ v ∈ HasVars.vars p.content, v < p.nextFree
```

**Theorem**: All well-formed programs satisfy this invariant.

**Alternative Formulation**: No variable at or above nextFree appears in content

```lean
def NextFree.wellFormed' (p : NextFree α) : Prop :=
  ∀ v ≥ p.nextFree, v ∉ HasVars.vars p.content
```

**Theorem**: These formulations are equivalent.

#### Well-formedness Invariant: All Uses Have Declarations

```lean
def NextFree.allUsesHaveDecls [HasVarsImp P α] (p : NextFree α) : Prop :=
  ∀ use ∈ HasVarsImp.modifiedVars p.content, 
    use ∈ HasVarsImp.definedVars p.content
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

When specifications (names) need to be validated against implementation (indices):

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

### 12. Elimination of old() Construct

**Problem**: The `old()` construct in postconditions creates a special case for referencing pre-state values, which is inconsistent with the uniform variable numbering approach.

**Solution**: Each variable in the `modifies` clause carries two identifiers - one for the current value and one for the old (pre-state) value. The semantics and VarContext use these identifiers to distinguish between current and old values.

**Important Note**: Currently, `old()` is only used for global variables in postconditions. Input parameters do not use `old()` since they are immutable in procedures.

#### Current Approach (with old())

```boogie
var g: int;

procedure Increment()
  modifies g;
  ensures g == old(g) + 1;
{
  g := g + 1;
}
```

#### New Approach (with dual identifiers)

```lean
-- Modifies clause carries both current and old identifiers
structure ModifiesEntry where
  name : String           -- Display name (e.g., "g")
  currentVar : Nat        -- Variable number for current value
  oldVar : Nat            -- Variable number for old/pre-state value

-- During procedure translation
def translateProcedure (proc : BoogieProcedure) (globals : List (String × Nat × Type)) : FreshM Procedure := do
  -- For each modified global, generate both current and old identifiers
  let modifiesEntries ← proc.modifies.mapM (fun globalName => do
    match globals.find? (fun (name, _, _) => name == globalName) with
    | some (name, currentVar, ty) =>
        let oldVar ← freshVar
        return ModifiesEntry.mk name currentVar oldVar
    | none => error s!"Global {globalName} not found")
  
  -- Translate postconditions using old identifiers
  let ensures := proc.ensures.map (fun e =>
    replaceOldReferences e modifiesEntries)
  
  return {
    inputs := proc.inputs,
    outputs := proc.outputs,
    modifies := modifiesEntries,  -- Carries both current and old identifiers
    requires := proc.requires,
    ensures := ensures,
    body := translateBody proc.body
  }

-- Replace old(g) with reference to old identifier
def replaceOldReferences (expr : Expr) (modifiesEntries : List ModifiesEntry) : Expr :=
  match expr with
  | .old (.fvar m currentVar ty) =>
      -- Find the old identifier for this global
      match modifiesEntries.find? (fun entry => entry.currentVar == currentVar) with
      | some entry => .fvar m entry.oldVar ty
      | none => expr  -- Not a modified global, keep as-is
  | _ => expr.map (replaceOldReferences · modifiesEntries)

-- VarContext tracks both current and old names
def VarContext.insertModifiesEntry (ctx : VarContext) (entry : ModifiesEntry) (ty : Type) : VarContext :=
  ctx
    |> .insert entry.currentVar entry.name ty
    |> .insert entry.oldVar ("old " ++ entry.name) ty
```

#### Example Translation

**Boogie source:**
```boogie
var g: int;

procedure Increment()
  modifies g;
  ensures g == old(g) + 1;
{
  g := g + 1;
}
```

**Translated to Performant Ordering:**
```lean
-- Assume global g was assigned number N during global initialization
-- Then the old value identifier gets a fresh number M (where M > N)

procedure Increment
  inputs: []
  outputs: []
  modifies: [
    { name: "g", currentVar: N, oldVar: M }
  ]
  requires: []
  ensures: [N == M + 1]  -- g == old g + 1 (using old identifier M)
  body:
    set N (fvar N + 1)  -- g := g + 1 (body only uses current identifier N)
```

**VarContext entries:**
```lean
N → ("g", int)
M → ("old g", int)
```

**Important**: The procedure body only references variable N. Variable M is only used in postconditions where `old(g)` appeared in the source. The actual numbers N and M depend on when variables were assigned during program initialization - M is simply a fresh number generated when processing the modifies clause.

**Key Points**:
- `old(g)` is replaced with a reference to variable 11 (the old identifier)
- The procedure body only uses variable 10 (the current value) for normal operations
- Variable 11 is ONLY used when translating `old()` expressions in contracts
- No explicit init statements or pre-state copies in the procedure
- The semantics layer is responsible for capturing pre-state values at procedure entry
- Each modified global has two identifiers in the modifies clause
- VarContext uses "old " prefix for old identifiers
- No transformation from procedure to procedure - just identifier assignment

#### Semantics Handling

The semantics layer handles the dual identifiers:

```lean
-- At procedure entry, the semantics captures pre-state values
def Procedure.eval (proc : Procedure) (state : State) : State :=
  -- Step 1: Capture old values for modified globals
  let state := proc.modifies.foldl (fun s entry =>
    match s.lookup entry.currentVar with
    | some value => s.insert entry.oldVar value
    | none => s
  ) state
  
  -- Step 2: Execute procedure body
  let state := proc.body.eval state
  
  -- Step 3: Check postconditions (can reference both current and old)
  ...
```

#### Benefits

1. **No transformation**: Procedures don't need to be transformed - just identifier assignment
2. **Uniformity**: All variable references use the same mechanism
3. **Simplicity**: No special case for `old()` in the AST after translation
4. **Clarity**: Pre-state values are explicit identifiers, not implicit constructs
5. **Semantic responsibility**: The semantics layer handles pre-state capture, not the translation
6. **Future-proof**: Supports "old " prefix convention for potential future syntax

#### Implementation Strategy

1. During procedure translation, identify all modified globals (from `modifies` clause)
2. For each modified global, generate a fresh identifier for the old value
3. Store both current and old identifiers in the `modifies` clause
4. Replace all `old()` references with old identifier references
5. Update VarContext to use "old " prefix for old identifiers
6. Update semantics to capture pre-state values at procedure entry
7. Remove `old()` constructor from expression AST

---

## Key Differences from De Bruijn Indices

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
