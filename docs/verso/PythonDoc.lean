/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import VersoManual

import Strata.Languages.Python.Resolution
import Strata.Languages.Python.Translation
import Strata.Languages.FineGrainLaurel.Elaborate

open Strata.Python.Resolution
open Strata.Python.Translation
open Strata.FineGrainLaurel

-- This gets access to most of the manual genre
open Verso.Genre Manual

-- This gets access to Lean code that's in code blocks, elaborated in
-- the same process and environment as Verso
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true

#doc (Manual) "The Python to Laurel Translation Pipeline" =>
%%%
shortTitle := "Python Pipeline"
%%%

# The Problem

The Laurel-to-Core translator expects Laurel programs where:

- Every name is resolved (no ambiguous references)
- Every call site has known arity and types
- Arguments to calls are values (not effectful expressions)
- Effects are explicit via calling conventions (heap threading, error outputs)

Python gives us none of this. Names are ambiguous, scoping is implicit,
arguments can be arbitrary expressions (including effectful calls), and
effects are entirely implicit.

# The Solution

Three passes, each establishing invariants that the next pass relies on:

```
Array (Python.stmt SourceRange)    (raw, unscoped)
  | [Resolution]
  v
ResolvedPythonProgram              (every name disambiguated, annotated with NodeInfo)
  | [Translation]
  v
Laurel.Program                     (valid Laurel, but effects implicit, args may be producers)
  | [Elaboration]
  v
Laurel.Program                     (effects explicit, args are values — ready for Core)
```

_Resolution_ disambiguates names. Its output guarantees: every reference
is annotated with what it refers to (variable, function, class, method).
Translation cannot emit an undefined reference because it only uses
identifiers that Resolution produced.

_Translation_ desugars Python surface syntax into Laurel. Its output
guarantees: valid Laurel structure (procedures, types, statements). But
it does NOT guarantee that effects are explicit or that arguments are
values — it translates Python structure directly.

_Elaboration_ makes effects explicit. Its output guarantees: arguments
to calls are values, effectful calls have their outputs bound via the
calling convention, heap/error threading is explicit. This is what
Laurel-to-Core expects.

## Engineering Principles

:::table +header
 *
   * Principle
   * What it eliminates
 *
   * Illegal states unrepresentable
   * Undefined references, invalid calls
 *
   * Proof-relevant elimination
   * Boolean blindness (no `isResolved` followed by separate lookup)
 *
   * Phase distinction
   * Mixing scoping data with target-language identifiers
 *
   * Folds
   * Ad-hoc traversal choices
 *
   * Correct by construction
   * Post-hoc rewrites, defensive checks
:::

# Resolution
%%%
tag := "resolution"
%%%

Resolution is a fold over the Python AST that threads a growing context as
accumulator. Each declaration extends the context; each reference is looked
up in the current context and annotated with the result. The output is the
same AST with a `NodeInfo` on every node — the scoping derivation for the
program.

## What Resolution Produces

The annotation on each node tells Translation exactly what to do:

- Name use → `.variable name`
- Function call → `.funcCall sig` (sig carries everything needed for emission)
- Class instantiation → `.classNew className initSig`
- Method call → `.funcCall sig` (sig has `className = some _` for qualification)
- Attribute access → `.attribute name` (bare field name; Elaboration resolves later)
- Operators → `.funcCall sig` (operators are runtime procedures with correct arity)
- Unresolvable → `.unresolved` (Translation emits Hole)
- Non-reference → `.irrelevant`

{docstring Strata.Python.Resolution.NodeInfo}

This is proof-relevant elimination: pattern matching on `NodeInfo` gives you
the data you need AND determines your action. There is no
`isResolved : String -> Bool` followed by a separate lookup. The annotation
IS the resolution.

## The Phase Boundary

All Resolution types are purely Python-level. No `Laurel.Identifier` appears
anywhere in Resolution's output. This is enforced by a newtype:

{docstring Strata.Python.Resolution.PythonIdentifier}

The only ways to create one are `.fromAst` (from a parsed AST node),
`.fromImport` (first component of a dotted module path), or `.builtin`
(for Python builtins like `len`). You cannot fabricate an identifier from
an arbitrary string — all identifiers trace back to source or builtins.

Translation obtains Laurel identifiers by calling accessor functions on
these Python-level structures. The builtin mapping (`len` ->
`Any_len_to_Any`), method qualification (`get_x` -> `Account@get_x`), and
module qualification (`timedelta` -> `datetime_timedelta`) are all encoded
in those accessors. Translation never applies naming conventions itself.

## Function Signatures

When Resolution encounters a function definition or a call, it builds a
`FuncSig` that carries everything Translation will need:

{docstring Strata.Python.Resolution.FuncSig}

The parameter structure distinguishes instance methods (with an explicit
receiver) from static functions:

{docstring Strata.Python.Resolution.FuncParams}

The receiver is separated from the parameter list so that argument matching
can handle it correctly — the receiver gets its own slot in the zip-fold.
The parameters themselves are split by Python's parameter categories:

{docstring Strata.Python.Resolution.ParamList}

Defaults are resolved expressions (they carry `ResolvedAnn`). This is what
makes the types mutually recursive — `ParamList` stores resolved defaults,
which depend on `ResolvedAnn`, which depends on `NodeInfo`, which depends
on `FuncSig`, which depends on `ParamList`.

## How Resolution Builds Context

Resolution threads a `Ctx` (a `HashMap PythonIdentifier CtxEntry`) as its
fold accumulator. At the top level, each declaration extends it:

- `def f(...)` extends with `.function sig`
- `class C` extends with `.class_ name fields methods`
- `import M` extends with `.module_ moduleCtx` (where moduleCtx is M's resolved Ctx)
- `x : T = ...` extends with `.variable ty`

{docstring Strata.Python.Resolution.CtxEntry}

Within a class body, the context is extended with `self` typed as the
enclosing class (enabling method resolution on `self`) and all methods
registered under their bare names (enabling `self.method()` lookup).

Within a function body, the context is extended with parameters and locals.
Python's scoping rule — any assignment target anywhere in the body is
function-local — is computed upfront:

{docstring Strata.Python.Resolution.computeLocals}

FunctionDef and ClassDef are NOT included in locals. They are declarations,
not assignment targets.

## Import Resolution

Resolution is monadic (`ResolveM := ReaderT System.FilePath (StateT ResolveState (EIO String))`).
The reader carries `baseDir` — the root directory for finding module files.
The state collects resolved imported module programs for Translation and
memoizes already-resolved module paths.

A module is a Ctx. `CtxEntry.module_` carries the module's resolved context:

```
| module_ (moduleCtx : Ctx)
```

### Demand-Driven Loading

Modules are loaded on demand — only when a name from them is actually
referenced. This avoids eagerly loading an entire package (e.g. boto3's 421
submodules) when only one service is used.

The mechanism relies on **qualified type annotations** in generated stubs.
The boto3 `__init__` stub declares:

```python
@overload
def client(service_name: Literal["s3"]) -> boto3.S3: ...
```

The return type `boto3.S3` is an attribute expression (`.Attribute (.Name "boto3") "S3"`),
not a string. It is structured data in the AST.

Loading proceeds lazily:

1. `import boto3` → load `boto3/__init__.python.st.ion` (slim: only `client()` overloads,
   no `from boto3.X import X`). Insert `boto3 → .module_ ctx` with `client` in ctx.

2. `x = boto3.client("s3")` → `resolveMethodCall` looks up `client` in boto3's ctx →
   `.function sig`. The return type annotation is `boto3.S3` (an Attribute expr).

3. `x.list_buckets(...)` → `typeOfExpr` on `x` yields the annotation `boto3.S3`.
   `resolveMethodCall` needs the `S3` class. It walks the attribute chain:
   look up `boto3` → `.module_ ctx` → look up `S3` in ctx → not found →
   **load `boto3/S3.python.st.ion` on demand**, resolve it, insert `S3` into
   boto3's module ctx → now resolve `list_buckets` from `S3`'s methods.

The key insight: the attribute chain `boto3.S3` in the type annotation IS the
load path. No external dispatch table needed. The structured AST contains
the information needed to locate the module file.

### What becomes monadic

Both statement-level AND type-resolution functions operate in `ResolveM`:
- `resolveStmt`, `resolveBlock`, `resolveFuncDef`, `resolveMatchCase` — encounter imports
- `resolveMethodCall`, `typeOfExpr` — may trigger demand-driven loads when
  traversing qualified type annotations through module contexts

`resolveExpr` itself remains pure for most cases. Only the `.Call` case
(which dispatches to `resolveMethodCall`) touches the monad.

### Module file lookup

Given component name `n` and directory `dir`:
1. Try `dir / (n ++ ".python.st.ion")`
2. Try `dir / n / "__init__.python.st.ion"` (package)

### Compiled Module Cache

Imported modules are compiled to Laurel on demand and cached to disk
(analogous to CPython's `.pyc`). The pipeline translates each imported
module's resolved AST with caching:

```
for each imported module (sourcePath, resolvedAST):
  cachePath := sourcePath with ".python.st.ion" → ".laurel.st"
  if cachePath exists on disk:
    load cached Laurel program
  else:
    translate resolvedAST → Laurel program
    write Laurel program to cachePath
  merge Laurel program into combined program
```

The cached Laurel contains only signatures (procedure declarations, type
definitions — no bodies to elaborate). Subsequent runs skip Translation
entirely for cached modules.

### Stub generation convention

Generated library stubs (e.g. boto3) use **qualified attribute references**
for return types, not imports:

```python
# boto3/__init__.py — SLIM, no from-imports of submodules
@overload
def client(service_name: Literal["s3"]) -> boto3.S3: ...
@overload
def client(service_name: Literal["ec2"]) -> boto3.EC2: ...
```

Each service class lives in its own file (`boto3/S3.python.st.ion`).
Only the services actually used by the analyzed program get loaded.

### Query-Based Module Resolution

Imported modules are resolved lazily at the declaration level. Loading a
module does NOT resolve all its statements. Instead:

1. **Index** — scan the module AST for top-level declarations (class names,
   function names, method names within classes). This is a shallow structural
   scan — no body resolution, no type resolution. Fast (O(n) in declaration
   count, not statement count).

2. **Store thunked entries** — the Ctx entry for an imported class stores
   method names with `Thunk FuncSig` for each method's signature. The thunk
   captures the raw AST of the method definition.

3. **Force on demand** — when `resolveMethodCall` needs a specific method's
   signature (e.g. `s3.list_buckets(...)`), it forces that method's thunk.
   This runs `extractFuncSig` on just that one function definition. Other
   methods in the class remain unresolved.

This means loading a 2841-line module (like S3) takes milliseconds (indexing
only). Each method call pays only for resolving one function's parameter list.

The indexing scan is a simple structural match on the AST:
- `FunctionDef name ...` → record function name + raw AST
- `ClassDef name body ...` → record class name, scan body for method names + raw ASTs
- Everything else (TypedDicts, assignments, imports) → skip

### Emitting Demanded Imported Declarations

Imported modules are NOT translated whole. Resolution records exactly the
declarations a user program demands, and the pipeline translates only those.
Three kinds of demand are recorded in `ResolveState`:

- **`demandedMethods`** — when `resolveMethodCall` resolves a class method
  (e.g. `s3.delete_object`), it resolves that method's raw AST into a resolved
  `FunctionDef` (`className = some S3`) and records it. The pipeline runs
  `runTranslation` on these; each becomes an `S3@delete_object` procedure with
  its leading-assert preconditions intact (stub asserts = specs).

- **`demandedFunctions`** — when a call matches a module-level `.function` or
  an `.overloadedFunction` overload (e.g. `boto3.client("s3")` → overload N),
  the matched overload's raw AST is resolved and recorded. The pipeline
  translates it into a `client$N` procedure whose return type is the service
  class (`boto3.S3`).

- **`demandedClasses`** — whenever a method or init of class `S3` is demanded,
  `S3`'s name and field list (captured at index time in the `.class_` entry)
  are recorded. The pipeline emits a `Composite` type definition for each, so
  that `Composite "S3"` referenced by `client$N`'s return type is defined.

The pipeline's Step 3:
1. Translate user code normally via `runTranslation`.
2. Translate `demandedMethods` and `demandedFunctions` (resolved ASTs) into
   procedures.
3. Emit a `Composite` type for each `demandedClass` (fields → `pythonTypeToHighType`).
4. Imported procedures + types form the trusted runtime (not elaborated);
   user code is elaborated normally.

Only what the program touches is translated. The 345 TypedDicts and ~200
uncalled methods of S3 never become Laurel.

## Overload Resolution

Python `@overload` functions define multiple signatures for the same name.
Resolution stores them as an ordered list of `FuncSig` under a single
`CtxEntry`:

```
| overloadedFunction (overloads : List FuncSig)
```

When Resolution encounters a call to an overloaded name, it walks the
overload list in declaration order and checks if the call site's arguments
match the parameter types of each overload. First match wins.

Matching: for each parameter position, check if the argument's static type
(from `typeOfExpr` or literal type) is compatible with the parameter's
declared type. A `Literal["s3"]` parameter matches a string literal `"s3"`.
A `str` parameter matches any string-typed expression. `Any` matches
everything.

The resolved call references a specific overload. Translation emits each
overload as a distinctly-named procedure:

```
client → client$0, client$1, ..., client$N
```

Only the overloads actually referenced by resolved calls are emitted (the
rest are dead code — never translated). The call site's annotation carries
the specific overload's sig, so Translation knows which disambiguated name
to call.

Resolution builds the overload list from consecutive `@overload`-decorated
function definitions with the same name. The `@overload` decorator is
recognized by checking the `decorators` field for a `.Name "overload"` node.

## Method Resolution

When Resolution encounters `receiver.method()`, it needs to determine the
receiver's class to find the method signature. It does this by chasing
_spines_ — `.Name` and `.Attribute` chains:

{docstring Strata.Python.Resolution.typeOfExpr}

- `.Name n` looks up `ctx[n]` to get the variable's type annotation
- `.Attribute obj field` recursively gets the type of `obj`, finds that
  class in ctx, and looks up `field` in its field list

For any non-spine receiver (`.Call`, `.Subscript`, `.IfExp`), Resolution
emits `.unresolved`. This is tech debt — those forms could be resolved by
interpreting return types, but are not yet implemented.

## Attribute Resolution

Every `.Attribute` node gets `.attribute name` where `name` is the bare
Python field name. Resolution does NOT resolve which class the field belongs
to — that requires knowing the receiver's type at use-site, which is
Elaboration's job. Elaboration synthesizes the receiver type and branches:

- Composite receiver: look up the field in the class, emit `readField`
- Any receiver: produce Any (field access on Any is unknowable)

When the Attribute is the callee of a Call (`obj.method()`), the Call
node's annotation carries `.funcCall sig` with the resolved method — the
Attribute's own `.attribute` annotation is irrelevant.

## The Entry Point

{docstring Strata.Python.Resolution.resolve}

The initial context is seeded with Python builtins — each with a correct
`FuncSig` (proper arity, param names, return type):

{docstring Strata.Python.Resolution.builtinContext}

# The Bridge: Accessor Functions
%%%
tag := "accessors"
%%%

Between Resolution and Translation sits a set of accessor functions. These
are the ONLY mechanism by which Translation obtains `Laurel.Identifier`
values. They encode all naming conventions in one place.

{docstring Strata.Python.Resolution.PythonIdentifier.toLaurel}

{docstring Strata.Python.Resolution.FuncSig.laurelName}

{docstring Strata.Python.Resolution.FuncSig.laurelDeclInputs}

{docstring Strata.Python.Resolution.FuncSig.matchArgs}

{docstring Strata.Python.Resolution.FuncSig.laurelLocals}

{docstring Strata.Python.Resolution.FuncSig.laurelReceiver}

`matchArgs` deserves emphasis: it is a zip-fold over parameter slots.
Each slot is filled in order — positional arg first, then kwarg by name,
then resolved default. It includes the receiver slot for instance methods.
It lives in Resolution (not Translation) because it accesses the private
`ParamList` fields and the resolved default expressions.


# Translation
%%%
tag := "translation"
%%%

Given an already-disambiguated AST, Translation emits Laurel by structural
recursion. It pattern matches on `NodeInfo` and calls the accessor
functions above. It never resolves names, never applies naming conventions,
never fabricates identifiers.

## The Writer Monad

Translation needs to emit statements. Most expression translations produce
a single Laurel expression. But some — like class instantiation in
expression position — need to emit prefix statements (`tmp := New cls;
initCall`) and then return a reference (`tmp`). A writer monad handles
this cleanly:

{docstring Strata.Python.Translation.TransM}

`tell` emits statements. `collect` (= `lift . runWriterT`) captures them
at block boundaries. `translateExpr` returns `TransM StmtExprMd` — it may
`tell` prefix statements and return an expression value.

The state carries a fresh name counter and a stack of loop labels (for
break/continue → `Exit` translation):

{docstring Strata.Python.Translation.TransState}

{docstring Strata.Python.Translation.TransError}

## How Translation Uses NodeInfo

_Reference nodes_ (Name, Call, BinOp, Attribute): Translation pattern
matches on `ann.info` and transcribes:

- `.variable name` -> `Identifier name.toLaurel`
- `.funcCall sig` -> `StaticCall sig.laurelName (matchArgs ...)`
- `.classNew cls initSig` -> `tell [New, initCall]; return tmpRef`
- `.attribute name` -> `FieldSelect obj name.toLaurel`
- `.unresolved` -> `Hole`

For operators (BinOp, UnaryOp, Compare, BoolOp), Translation reads
`.funcCall sig` from the annotation. The sig has correct arity (2 for
binary, 1 for unary) and the correct runtime procedure name. Translation
uses `matchArgs` uniformly — no hardcoded argument lists.

_Structural nodes_ (literals, control flow): Translation emits the
corresponding Laurel construct directly — `LiteralInt`, `Block`, `While`,
`IfThenElse`, `Assign`, `Exit`, `Assert`, `Assume`, `LocalVariable`.

_Declaration nodes_ (FunctionDef, ClassDef): Translation reads
`.funcDecl sig` / `.classDecl name fields methods` and emits
`Procedure` / `CompositeType`.

## Params as Mutable Locals

Python parameters are mutable — you can reassign `x` inside a function.
Laurel inputs are immutable. Translation bridges this:

- Procedure inputs are named `$in_X`
- The body declares `LocalVariable X := $in_X` for each param
- The body uses the mutable `X`

## Type Mapping

{docstring Strata.Python.Translation.pythonTypeToHighType}

## The Entry Point

{docstring Strata.Python.Translation.runTranslation}

# Coverage
%%%
tag := "coverage"
%%%

## Precisely Translated

- Literals (int, bool, str, None)
- Variables (identifiers, scope hoisting)
- Binary/comparison/boolean/unary operators (-> prelude StaticCalls)
- Function definitions (params, defaults, kwargs, return)
- Class definitions (fields, methods with self)
- Assignments (simple, augmented, annotated, tuple unpacking)
- Control flow (if/elif/else, while, for, break, continue)
- Return, assert, assume
- Try/except (labeled blocks + isError guards)
- Context managers (with/as -> resolved enter/exit calls)
- List/dict/tuple literals (-> `ListAny_cons`/`DictStrAny_cons` encoding)
- F-strings (-> `to_string_any`)
- Subscript read/write (-> `Any_get`/`Any_sets`)
- Slice notation (-> `from_Slice`)
- Module imports (-> qualified name resolution)
- Class instantiation (-> New + init call)
- Method calls (-> qualified StaticCall with self)

## Approximated (Hole)

Sound but imprecise — the translation produces a nondeterministic Hole
that can take any value, so verification remains sound but cannot prove
properties that depend on the precise semantics.

- Unresolved names (not in context)
- Lambda expressions
- List/set/dict comprehensions
- Generator expressions
- Walrus operator
- Match statements
- Async constructs
- Decorators
- Star expressions
- Float literals (no real arithmetic)

## Unsupported (Translation throws)

- Chained comparisons (`a < b < c`)
- Multiple assignment targets (`x = y = 5`)


# Elaboration
%%%
tag := "elaboration"
%%%

## What Walks In, What Walks Out

Input: a `Laurel.Program`. Output: a `Laurel.Program` with explicit effect
parameters determined by each procedure's grade.

Formally, elaboration translates Laurel derivations into GFGL (Graded
Fine-Grain Laurel) derivations, then projects GFGL back to Laurel. We
present the Laurel type system (source), then GFGL (target), then the
translation.

## Laurel: The Source Type System

Laurel is impure CBV. One judgment form. The context Γ carries variable
bindings (x : A) and label names (l).

$$`\Gamma \vdash e : A`

$$`\frac{}{\Gamma \vdash n : \mathsf{int}} \qquad \frac{}{\Gamma \vdash b : \mathsf{bool}} \qquad \frac{}{\Gamma \vdash s : \mathsf{string}}`

$$`\frac{(x : A) \in \Gamma}{\Gamma \vdash x : A}`

$$`\frac{f : (A_1, \ldots, A_n) \to B \in \Gamma \quad \Gamma \vdash e_i : A_i}{\Gamma \vdash f(e_1, \ldots, e_n) : B}`

$$`\frac{\Gamma \vdash e : C \quad \text{fields}(C, f) = T}{\Gamma \vdash e.f : T}`

$$`\frac{\Gamma \vdash e : \Gamma(x) \quad \Gamma \vdash \text{rest} : A}{\Gamma \vdash (x := e);\ \text{rest} : A}`

$$`\frac{\Gamma \vdash e : T \quad \Gamma, x{:}T \vdash \text{rest} : A}{\Gamma \vdash (\mathbf{var}\ x{:}T := e);\ \text{rest} : A}`

$$`\frac{\Gamma \vdash c : \mathsf{bool} \quad \Gamma \vdash t : A \quad \Gamma \vdash f : A \quad \Gamma \vdash \text{rest} : A}{\Gamma \vdash (\mathbf{if}\ c\ \mathbf{then}\ t\ \mathbf{else}\ f);\ \text{rest} : A}`

$$`\frac{\Gamma \vdash c : \mathsf{bool} \quad \Gamma \vdash \text{body} : A \quad \Gamma \vdash \text{rest} : A}{\Gamma \vdash (\mathbf{while}\ c\ \mathbf{do}\ \text{body});\ \text{rest} : A}`

$$`\frac{\Gamma, l \vdash \text{body} : A \quad \Gamma \vdash \text{rest} : A}{\Gamma \vdash \{\text{body}\}_l;\ \text{rest} : A}`

$$`\frac{l \in \Gamma}{\Gamma \vdash \mathbf{exit}\ l : A}`

$$`\frac{\Gamma \vdash c : \mathsf{bool} \quad \Gamma \vdash \text{rest} : A}{\Gamma \vdash (\mathbf{assert}\ c);\ \text{rest} : A}`

$$`\frac{\Gamma \vdash \text{obj} : C \quad \Gamma \vdash v : \text{fieldType}(C, f) \quad \Gamma \vdash \text{rest} : A}{\Gamma \vdash (\text{obj}.f := v);\ \text{rest} : A}`

$$`\frac{}{\Gamma \vdash \mathbf{skip} : \mathsf{TVoid}}`

## GFGL: The Type System

GFGL has two sorts — values (pure, duplicable) and producers (effectful,
carry a continuation). Typing is bidirectional with four judgment forms:

$$`\Gamma \vdash V \Rightarrow A \qquad \Gamma \vdash V \Leftarrow A \qquad \Gamma \vdash M \Rightarrow A\ \&\ d \qquad \Gamma \vdash M \Leftarrow A\ \&\ e`

### Types

{docstring Strata.FineGrainLaurel.LowType}

### Grades

{docstring Strata.FineGrainLaurel.Grade}

{docstring Strata.FineGrainLaurel.Grade.leftResidual}

### Terms

{docstring Strata.FineGrainLaurel.FGLValue}

{docstring Strata.FineGrainLaurel.FGLProducer}

### Subtyping: A ≤ B ↦ c

`subtype` is a total case analysis of the coercion relation over `LowType`. Every
ordered pair `(A, B)` is decided: `.refl` when `A = B`, `.coerce w` when Python
performs an implicit conversion `A → B` (witnessed by one direct runtime
function), and `.unrelated` otherwise. `.unrelated` is a deliberate verdict per
pair, not a fall-through for forgotten cases.

`LowType.TCore` carries an open name string, so the relation cannot match one arm
per name. It decides the finite set of core types that `eraseType` produces
(`Any`, `Composite`, `ListAny`, `DictStrAny`, …); any unrecognized `TCore` name
is `.unrelated`, the sound default for a type the relation knows nothing about.

The coercion families, all witnessed by functions in the runtime:

- **box** (`T ≤ Any`): the value constructors `from_int`, `from_str`, `from_bool`,
  `from_float`, `from_Composite`, `from_ListAny`, `from_DictStrAny`, `from_None`.
- **unbox** (`Any ≤ T`): the projections `Any_to_bool`, `Any..as_int!`,
  `Any..as_string!`, `Any..as_float!`, `Any..as_Composite!`, `Any..as_Dict!`,
  `Any..as_ListAny!`.
- **truthiness** (`T ≤ bool`): Python's `bool(x)` per type — `int_to_bool`,
  `str_to_bool`, `float_to_bool`, `list_to_bool`, `dict_to_bool`, `None ↦ false`,
  `Composite ↦ true` (objects are truthy by default).
- **numeric** (`bool ≤ int ≤ float`): `bool_to_int`, `int_to_real`, `bool_to_real`
  — Python's numeric tower for arithmetic.

`subtype` returns one witness; the elaborator applies it once at each typing
boundary (only from `checkValue`) and never chains two `subtype` results, so each
pair needs only its single direct witness.

{docstring Strata.FineGrainLaurel.subtype}

### Subgrading: d ≤ e ↦ (pre, outs)

{docstring Strata.FineGrainLaurel.mkGradedCall}

### Runtime Interface (Heap Model)

{docstring Strata.Laurel.heapConstants}

### Value Synthesis: Γ ⊢ V ⇒ A

$$`\frac{}{\Gamma \vdash \mathsf{litInt}\ n \Rightarrow \mathsf{TInt}} \qquad \frac{}{\Gamma \vdash \mathsf{litBool}\ b \Rightarrow \mathsf{TBool}} \qquad \frac{}{\Gamma \vdash \mathsf{litString}\ s \Rightarrow \mathsf{TString}}`

$$`\frac{(x : A) \in \Gamma}{\Gamma \vdash \mathsf{var}\ x \Rightarrow A}`

$$`\frac{f : (A_1, \ldots, A_n) \to B\ \&\ \mathsf{pure} \quad \Gamma \vdash V_i \Leftarrow A_i}{\Gamma \vdash \mathsf{functionCall}\ f\ [V_1, \ldots, V_n] \Rightarrow B}`

### Value Checking: Γ ⊢ V ⇐ A

$$`\frac{\Gamma \vdash V \Rightarrow B \quad B \leq A \mapsto c}{\Gamma \vdash c(V) \Leftarrow A}`

### Producer Synthesis: Γ ⊢ M ⇒ A & d

Exactly one rule:

$$`\frac{f : (A_1, \ldots, A_n) \to B\ \&\ d \quad \Gamma \vdash V_i \Leftarrow A_i}{\Gamma \vdash \mathsf{procedureCall}\ f\ [V_1, \ldots, V_n] \Rightarrow B\ \&\ d}`

### Producer Checking: Γ ⊢ M ⇐ A & e

$$`\frac{\Gamma \vdash \mathsf{procedureCall}\ f\ [V_i] \Rightarrow B\ \&\ d \quad d \leq e \mapsto (\text{pre}, \text{outs}) \quad \Gamma, \text{outs} \vdash K \Leftarrow A\ \&\ (d \backslash e)}{\Gamma \vdash \mathsf{procedureCall}\ f\ (\text{pre} \mathbin{++} [V_i])\ \text{outs}\ K \Leftarrow A\ \&\ e}`


$$`\frac{\Gamma \vdash V \Leftarrow \mathsf{bool} \quad \Gamma \vdash M_t \Leftarrow A\ \&\ e \quad \Gamma \vdash M_f \Leftarrow A\ \&\ e \quad \Gamma \vdash K \Leftarrow A\ \&\ e}{\Gamma \vdash \mathsf{ifThenElse}\ V\ M_t\ M_f\ K \Leftarrow A\ \&\ e}`

$$`\frac{\Gamma \vdash V \Leftarrow \mathsf{bool} \quad \Gamma \vdash M_b \Leftarrow A\ \&\ e \quad \Gamma \vdash K \Leftarrow A\ \&\ e}{\Gamma \vdash \mathsf{whileLoop}\ V\ M_b\ K \Leftarrow A\ \&\ e}`

$$`\frac{\Gamma \vdash V \Leftarrow A}{\Gamma \vdash \mathsf{produce}\ V \Leftarrow A\ \&\ e} \qquad \frac{l \in \Gamma}{\Gamma \vdash \mathsf{exit}\ l \Leftarrow A\ \&\ e}`

$$`\frac{\Gamma \vdash M \Leftarrow \Gamma(x)\ \&\ e \quad \Gamma \vdash K \Leftarrow A\ \&\ e}{\Gamma \vdash \mathsf{assign}\ x\ M\ K \Leftarrow A\ \&\ e}`

$$`\frac{\Gamma \vdash M \Leftarrow T\ \&\ e \quad \Gamma, x{:}T \vdash K \Leftarrow A\ \&\ e}{\Gamma \vdash \mathsf{varDecl}\ x\ T\ M\ K \Leftarrow A\ \&\ e}`

$$`\frac{\Gamma \vdash V \Leftarrow \mathsf{bool} \quad \Gamma \vdash K \Leftarrow A\ \&\ e}{\Gamma \vdash \mathsf{assert}\ V\ K \Leftarrow A\ \&\ e}`

$$`\frac{\Gamma, l \vdash M_b \Leftarrow A\ \&\ e \quad \Gamma \vdash K \Leftarrow A\ \&\ e}{\Gamma \vdash \mathsf{labeledBlock}\ l\ M_b\ K \Leftarrow A\ \&\ e}`

## The Translation ⟦·⟧ : Laurel → GFGL

The translation is a transformation of Laurel typing derivations
(`Γ ⊢ e : A`) into GFGL producer checking derivations
(`⟦Γ⟧ ⊢ M ⇐ ⟦A⟧ & d`). Every Laurel derivation maps to a producer —
even literals and variables (they become `produce V`). This is the
CBV-to-FGCBV embedding.

Three functions:

```
⟦·⟧⇐ₚ : (Γ : LaurelCtx) → (s : StmtExpr) → (k : List StmtExpr)
       → (A : HighType) → (d : Grade)
       → (Γ ⊢ s;k : A)
       → ∃(M : FGLProducer). (⟦Γ⟧ ⊢ M ⇐ ⟦A⟧ & d)

⟦·⟧⇒ᵥ : (Γ : LaurelCtx) → (e : StmtExpr)
       → ∃(A : HighType). (Γ ⊢ e : A)
       → ∃(V : FGLValue). (⟦Γ⟧ ⊢ V ⇒ ⟦A⟧)

⟦·⟧⇐ᵥ : (Γ : LaurelCtx) → (e : StmtExpr) → (A : HighType)
       → (Γ ⊢ e : A)
       → ∃(V : FGLValue). (⟦Γ⟧ ⊢ V ⇐ ⟦A⟧)
```

`⟦·⟧⇐ₚ` (`checkProducer`) is the entry point. `⟦·⟧⇒ᵥ` (`synthValue`)
and `⟦·⟧⇐ᵥ` (`checkValue`) build value sub-terms inside producer forms.
Producer synthesis (⟦·⟧⇒ₚ) is handled by inversion within
`checkProducerStaticCall` — the single synthesis rule is always a call.

### Setup: Environment and Grades

Before translating, we build Γ from the program declarations and
infer grades for each procedure.

{docstring Strata.FineGrainLaurel.buildElabEnvFromProgram}

{docstring Strata.FineGrainLaurel.ElabTypeEnv}

{docstring Strata.FineGrainLaurel.ElabEnv}

{docstring Strata.FineGrainLaurel.ElabState}

{docstring Strata.FineGrainLaurel.fullElaborate}

`fullElaborate` runs two passes:

1. _Grade inference_ (pass 1): For each user procedure, try elaborating its
   body at grade `pure`, then `proc`, then `err`, then `heap`, then `heapErr`.
   The first grade where elaboration succeeds (returns `some`) is that
   procedure's grade. Iterate to fixpoint — when a callee's grade changes,
   re-elaborate its callers. Convergence is guaranteed by the finite lattice.

2. _Term production_ (pass 2): With grades fixed, elaborate each procedure's
   body at its inferred grade. Pass 1 guarantees this succeeds. Project the
   resulting GFGL term back to Laurel.

Runtime procedure grades are not inferred — they're read from the signature
by `gradeFromSignature` (does it have a Heap input? An Error output?).

### Procedure bodies are commands (checked at `TVoid`)

Both passes elaborate the body at expected type `.TVoid`, not the procedure's
return type. A translated procedure body is a statement command, not a value:
Python statements do not return their last expression, and `return e` was already
lowered by Translation to `LaurelResult := e; exit`. So the value, when there is
one, flows through that explicit assignment — which `checkAssign` types against
`LaurelResult`'s own declared type, independent of the ambient expected type.

Checking the body at the return type instead would conflate the two. A loop body
or branch arm whose last statement is a void call (`print(...)`) would have that
call's `()` result coerced toward the declared return type and projected as a
spurious `LaurelResult := from_None()` — ill-typed when the return type is a
scalar (`Impossible to unify Any with string`). At `.TVoid` no such coercion
arises, and the void tail projects to nothing (see Projection's optional
destination). The return value reaches `LaurelResult` only through the `return`
assignment.

### Preconditions

A `requires` clause is a pure value of type `bool` — no effects, no sequencing,
no continuation — so pass 2 elaborates it with the value judgment `checkValue`
(expected type `.TBool`), not the producer judgment that elaborates bodies.
`checkValue` synthesizes the term and applies the subtyping coercions —
`from_int`/`from_str` on the argument literals (the runtime operators take `Any`
parameters) and `Any_to_bool` on the `Any`-typed result — and `projectValue`
yields the single Core expression that replaces the clause. Holes it uses are
collected into the program's hole procedures alongside the body's.

A precondition may contain a hole — e.g. a stub assert
`re.compile(...).search(kwargs["RoleName"]) is not None`, where `re` is unmodeled
so the subterm is a hole. In a body such a hole is nondeterministic havoc, but in
a pure value position nondeterminism has no meaning: the value must be a
deterministic function of what is in scope. So `checkValue`'s `.Hole` case
elaborates *any* hole as the deterministic `hole_N(inputs)` (an uninterpreted
pure function of the procedure's inputs), regardless of how Translation marked it.
The contract stays well-typed and the resulting caller obligation is sound but
uninterpretable — verification is inconclusive, never unsound, and no conjunct is
dropped.

Translation emits preconditions in surface form, e.g.
`PGe(Any_len_to_Any(Any_get($in_kwargs, "Key")), 1)` — bare `intConst 1` and
`strConst "Key"`, and an `Any`-typed `PGe(...)` standing in a `bool` position.
Without this step those terms reach Core uncoerced; the Core type checker reports
`Impossible to unify Any with (arrow Any (arrow Any Any))` at the clause's source
range.

{docstring Strata.FineGrainLaurel.gradeFromSignature}

### Type Erasure: ⟦·⟧ on types

{docstring Strata.FineGrainLaurel.eraseType}

### `checkProducer` — the entry point (⟦·⟧⇐ₚ)

Each case in the pattern match translates a Laurel statement into the
corresponding GFGL producer checking derivation. The `k` parameter
is the continuation — `checkProducers(k, A, d)` translates it.

- `.IfThenElse` → `checkProducerIf`
- `.While` → `checkProducerWhile`
- `.Exit` → exit rule (inline)
- `.LocalVariable` → `checkProducerVarDecl`
- `.Assert` / `.Assume` → `checkProducerAssert` / `checkProducerAssume`
- `.Block` → `checkProducerBlock`
- `.Assign` → `checkAssign` (dispatches on LHS/RHS)
- `.StaticCall` → `checkProducerStaticCall` (bare call, discards return value)
- `.New` → failure (bare `new` in statement position is pathological)
- `.Hole` → inline (deterministic or nondeterministic)
- `.Return` / `.InstanceCall` → failure (not yet supported)
- All other `StmtExpr` constructors → failure (bare value expressions are ill-typed in Laurel)

{docstring Strata.FineGrainLaurel.checkProducer}

The clause helpers, each implementing one translation rule:

{docstring Strata.FineGrainLaurel.checkProducerIf}

{docstring Strata.FineGrainLaurel.checkProducerWhile}

{docstring Strata.FineGrainLaurel.checkProducerVarDecl}

{docstring Strata.FineGrainLaurel.checkProducerAssert}

{docstring Strata.FineGrainLaurel.checkProducerAssume}

{docstring Strata.FineGrainLaurel.checkProducerStaticCall}

{docstring Strata.FineGrainLaurel.checkProducerBlock}

### `checkAssign` — assignment elaboration

Dispatches on LHS to get the assignee, then on RHS:

- `.FieldSelect` LHS → `checkAssignFieldWrite` (heap write)
- `.Identifier` LHS, `.StaticCall` RHS → `checkAssignStaticCall`
- `.Identifier` LHS, `.New` RHS → `checkAssignNew`
- `.Identifier` LHS, other RHS → `checkAssignVar`

`StaticCall` and `New` RHS need the assignee inside the effect scope.

{docstring Strata.FineGrainLaurel.checkAssign}

{docstring Strata.FineGrainLaurel.checkAssignVar}

{docstring Strata.FineGrainLaurel.checkAssignStaticCall}

{docstring Strata.FineGrainLaurel.checkAssignNew}

{docstring Strata.FineGrainLaurel.checkAssignFieldWrite}

### `checkValue` — internal helper (⟦·⟧⇐ᵥ)

Calls `synthValue`, then applies the coercion from `subtype`.

{docstring Strata.FineGrainLaurel.checkValue}

### `synthValue` — internal helper (⟦·⟧⇒ᵥ)

Called by `checkValue`. Discovers the value and its type. Operates on
expressions already in value form (bound variables, literals, pure calls).

{docstring Strata.FineGrainLaurel.synthValue}

{docstring Strata.FineGrainLaurel.synthValueLiteral}

{docstring Strata.FineGrainLaurel.synthValueVar}

{docstring Strata.FineGrainLaurel.synthValueFieldSelect}

{docstring Strata.FineGrainLaurel.synthValueStaticCall}

## Projection: GFGL → Laurel (Destination Passing Style)

Elaboration maps Laurel derivations (`Γ ⊢ e : A`) to GFGL derivations
(`⟦Γ⟧ ⊢ M ⇐ ⟦A⟧ & d`). Projection reverses this:

```
⟦D⟧ₓ⁻¹ : (⟦Γ⟧ ⊢ M ⇐ ⟦A⟧ & d) → ∃e⃗. (Γ, x : A ⊢ e⃗ : TVoid)
```

Given a GFGL checking derivation `D` and a destination variable `x : A`,
projection produces a Laurel statement list `e⃗` that assigns to `x`.
One GFGL rule maps to one or more Laurel typing rules in the output.

The destination is **optional**: `x : A` may be omitted. A producer whose value
has nowhere to go (a `TVoid` command — see "Procedure bodies are commands"
below) projects with no destination, and its tail `produce` emits no assignment
at all rather than `x := v`. This is the only correct reading when there is no
`x : A` in the context: there is nothing to assign to.

```
proj : Option StmtExprMd → FGLProducer → List StmtExprMd
```

The destination threads down unchanged through control flow (`if`/`while`/
labeled block) and through a procedure call's continuation; an assignment's RHS
subproducer is projected with `some target`, so `x := f()` still writes `x` even
inside a void body. `projProduce none` yields `[]`; `projProduce (some d)` yields
`d := v`.

The top-level body is projected with no destination (`none`). A `return e` was
already lowered by Translation to `LaurelResult := e; exit`, so the returned
value reaches `LaurelResult` through that explicit assignment, not through the
body's tail.

Each helper carries its derivation tree showing the GFGL rule on top
and the Laurel rules on bottom:

{docstring Strata.FineGrainLaurel.proj}

{docstring Strata.FineGrainLaurel.projProduce}

{docstring Strata.FineGrainLaurel.projVarDecl}

{docstring Strata.FineGrainLaurel.projAssign}

{docstring Strata.FineGrainLaurel.projIfThenElse}

{docstring Strata.FineGrainLaurel.projWhileLoop}

{docstring Strata.FineGrainLaurel.projProcedureCall}

{docstring Strata.FineGrainLaurel.projAssert}

{docstring Strata.FineGrainLaurel.projAssume}

{docstring Strata.FineGrainLaurel.projLabeledBlock}

{docstring Strata.FineGrainLaurel.projExit}

{docstring Strata.FineGrainLaurel.projSkip}

# Tech Debt
%%%
tag := "tech_debt"
%%%

- _Instance procedures:_ Methods are emitted as top-level statics with
  `self` as first param. The `instanceProcedures` field on CompositeType
  is empty.
- _Spine resolution incomplete:_ Non-spine receivers emit `.unresolved`.
- _Match case pattern bindings:_ Not extracted as locals (requires walking
  `Python.pattern`).
- _Loop labels:_ Push/pop on mutable state. Should be reader monad.
- _Multi-output forces err grade:_ Translation declares `maybe_except`
  on every procedure, causing grade inference to always join with err.
