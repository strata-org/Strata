# Known Bugs in BoogieToStrata

## 1. Function parameter names can shadow type synonyms

**Status**: Open

### Description

When BoogieToStrata emits function definitions, it preserves Boogie's original
parameter names verbatim (after sanitization via `SanitizeNameForStrata`). If a
parameter name happens to match a type synonym name, the Strata parser cannot
disambiguate between the parameter and the type, producing a parse error.

### Triggering example

Given this Boogie input:

```boogie
type i1 = int;

function $add.i1(i1: i1, i2: i1) returns (i1) { i1 + i2 }
```

BoogieToStrata produces:

```
type i1 := int;

function _add_i1(i1 : i1, i2 : i1) : (i1) {
  (i1 + i2)
}
```

Strata rejects this with:

```
error: Expected a type instead of i1
```

The parser sees `i1` in the position `param_name : i1` and cannot resolve `i1` as
a type because it has already been bound as a parameter name in scope.

### Impact

This affects **all** SMACK-generated Boogie files because SMACK's integer type
definitions use `type i1 = int; type i8 = int; ...` and the corresponding
arithmetic functions use matching parameter names (e.g., `$add.i1(i1: i1, i2: i1)`).

### Root cause

`StrataGenerator.cs` line 1788 in `WriteFormals`:

```csharp
var name = v.TypedIdent.Name ?? "";
if (name == "") name = $"x{n++}";
WriteText($"{prefix}{Name(name)} : ");
```

The emitted name is sanitized (dots/dollars removed) but never checked against
type names in scope.

### Suggested fixes

**Option A — Rename conflicting parameters during emission (simplest)**:

In `WriteFormals`, check if the sanitized parameter name matches any type synonym
or type constructor name in the program. If so, prefix it (e.g., `p_i1` or `arg_i1`):

```csharp
var name = v.TypedIdent.Name ?? "";
if (name == "") name = $"x{n++}";
var sanitized = Name(name);
if (_typeSynonymNames.Contains(sanitized) || _typeCtorNames.Contains(sanitized))
    sanitized = $"p_{sanitized}";
WriteText($"{prefix}{sanitized} : ");
```

This requires collecting type names into a `HashSet<string>` during `FindSpecialTypes()`
or at the start of `EmitProgramAsStrata`.

**Option B — Rename in VisitFunction specifically for function bodies**:

Since the parameter names also appear in the function body expression, you'd need
to also apply the renaming when visiting `IdentifierExpr` nodes within function
bodies. A substitution map scoped to `VisitFunction` would handle this.

**Option C — Quote identifiers in Strata**:

If Strata's parser supported quoted identifiers (e.g., `|i1|`), this would resolve
all naming conflicts. However, this requires changes to the Strata parser.

### Recommendation

Option A is the least invasive. The set of type synonyms is known at emission time,
so a simple prefix avoids the collision. The body references will also match because
Boogie uses the same name in `IdentifierExpr` nodes, so renaming must be applied
consistently in both the signature and the body.

---

## 2. Function definitions emitted in declaration order cause forward references

**Status**: Open

### Description

BoogieToStrata emits functions in the order they appear in Boogie's
`TopLevelDeclarations`. When an inline function references another inline function
defined later in the file, the Strata parser rejects it as an "Unknown variable."

### Triggering example

```boogie
function {:inline} $isExternal(p: ref) returns (bool) { $slt.ref.bool(p, $EXTERNS_BOTTOM) }
// ... 3000 lines later ...
function {:inline} $slt.ref.bool(p1: ref, p2: ref) returns (bool) { p1 < p2 }
```

BoogieToStrata emits `_isExternal` before `_slt_ref_bool`, producing:

```
function _isExternal(p : ref) : (bool) {
  _slt_ref_bool(p, _EXTERNS_BOTTOM)
}
// ... much later ...
function _slt_ref_bool(p1 : ref, p2 : ref) : (bool) {
  (p1 < p2)
}
```

Strata error:

```
error: Unknown variable _slt_ref_bool
```

### Impact

Affects all SMACK-generated files because SMACK's prelude has many inline functions
with inter-dependencies that don't follow declaration order.

### Root cause

`StrataGenerator.cs` line 104-107:

```csharp
var functions = liveDeclarations.OfType<Function>().ToList();
if (functions.Count != 0) {
    generator.WriteLine("// Functions");
    functions.ForEach(f => generator.VisitFunction(f));
}
```

Functions are emitted in declaration order without dependency analysis.

### Suggested fixes

**Option A — Topological sort (recommended)**:

Before emitting, build a dependency graph among functions (each function depends on
functions it calls in its body) and emit them in topological order:

```csharp
var functions = liveDeclarations.OfType<Function>().ToList();
var sorted = TopologicalSort(functions, f => GetCalledFunctions(f.Body, functions));
sorted.ForEach(f => generator.VisitFunction(f));
```

**Option B — Two-pass emission**:

First emit all function signatures (declarations without bodies), then emit bodies.
This requires Strata to support forward-declared functions, which it may already do
for functions without bodies (uninterpreted functions).

**Option C — Emit declarations for all functions first**:

Before the definitions section, emit `function name(params) : (rettype);` for every
function that will later have a body. This acts as a forward declaration.
