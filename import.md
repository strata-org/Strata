# Import Resolution Plan

## Problem

Module-level imports (`import boto3`, `from botocore.exceptions import ClientError`)
are only visible inside `@module_init`. Other functions see these names as unresolved,
producing `unsupported "Unresolved name: X"` instructions that make the SSA value
unusable. This accounts for 273 of 289 remaining corpus warnings.

### Root cause

`translateModule` builds `moduleBindings` (line 1622-1628) from function/class
definitions only. Import statements are processed by `translateSimpleStmt` when
encountered during `@module_init` body translation. Other functions don't inherit
these bindings.

### Three categories of unresolved names

| Category | Count | Examples | Fix |
|----------|-------|----------|-----|
| Module-level imports used in functions | ~200 | `boto3`, `json`, `sys`, `ClientError` | Collect import bindings and propagate to all functions |
| `__name__` | 44 | `if __name__ == '__main__'` | Add to prelude as `qualifiedRef builtins.__name__` |
| Module-level variable assignments | ~25 | `logger = getLogger(...)`, `region = ...` | Out of scope for this change — these are runtime values, not imports |

## Design

### Step 1: Collect import bindings at module level

Add a function that scans top-level statements for `Import` and `ImportFrom` and
builds a `Std.HashMap String QualifiedName`, parallel to how `collectModuleGlobals`
works. This runs before `translateFunc`.

```lean
private def collectImportBindings (stmts : Array (stmt SourceRange))
    : Std.HashMap String QualifiedName := Id.run do
  let mut bindings : Std.HashMap String QualifiedName := {}
  for s in stmts do
    match s with
    | .Import _ ⟨_, aliases⟩ =>
      for a in aliases do
        let modName := a.name
        let localName := a.asname.getD modName
        bindings := bindings.insert localName (QualifiedName.mk' modName modName)
    | .ImportFrom _ ⟨_, modOpt⟩ ⟨_, aliases⟩ _ =>
      let modName := match modOpt with
        | some ⟨_, m⟩ => m | none => "unknown"
      for a in aliases do
        let localName := a.asname.getD a.name
        bindings := bindings.insert localName (QualifiedName.mk' modName a.name)
    | _ => pure ()
  return bindings
```

This mirrors the existing `Import`/`ImportFrom` handling in `translateSimpleStmt`
(lines 1081-1096) but runs statically before translation.

### Step 2: Merge import bindings into moduleBindings

In `translateModule`, merge the import bindings into `moduleBindings` so every
function sees them:

```lean
let importBindings := collectImportBindings stmts
let moduleBindings := importBindings.fold (init := moduleBindings) fun acc k v =>
  acc.insert k v
```

Function/class definitions take precedence over imports (same shadowing as Python).
Since `moduleBindings` is built after `importBindings`, the fold order handles this
correctly — function names overwrite import names if they collide.

### Step 3: Add `__name__` to prelude

`__name__` is a module-level special variable. Add it to `pythonPrelude` in IR.lean:

```lean
mk "__name__",
```

This resolves to `qualifiedRef builtins.__name__` — an opaque value of type `str`.
Not strictly a builtin, but the right pragmatic choice: every module has it, and
for static analysis purposes the value is always either `"__main__"` or the module
name (both strings).

### Step 4: Exclude import bindings from demand analysis

Import-bound names are already excluded from demand analysis via `globals` (which
includes imports from `collectModuleGlobals`). The `preludeGlobals` set added for
the prelude fix also covers prelude names. No additional changes needed here —
the import bindings will resolve via `lookupVar`'s `varEnv` check before reaching
the demand-driven block parameter path.

Actually: the `globals` set in `collectModuleGlobals` already includes import
names (lines 83-88). And these globals are passed through `FuncInfo.globals` to
`demandAnalysis`. So import names are already excluded from block params. The
only missing piece was that they weren't in `varEnv` for `lookupVar` — which
Steps 1-2 fix.

## Impact

### Before
- 289 total warnings across 51 corpus files
- 273 are unresolved names from imports
- 44 are `__name__`

### After (expected)
- ~25 warnings remaining (module-level variable assignments like `logger`, `region`)
- These are genuine runtime values that can't be resolved statically without
  executing the code or providing type stubs

### Unresolved names that will remain

| Name | Count | Source | Why unresolvable |
|------|-------|--------|------------------|
| `logger` | 19 | `logger = logging.getLogger(...)` | Runtime assignment |
| `region` | 3 | `region = os.environ.get(...)` | Runtime assignment |
| `job_settings` | 1 | Config variable | Runtime assignment |
| `impact_analysis` | 1 | Variable | Runtime assignment |
| `filter_msg` | 1 | Variable | Runtime assignment |

These are not imports — they're module-level variable assignments whose values
depend on runtime state. The correct SSA output for these is `undef("name")`
(the variable exists but its initial value is unknown at translation time).
Currently they emit `unsupported "Unresolved name"` which is slightly wrong —
the name *is* resolved (it's a module variable), we just don't know its value.

A future improvement could scan module-level assignments and bind them as
`local` values with `undef`, but that's out of scope here.

## Test plan

### New test: extend t17_import.py

The existing `t17_import.py` tests import handling at module init level. Add a
function that uses imported names to verify cross-function resolution:

```python
import json
from os.path import join

def use_imports():
    data = json.dumps({"key": "value"})
    path = join("/tmp", "output.txt")
    return data
```

Expected: `json.dumps(...)` → `callQualified json.dumps`, `join(...)` →
`callQualified os.path.join`.

### Verify existing tests still pass

The prelude and import changes affect name resolution globally. Regenerate
expected files and verify 34/34.

### Corpus re-validation

Run all 51 corpus files. Expected: warnings drop from 289 to ~25.

## Implementation sequence

1. Write extended t17_import.py test cases
2. Add `collectImportBindings` function
3. Merge import bindings into `moduleBindings` in `translateModule`
4. Add `__name__` to `pythonPrelude`
5. Run tests, iterate on expected output
6. Re-validate corpus
7. Update experiment_report.md with Phase 18 results
