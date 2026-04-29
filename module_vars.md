# Module-Level Variable Plan

## Problem

Module-level assignments like `logger = logging.getLogger(...)` are translated
inside `@module_init` but invisible to other functions. Functions that reference
`logger` get `unsupported "Unresolved name: logger"`, which is wrong — the name
*is* resolved (it's a module-level global), we just don't know its value statically.

## Design (based on A.py/B.py test)

Python's actual semantics: module-level `x = 1` in module M creates `M.x`.
Functions in M that reference `x` are reading `M.x` — a module attribute.
External code accesses it as `M.x` too (and can mutate it, as B.py shows).

So the correct SSA representation is: functions see unresolved module-level
names as `qualifiedRef M.name`. This is:
- Semantically accurate (it IS a module attribute)
- Consistent with how imports work (they're also qualifiedRef)
- Useful for downstream analysis (the qualified name tells you where to look)

### What changes

In `translateModule`:
1. Scan top-level statements for assignment targets (`Assign`, `AnnAssign`,
   `AugAssign` with `Name` targets)
2. Add them to `moduleBindings` as `QualifiedName.mk' moduleName name`
3. Functions/classes/imports take precedence (they're added after)

In `collectModuleGlobals`:
1. Also collect assignment targets so demand analysis excludes them from
   block parameters

### SSA output example

For module "M" with `logger = logging.getLogger(__name__)`:

```
func foo():
  bb0():
    %0:logger = qualifiedRef M.logger
    %1 = call attr(%0, "info")(positional(strLit "hello"))
    ret
```

### Precedence (matches Python)

1. Function parameters — shadow everything
2. Local assignments — shadow after the assignment point
3. Imports (`import X`, `from X import Y`) — qualifiedRef to the imported module
4. Module-level assignments — qualifiedRef to M.name
5. Prelude builtins — qualifiedRef to builtins.name

If a name is both imported and assigned at module level, the import wins
because `moduleBindings` from imports overwrites the assignment entry
(imports are processed after assignments in the merge order).

## Implementation

Combined with the import fix from import.md:

### Step 1: `collectImportBindings`

Scans imports and returns `Std.HashMap String QualifiedName`.

### Step 2: `collectModuleAssignments`

Scans `Assign`/`AnnAssign`/`AugAssign` targets and returns `Std.HashSet String`.

### Step 3: Build `moduleBindings` in `translateModule`

```
assignments (qualifiedRef M.x)  →  imports (qualifiedRef X.y)  →  functions/classes
```

Later entries overwrite earlier ones, giving correct precedence.

### Step 4: Update `collectModuleGlobals`

Add assignment targets so demand analysis excludes them from block params.

### Step 5: Add `__name__` to prelude

Every module has it; treating it as `qualifiedRef builtins.__name__` is correct.

## Test: t27_module_vars.py

Covers:
- Simple module var used in a function (`logger`, `MAX_RETRIES`)
- Annotated assignment used in a function (`threshold`)
- Function parameter shadows module var (`param_shadows_module_var`)
- Local assignment shadows module var (`local_shadows_module_var`)
- Mixed imports and module vars in one function (`mixed_imports_and_vars`)
