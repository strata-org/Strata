# SSA Translation Pipeline Steps

## Input

Python source → `py_to_strata` → Ion binary (`*.python.st.ion`) → `readPythonStrataBytes` → `Array (stmt SourceRange)`

## Entry Point: `translateModule`

Takes a module name and the top-level statement array. Returns `TranslateResult` (Module + warnings).

### Step 1: Scan module structure — `scanModule`

Splits the top-level statement array into `FuncInfo` records:
- Each `FunctionDef` / `AsyncFunctionDef` → one `FuncInfo`
- Each `ClassDef` → one `FuncInfo` per method, plus `@ClassName_init` for class-body statements
- Remaining top-level statements → `@module_init`

Also runs `collectModuleGlobals` to build a `HashSet String` of names that are
"external" to each function (won't become block parameters):
- Function names, class names, import names
- For non-init functions: also includes module-level assignment targets (`funcGlobals`)
- For `@module_init`: does NOT include assignment targets (they're local to init)

USER: Should assignment targets in @module_init be globals?

### Step 2: Collect module-level bindings

Three scans over the top-level statements, building `moduleBindings : HashMap String QualifiedName`:

| Scan | Function | What it collects | Precedence |
|------|----------|------------------|------------|
| Implicit | (inline) | `__name__` → `M.__name__` | Lowest |
| Assignments | `collectModuleAssignments` | `Assign`, `AnnAssign`, `AugAssign` with `Name` targets → `M.name` | Low |
| Imports | `collectImportBindings` | `Import`, `ImportFrom` → qualified refs (e.g., `boto3.boto3`, `os.path.join`) | Medium |
| Functions/Classes | (inline fold over `scanModule` results) | `funcName` → `M.funcName`, `className` → `M.className` | Highest |

Later entries overwrite earlier ones, so functions/classes shadow imports shadow assignments.

USER: Should we warn about overwriting these?

**Limitation:** `collectModuleAssignments` only scans top-level statements. Assignments nested inside `if __name__ == "__main__":` are not collected.

USER: Can collectModuleGlobals and collectModuleAssignments be combined?

### Step 3: Translate each function — `translateFunc`

Called once per `FuncInfo`. Pure function (no IO). Steps within:

#### 3a: Initialize varEnv from moduleBindings

Every function starts with `varEnv` populated from `moduleBindings` — all entries become `Binding.qualified`. This is how functions see imports, module-level assignments, and sibling function/class names.

#### 3b: Bind function parameters

Each parameter gets a fresh `SSAVal` and is bound in `varEnv` as `Binding.local`. Parameters shadow module bindings of the same name.

#### 3c: Demand analysis — `demandAnalysis2` (in Blockify.lean)

Computes which variables each block needs as parameters. Two stages:

1. **Forward summary pass** — Walks the AST once, building per-block summaries:
   - `defs`: variables assigned in this block
   - `reads`: variables read in this block (upward-exposed uses)
   - `successors`: block indices this block can branch to

   Allocates block IDs for each compound statement (if/for/while/try/with) and
   expression sub-blocks (BoolOp/IfExp/chained Compare).

2. **Fixpoint solver** — Standard backward liveness:
   ```
   liveIn(B)  = reads(B) ∪ (liveOut(B) \ defs(B))
   liveOut(B) = ∪ { liveIn(S) | S ∈ successors(B) }
   ```
   Converges in 2–3 iterations for loops.

Output: `Array DemandVars` — `result[i]` = sorted variable names block `i` needs.

The `globals` set (from Step 1) is subtracted — those names resolve via `lookupVar`, not block params. The prelude names are also added to globals before calling demand analysis.

#### 3d: Emit SSA — `translateBody` / `translateExpr`

DFS walk over the AST, emitting instructions and building blocks:

- **`lookupVar(name)`** — Resolution chain:
  1. `varEnv` local → return existing SSAVal
  2. `varEnv` qualified → emit `qualifiedRef` instruction
  3. `prelude` → emit `qualifiedRef` instruction
  4. Error → emit `unsupported "Unresolved name: ..."` + warning

- **Block transitions** — When branching to a new block:
  - `buildBranchArgs`: for each demanded variable, look up current value in `varEnv`. If not found, emit `undef(name)` and bind it.
  - `buildBlockParams`: create fresh SSAVals as block parameters, rebind in `varEnv`.

- **Expression blocks** — BoolOp, IfExp, chained Compare create sub-blocks with short-circuit semantics. The `fwd` (forwarding context) threads values that must survive through expression blocks as extra block params/args.

- **Scope extras** — `_iter` (for-loop) and `_mgr` (with-statement) are threaded as extra block params alongside demanded variables.

#### 3e: Block ID remap

During translation, blocks get "fresh" IDs in allocation order. But emission order differs (inner blocks emit between pre-allocated outer blocks). A final remap pass rewrites all terminator block references from allocation order to emission order.

### Step 4: Assemble module

Collect all translated `Func` values and warnings into a `Module`.

## Key Data Structures

| Structure | Purpose |
|-----------|---------|
| `FuncInfo` | Pre-translation record: name, params, body, globals |
| `SSAConfig` | Read-only: prelude, moduleName |
| `SSAState` | Mutable: varEnv, blocks, instructions, demand array, scope extras |
| `BodyCtx` | Per-body context: demand array, loop targets, exception var |
| `Binding` | `local SSAVal` or `qualified QualifiedName` |
| `Fwd` | Forwarding context: values threaded through expression blocks |

## Known Gap: Function-Local Variable Collection

`lookupVar` has no way to distinguish "variable that exists but hasn't been assigned on this path" from "completely unknown name." Both hit the error path (step 4 of lookupVar).

The `buildBranchArgs` path handles the first case correctly — demand analysis identifies the variable, and `undef` is emitted when it's not in `varEnv`. But `lookupVar` is called for direct references within a block, before any block transition occurs.

A fix would be to collect all locally-defined variable names for the function body (a cheap single-pass scan of assignment targets) and store them in `SSAConfig` or `SSAState`. Then `lookupVar` could check: if the name is in this set, emit `undef(name)` instead of `unsupported "Unresolved name"`.
