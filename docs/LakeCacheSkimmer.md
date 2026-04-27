# Lake Cache Skimmer: Design Document

## Problem

Lean's `lake build` caches elaboration results in `.olean` files. When a module's
elaboration depends on external state (file system, SMT solvers, network, etc.),
the cached result may be stale — but Lake has no way to know this, since it only
tracks source file changes and dependency graphs.

We need a tool that identifies modules whose elaboration *might* depend on
external state and invalidates their cached build artifacts, forcing `lake build`
to re-elaborate them.

## Definition of Purity

A Lean module is **pure** if replaying its build trace produces exactly the same
observable behavior, given that:

1. The module's source content has not changed, and
2. The content of all of its transitive dependencies has not changed.

Equivalently, a module is **impure** if its elaboration:

- **Reads** any state not determined by (1) and (2) above — e.g., file system
  contents outside the dependency graph, environment variables, network state,
  timestamps, random values, or
- **Mutates** any state other than stdout and stderr output (which is captured
  by the build trace).

Note that stdout/stderr output during elaboration (e.g., from `#check`, `#print`,
`logInfo`) is NOT considered a side effect for our purposes, because Lake's build
trace already captures it. The concern is specifically about elaboration behavior
that depends on or affects state *outside* the Lean build system's tracking.

### Implications

Under this definition:

- **`initialize`** is impure: it runs an arbitrary `IO` action that *could* read
  external state, even though many `initialize` blocks only create `IO.Ref`s or
  register extensions (which is deterministic). We cannot statically distinguish
  safe `initialize` from unsafe ones, so all are conservatively impure.

- **`#eval`** is impure: it executes arbitrary code that could perform IO.

- **`#guard_msgs`** is pure *by itself*: it wraps another command and checks its
  output against expected text from the source. The wrapped command is elaborated
  separately and will be checked by the linter independently. If the wrapped
  command is `#eval`, the linter catches `#eval`, not `#guard_msgs`.

- **`#guard`** is impure: it evaluates an expression at elaboration time. The
  expression could in principle depend on external state via `native_decide` or
  similar, though in practice it rarely does. Conservatively impure.

- **`run_cmd` / `run_elab` / `run_meta`** are impure: they execute monadic code
  that has access to `IO`.

- **`declaration`** (`def`, `theorem`, etc.) is pure: elaboration only reads the
  environment (determined by deps) and the source text. Even `native_decide` in
  proofs is deterministic given the same source and deps.

- **Inspection commands** (`#check`, `#print`, etc.) are pure: they only read
  the environment and write to stdout/stderr (captured by build trace).

## Design Goals

1. **Soundness**: If we identify a module as pure, it must be impossible for its
   elaboration to have read external state or mutated state beyond stdout/stderr.
   False negatives (missing an impure module) cause stale cache bugs that are
   extremely hard to diagnose.

2. **Precision**: Minimize false positives. If we flag too many modules as impure,
   every build re-elaborates them unnecessarily, defeating the purpose of caching.

## Background: How Lean Modules Can Perform IO

Lean interleaves parsing and elaboration: each command is parsed using syntax
extensions registered by all previously elaborated commands, then elaborated
before the next command is parsed. This means we cannot parse a file without
elaborating it.

The complete set of ways a module can perform IO during elaboration:

| Command | Mechanism | Leaves `.olean` trace? |
|---------|-----------|----------------------|
| `initialize` / `builtin_initialize` | Runs IO action at module load time | Yes — `[init]` attribute |
| `#eval` / `#eval!` | Executes arbitrary expression | No |
| `#guard_msgs` | Executes wrapped command, checks output | No |
| `#guard` | Evaluates boolean expression | No |
| `run_cmd` / `run_elab` / `run_meta` | Executes monadic code | No |
| Custom `@[command_elab]` | Elaborator may perform IO | No (at use site) |
| `native_decide` / `decide` | Pure computation | N/A (pure) |

The key challenge: most impure commands leave **no trace** in the `.olean` file.
The `.olean` records the *result* of elaboration (declarations, attributes,
environment extensions), not *how* it got there.

## Approaches Considered

### Option A: Instrument the Elaboration Loop

Register a `CommandElab` wrapper that intercepts every command before elaboration,
logs its syntax kind, then delegates to the real elaborator. Write results to a
side-channel file (e.g., `.purity.json`).

**Pros:**
- Perfect accuracy — sees every command exactly as Lean sees it
- No post-build analysis needed

**Cons:**
- Requires modifying the build process
- Every module must import the instrumentation module
- Side-channel files add complexity

### Option B: Re-elaborate Post-Build

After `lake build`, use `Lean.Elab.process` to re-elaborate each source file.
Since `.olean` files exist, `importModules` is fast, but the file itself is
fully re-elaborated. Intercept commands during this re-elaboration.

**Pros:**
- No build modification needed
- Perfect accuracy

**Cons:**
- Re-elaborates every source file — O(n) in codebase size
- Potentially very slow for large codebases
- Duplicates work already done by `lake build`

### Option C: Hybrid `.olean` Inspection + Text Scan

Use `.olean` inspection for `initialize` (precise, via `[init]` attribute).
Use text scanning (grep) for `#eval`, `#guard_msgs`, etc.

**Pros:**
- Fast — no re-elaboration
- `.olean` check is perfectly precise for `initialize`

**Cons:**
- Text scan can false-positive on patterns in comments, strings, or
  custom syntax (e.g., DDM `//` comments containing "initialize")
- Text scan can false-negative if a pattern appears in an unexpected form
- Cannot detect IO from custom command elaborators

### Option D: Persistent Environment Extension (Recommended)

Define a persistent environment extension that records which impure command kinds
were used during elaboration. Register a `CommandElab` hook (via `initialize`)
that writes to this extension whenever an impure command is elaborated. After
`lake build`, load each `.olean` and read the extension.

**Pros:**
- Perfect accuracy — the hook sees every command during real elaboration
- Readable from `.olean` — no re-elaboration, instant classification
- No side-channel files — data lives in the `.olean` itself
- Survives incremental builds — only re-elaborated modules update their data

**Cons:**
- Every module must transitively import the module that registers the hook
- Adds a small overhead to every command elaboration (syntax kind check)
- Requires a base module that all other modules import

## Recommendation

**Option D needs modification.** The linter API cannot write to persistent
environment extensions (`withoutModifyingEnv`). Two viable alternatives:

### Option D' — Custom command elaborator wrappers

Register `@[command_elab]` handlers for each known impure command kind
(`eval`, `initialize`, `guard_msgs`, etc.) that write to the persistent
extension before delegating to the real elaborator. Since these run during
normal elaboration (not as linters), environment modifications persist.

### Option D'' — Linter + IO.Ref side channel

Use the linter API to detect impure commands, but write to a global `IO.Ref`
instead of the environment. After `Elab.process` completes, read the ref.
This works when re-elaborating files post-build but does NOT persist in
`.olean` files — the skimmer must re-elaborate each file.

### Current pragmatic approach

`lake exe skim` runs `lake build` followed by linter-based purity checking.
This is correct and sound but requires developers to use `lake exe skim`
instead of `lake build`.

### Future: Lake plugin (zero-workflow-change)

Lake supports `plugins` on `lean_lib` and `lean_exe` targets — shared libraries
loaded via `lean --plugin` during elaboration. A plugin could register the
purity linter, which would then run automatically during every `lake build`
with no workflow change for developers.

The plugin would:
1. Register the purity linter via `initialize` (same as current `PurityTracker`)
2. Write a `.impure` marker file when impure commands are detected
3. A post-build step (or Lake `post_update` hook) would read markers and
   delete the corresponding `.olean` files

Configuration in `lakefile.toml`:
```toml
[[lean_lib]]
name = "PurityPlugin"
# Lake builds this as a shared library

[[lean_lib]]
name = "Strata"
plugins = ["PurityPlugin"]
```

**Status**: Feasible based on Lake documentation. The `plugins` field is
documented and supported in both TOML and Lean lakefiles. Implementation
requires experimentation with the plugin build/load machinery.

**Key advantage**: Developers just run `lake build` — the plugin runs
automatically, no risk of forgetting to skim.

### Implementation Sketch

```lean
-- PurityHook.lean (imported transitively by all modules)

/-- Persistent extension recording impure command kinds used in this module. -/
initialize purityExt : SimplePersistentEnvExtension SyntaxNodeKind (Array SyntaxNodeKind) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun s n => s.push n
    addImportedFn := fun _ => pure #[]  -- only track current module's commands
  }

/-- Register a linter that records impure commands into the environment. -/
initialize addLinter {
  name := `purityTracker
  run := fun stx => do
    let kind := stx.getKind
    if !isPureCommand kind then
      modifyEnv fun env => purityExt.addEntry env kind
}
```

Post-build, the skimmer loads each `.olean` and checks:

```lean
let env ← importModules #[{ module := modName }] {}
let entries := purityExt.getState env  -- only current module's entries
if entries.isEmpty then PURE else IMPURE
```

### Deployment

The hook module must be imported by every source file. Options:

1. **Add to a root module** that everything already imports (e.g., `Strata.lean`
   or a prelude).
2. **Use a Lake plugin** that automatically injects the import.
3. **Add as a direct import** to every file (most explicit, most verbose).

Option 1 is simplest if such a root module exists.

### Fallback

Until Option D is implemented, Option C (hybrid `.olean` + text scan) provides
a reasonable approximation. It is sound for the known set of impure commands
but may have false positives from text patterns in non-code contexts.

## Open Questions

### 1. Is there a `CommandElab` hook API? — RESOLVED ⚠️

**Partially.** Lean provides the `Linter` API (`Lean.addLinter`) which registers
a callback that runs after every top-level command elaboration. The linter
receives the full command `Syntax` and runs in `CommandElabM`.

**However**, linters run inside `withoutModifyingEnv` (see `runLintersAsync` in
`Lean/Elab/Command.lean:334`), which means **environment modifications are
discarded**. This is by design — linters are intended for reporting diagnostics,
not for modifying the environment.

This means:
- ✅ A linter CAN inspect each command's syntax kind
- ✅ A linter CAN produce messages/warnings
- ❌ A linter CANNOT write to a persistent environment extension
- ❌ A linter CANNOT modify the `.olean` output

**Consequence**: Option D as originally sketched (linter + persistent extension)
does not work. The linter can see the commands but cannot persist its findings
in the `.olean`.

**Alternative mechanisms to investigate**:
- **Custom `@[command_elab]` wrappers**: Register elaborators for known impure
  command kinds that record to the extension before delegating to the real
  elaborator. This runs *during* elaboration (not as a linter), so environment
  modifications persist.
- **`IO.Ref` side channel**: The linter writes to a global `IO.Ref` instead of
  the environment. Post-elaboration, the skimmer reads the ref. This works for
  `Elab.process` but not for `.olean`-based post-build analysis.
- **Lean plugin / Lake hook**: Use Lake's plugin system to inject instrumentation
  into the build pipeline.

2. **What is the right set of impure command kinds?** The table above covers
   known built-in commands. We should audit Lean's source for any others and
   establish a process for updating the list when the Lean toolchain is upgraded.

3. **How do we handle custom `@[command_elab]` elaborators that perform IO?**
   The hook sees the command's syntax kind, but can't know whether the
   elaborator implementation performs IO. One conservative approach: treat any
   command kind not on a known-pure allowlist as potentially impure.

4. **Performance impact of the hook?** The hook runs for every command in every
   module. The check is a hash set lookup on the syntax kind, which should be
   negligible.
