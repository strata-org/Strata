# Lake Cache Skimmer: Design Document

## Problem

Lean's `lake build` caches elaboration results in `.olean` files. When a module's
elaboration depends on external state (file system, SMT solvers, network, etc.),
the cached result may be stale — but Lake has no way to know this, since it only
tracks source file changes and dependency graphs.

We need a tool that identifies modules whose elaboration *might* perform IO and
invalidates their cached build artifacts, forcing `lake build` to re-elaborate
them.

## Design Goals

1. **Soundness**: If we identify a module as pure, it must be impossible for its
   elaboration to have performed any IO. False negatives (missing an impure module)
   cause stale cache bugs that are extremely hard to diagnose.

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

**Option D** is the recommended approach. It achieves both design goals:

1. **Soundness**: The hook runs inside the real elaboration loop, so it sees
   exactly what Lean sees. If a command performs IO, the hook records it.

2. **Precision**: Only modules that actually elaborate impure commands are
   flagged. No false positives from text patterns in comments or custom syntax.

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

### 1. Is there a `CommandElab` hook API? — RESOLVED ✅

**Yes.** Lean provides the `Linter` API in `Lean.Elab.Command`:

```lean
structure Linter where
  run : Syntax → CommandElabM Unit
  name : Name
```

`Lean.addLinter` registers a linter that runs **after every top-level command
elaboration** (called from `elabCommandTopLevel` → `runLintersAsync`). The
linter receives the full command `Syntax` and runs in `CommandElabM`, which
means it can:

- Inspect `stx.getKind` to identify the command type
- Call `modifyEnv` to write to a persistent environment extension
- Access the full elaboration state

This is the exact mechanism needed for Option D. The linter sees every command
as Lean sees it, after macro expansion, with the correct syntax kind. It runs
during normal `lake build` with no special instrumentation needed — just
`import` the module that registers the linter.

**Registration** is via `initialize`:

```lean
initialize addLinter {
  name := `purityTracker
  run := fun stx => do
    let kind := stx.getKind
    if !isPureCommand kind then
      modifyEnv fun env => purityExt.addEntry env kind
}
```

This resolves the feasibility question for Options A and D. Option D is
confirmed as the recommended approach.

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
