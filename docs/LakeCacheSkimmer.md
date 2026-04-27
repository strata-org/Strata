# Lake Cache Skimmer: Design Document

## Problem

Lean's `lake build` caches elaboration results in `.olean` files. When a module's
elaboration depends on external state (file system, SMT solvers, network, etc.),
the cached result may be stale — but Lake has no way to know this, since it only
tracks source file changes and dependency graphs.

We need a mechanism that identifies modules whose elaboration *might* depend on
external state and forces `lake build` to re-elaborate them.

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

### Implications

Under this definition:

- **`initialize`** is impure: it runs an arbitrary `IO` action that *could* read
  external state. We cannot statically distinguish safe from unsafe `initialize`
  blocks, so all are conservatively impure.
- **`#eval` / `#eval!`** is impure: executes arbitrary code that could perform IO.
- **`#guard`** is impure: evaluates an expression at elaboration time.
- **`run_cmd` / `run_elab` / `run_meta`** are impure: execute monadic code with
  IO access.
- **`#guard_msgs`** is pure *by itself*: it wraps another command and checks its
  output against source text. The wrapped command is checked independently by the
  linter. (Note: Lean skips linters for `#guard_msgs`, but runs them on the inner
  command.)
- **`declaration`** (`def`, `theorem`, etc.) is pure.
- **Inspection commands** (`#check`, `#print`, etc.) are pure.

## Design Goals

1. **Soundness**: If we identify a module as pure, it must be impossible for its
   elaboration to have read external state or mutated state beyond stdout/stderr.

2. **Precision**: Minimize false positives (pure modules incorrectly flagged as
   impure).

3. **Zero workflow change**: Developers should just run `lake build` with no
   extra steps.

## Solution: Lake Compiler Plugin

The solution is a **Lean compiler plugin** (`PurityPlugin.lean`) that runs
automatically during every `lake build`. No separate tools or scripts needed.

### How It Works

The plugin uses an **inverted marker** design — safe by default:

1. **At plugin load** (start of each `lake build`): For every `.lean` source file
   that does NOT have a `.pure` marker in `.lake/build/lib/lean/`, delete its
   `.trace` file. This causes Lake to rebuild that module.

2. **During elaboration**: A linter (registered via `Lean.addLinter`) runs after
   each command. It checks the command's syntax kind against a pure allowlist.
   - If all commands are pure: a `.pure` marker file is written.
   - If any impure command is detected: the `.pure` marker is deleted.

3. **Result**: After the build, pure modules have `.pure` markers and will be
   cached on the next build. Impure modules have no markers and will be rebuilt.

### Safety Properties

- **No marker = rebuild**: If the plugin fails to run, a new file is added, or
  anything unexpected happens, there's no `.pure` marker, so the module gets
  rebuilt. This is the safe default.
- **`lake clean` triggers full rebuild**: Cleaning removes all markers, so the
  next build re-elaborates everything and re-establishes markers.
- **First build after adding the plugin**: All modules are rebuilt (no markers
  exist yet). This is expected and correct.

### Configuration

In `lakefile.toml`:

```toml
[[lean_lib]]
name = "PurityPlugin"
defaultFacets = ["shared"]

[[lean_lib]]
name = "Strata"
plugins = ["PurityPlugin:shared"]
```

The plugin is built as a shared library and loaded via `lean --plugin` during
elaboration of every module in the `Strata` library.

### Pure Command Allowlist

The plugin maintains an allowlist of command syntax kinds known to be pure.
Any command NOT on the allowlist is conservatively treated as impure.

The allowlist was audited against Lean v4.29.1 source code. See the inline
documentation in `PurityPlugin.lean` for the full audit.

The allowlist approach is **sound**: unknown commands default to impure (false
positives, not false negatives). The allowlist should be re-audited when
upgrading the Lean toolchain.

### Linter API

The plugin uses `Lean.addLinter` to register a callback that runs after every
top-level command elaboration. Key properties:

- Linters run inside `withoutModifyingEnv`, so they cannot modify the `.olean`.
  Instead, the plugin writes `.pure` marker files via IO (which IS available
  in `CommandElabM`).
- Linters are skipped for `#guard_msgs`, but run on the inner command. This
  means `#guard_msgs in #eval foo` correctly detects `#eval` as impure.
- Each module is elaborated in its own Lean process, so the linter state is
  fresh for each file.

### Marker File Layout

Markers are stored alongside `.olean` files in `.lake/build/lib/lean/`:

```
.lake/build/lib/lean/Strata/DDM/Elab/Env.olean   # build artifact
.lake/build/lib/lean/Strata/DDM/Elab/Env.trace    # Lake's build trace
.lake/build/lib/lean/Strata/DDM/Elab/Env.pure     # purity marker (if pure)
```

This means:
- Markers are automatically cleaned by `lake clean`
- Markers are in `.lake/` which is gitignored
- No source tree pollution

## Open Questions

1. **Toolchain upgrades**: The pure command allowlist is pinned to a specific
   Lean version. New impure commands in future Lean versions would not be on
   the allowlist and would correctly default to impure (safe). However, if a
   previously-pure command becomes impure, the allowlist would need updating.

2. **Custom `@[command_elab]` elaborators**: The plugin sees the command's
   syntax kind but can't know whether a custom elaborator performs IO. Unknown
   command kinds are treated as impure (conservative).

3. **Plugin loading for other libraries**: Currently the plugin is configured
   only for the `Strata` library. To cover `StrataTest` and other libraries,
   they would also need `plugins = ["PurityPlugin:shared"]` in their config.
