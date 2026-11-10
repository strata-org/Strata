/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Init
public meta import Lean.Elab.Command
public meta import Lean.Elab.Eval

open Lean Elab Command

/-! # Declarative tests

Small tests in Lean are naturally and easily expressed using commands such as `#guard`
and `#eval`. These commands must be executed sequentially during module elaboration.
When tests are numerous or heavyweight, there is substantial benefit to executing them
in parallel to take advantage of the CPUs on build systems. This module provides
similar macros for declaring tests in a form that can be executed in parallel.

Declare a set of *tests*, then choose a strategy for executing them.
Each test's body is bound to a `meta def` when it is declared, and a child module
runs it later by NAME. Nothing copies the body's source: the `def` is the captured
value, and the child only references it. The `def`s are `meta` because a test body
reaches the suite's `meta import`ed helpers (for example `withPython`), which a
non-`meta` `def` may not, and `#eval`/`#guard`/`run_cmd` all elaborate at meta time.

## Declaring tests

- `#test "Name" => <body>` binds `meta def Name := <body>` and runs it as
  `#eval Name`, so the body runs as an `IO` action (for example a
  `withPython fun ... => do ...` test); an uncaught exception fails it.
- `#test_guard "Name" => <prop>` binds `meta def Name := <prop>` and runs it as
  `#guard Name`. A false assertion fails, and the failure location identifies which
  one, so no message string is needed.
- `#test_cmd "Name" => <body>` binds `meta def Name : CommandElabM Unit := <body>`
  and runs it as `run_cmd Name`, so the body elaborates in the command monad:
  `logError`, `throwError`, and term elaborators such as `getIonSerializer%` all work.
- `#test_msgs "Name" => <body>` binds `meta def Name := <body>` and runs it as a
  message-golden test: the attached `/-- … -/` comment is the expected output (read
  as `#guard_msgs` reads it), and the child runs `#guard_msgs in #eval Name`.
- `#test_for_each_file "<dir>" "<pre>" "<suf>" <fn>` records one `#eval` per file in
  `dir` whose name starts with `pre` and ends with `suf`, named by its stem and
  running `<fn> "<stem>"`. The directory is read when the command is declared, so the
  set of tests follows the directory contents.
- `#test_for_each <fn> <names>` records one `#eval` per name in `names` (a
  `List String` evaluated now), each running `<fn> "<name>"`. Lets a table of tests
  (for example a `List Case`) drive the children by name.

For `#test`, `#test_guard`, `#test_cmd` and `#test_msgs` the name is optional: omit it
(`#test => <body>`) and the test is named `Test<n>`, where `n` counts the unnamed
tests already declared in the file (and never resets, so a second batch after a run
command does not reuse `Test0`).

The `for_each` forms do not bind a `def`: their body is already just a call
`<fn> "<name>"`, so the child runs that call directly.

## Running them

Two strategies execute the recorded tests; both clear the accumulator afterwards.

- `#run_tests` runs every recorded test sequentially in the current build process.
  A failing test logs its error but does not abort the rest, so one build surfaces
  all the failures. No files are written.
- `#run_tests_as_modules "<dir>"` checks the committed child modules under `<dir>`
  against what the recorded tests would emit. When they match, the build is clean and
  the children build as separate `lean` processes, so they run concurrently. On any
  drift — a missing, stale, or orphaned child — it regenerates the directory and
  fails the build; build once locally and commit the regenerated files to turn it
  green. So the loop is: if this fails on the build server, run the build once
  locally and check in the changed files.

A linter errors if a file records tests but runs neither `#run_tests` nor
`#run_tests_as_modules`, so the entries cannot be silently dropped.

Each generated child begins with a header collected from THIS file: a `public meta
import` of the suite module itself (which carries the test `def`s, helpers, and any
term elaborators) and the suite's `open`s. The `def`s a suite declares are reachable
even when kept private because the child also `meta import all`s the suite.
`run_cmd`/`#guard`/`#eval` elaborate at meta time, so the imports are `meta`.

## Incremental builds and `#test_for_each_file`

`#test_for_each_file` reads its directory when it elaborates, and Lake does not track
that directory as a build input. A clean build always re-elaborates the generator, so
`#run_tests_as_modules` regenerates the children and its drift check keeps the
committed set in sync — the build fleet is always correct. On a warm incremental LOCAL
build, adding or removing a file may not re-run the generator until it is recompiled
for some other reason. We deliberately do not declare the directory as a Lake
`[[input_dir]]`: the generated children are discovered and run by the custom test
driver, not through Lake's test graph, so such an input would be a misleading
dependency rather than something the runner actually reads.
-/

namespace Strata.IOTests.Tests

/-- One recorded test: its unique name and the command text the child runs.
    For `#test`/`#test_guard`/`#test_cmd`/`#test_msgs` the command references a
    `def` of that name; for the `for_each` forms it is a direct call. -/
meta structure Entry where
  name : String
  command : String
  deriving Inhabited

/-- The recorded tests, flushed by `#run_tests` or `#run_tests_as_modules`. -/
meta structure State where
  entries : Array Entry := #[]
  /-- A per-file counter for default `#test` names. A run command clears `entries` but
      NOT this, so a second batch of unnamed tests after `#run_tests` keeps getting fresh
      `Test<n>` names instead of reusing `Test0`. -/
  defaultCount : Nat := 0
  deriving Inhabited

/-- Per-file accumulator: the `#test*` commands push, a run command (`#run_tests`
    or `#run_tests_as_modules`) flushes and clears. -/
meta initialize testsExt : EnvExtension State ← registerEnvExtension (pure {})

/-- Push one test: its name and the command the child runs to execute it. -/
meta def record (name command : String) : CommandElabM Unit :=
  modifyEnv fun env => testsExt.modifyState env fun s =>
    { s with entries := s.entries.push { name, command } }

/-- The identifier a test name becomes. An arbitrary string is a legal single
    component, so a natural-language name (`#test "map contracts"`) works too. -/
meta def testIdent (name : String) : Ident := mkIdent (Name.mkSimple name)

/-- The default `#test` name: `Test<n>`, where `n` counts the unnamed tests already
    recorded in this file. Backed by `defaultCount`, which a run command does not
    reset, so names stay unique across batches separated by `#run_tests`. -/
meta def nextDefaultName : CommandElabM String := do
  let n := (testsExt.getState (← getEnv)).defaultCount
  modifyEnv fun env =>
    testsExt.modifyState env fun s => { s with defaultCount := s.defaultCount + 1 }
  return s!"Test{n}"

/-- The child's reference to a test `def` by name, qualified by the namespace the test
    is declared in so it resolves at the child's root scope no matter which namespaces
    the child opens. At the root namespace this is just `«name»`. -/
meta def childRef (name : String) : CommandElabM String := do
  let ns := (← getScope).currNamespace
  return if ns.isAnonymous then s!"«{name}»" else s!"{ns}.«{name}»"

/-- Record a test whose body runs as `#eval Name`, so it runs as an `IO` action at
    elaboration (for example a `withPython` test). The name is optional. -/
elab "#test" name:(ppSpace str)? " => " body:term : command => do
  let nm ← match name with | some s => pure s.getString | none => nextDefaultName
  elabCommand (← `(command| meta def $(testIdent nm):ident := $body))
  record nm ("#eval " ++ (← childRef nm))

/-- Record a test whose child runs `#guard Name`. The name is optional. -/
elab "#test_guard" name:(ppSpace str)? " => " prop:term : command => do
  let nm ← match name with | some s => pure s.getString | none => nextDefaultName
  elabCommand (← `(command| meta def $(testIdent nm):ident := $prop))
  record nm ("#guard " ++ (← childRef nm))

/-- Record a test whose child runs `run_cmd Name`; the body elaborates in the
    command monad. The name is optional. -/
elab "#test_cmd" name:(ppSpace str)? " => " body:term : command => do
  let nm ← match name with | some s => pure s.getString | none => nextDefaultName
  elabCommand (← `(command|
    meta def $(testIdent nm):ident : Lean.Elab.Command.CommandElabM Unit := $body))
  record nm ("run_cmd " ++ (← childRef nm))

/-- Record a message-golden test. The attached `/-- … -/` comment is the expected
    output, exactly as `#guard_msgs` reads it; the child reproduces that comment
    followed by `#guard_msgs in #eval Name`, so the golden check runs in the child
    unchanged. The expected output is read from the comment, never restated. The name
    is optional. -/
elab doc:(docComment)? "#test_msgs" name:(ppSpace str)? " => " body:term : command => do
  let nm ← match name with | some s => pure s.getString | none => nextDefaultName
  elabCommand (← `(command| meta def $(testIdent nm):ident := $body))
  let docSrc := match doc with
    | some d =>
      match d.raw.getSubstring? (withLeading := false) (withTrailing := false) with
      | some ss => ss.toString
      | none => d.raw.reprint.getD ""
    | none => ""
  record nm s!"{docSrc}\n#guard_msgs in\n#eval {← childRef nm}"

/-- Dynamically record one `#eval` test per file in `dir` whose name
    starts with `pre` and ends with `suf`. The child for a file is named by its
    stem (the name with `suf` removed) and runs `<fn> "<stem>"`. The directory is
    read at elaboration, so the set of children follows the directory contents. -/
elab "#test_for_each_file " dir:str pre:str suf:str fn:ident : command => do
  -- Resolve `fn` to its fully-qualified name now, against the namespace and opens in
  -- effect here, so the child's `#eval` names it absolutely. Spelling it as written
  -- would rely on the child opening the same namespace, which it need not (the child
  -- opens what `#run_tests_as_modules` sees, not what the test was declared under).
  -- `privateToUserName` turns the internal `_private.…` name of a private `fn` back
  -- into its writable logical name; `meta import all` makes that name resolve in the
  -- child. For a public `fn` it is already the logical name.
  let fnName := Lean.privateToUserName (← liftCoreM <| realizeGlobalConstNoOverload fn)
  let d : System.FilePath := dir.getString
  unless ← d.pathExists do
    throwError m!"#test_for_each_file: directory not found: {dir.getString}"
  for de in (← d.readDir) do
    let fname := de.fileName
    if fname.startsWith pre.getString && fname.endsWith suf.getString then
      let stem := (fname.dropEnd suf.getString.length).toString
      record stem s!"#eval {fnName} {repr stem}"

/-- Record one `#eval` test per name in `names` (a `List String` evaluated now),
    each running `<fn> "<name>"`. Lets a table of tests (for example a `List Case`)
    drive the child modules by name, without copying each test's source into them:
    the child looks its test up by name through `<fn>` at its own elaboration. -/
elab "#test_for_each " fn:ident names:term : command => do
  -- Resolve `fn` absolutely now (see `#test_for_each_file`), so the child does not
  -- depend on opening the namespace the test was declared under.
  let fnName := Lean.privateToUserName (← liftCoreM <| realizeGlobalConstNoOverload fn)
  let xs ← liftTermElabM <| unsafe Term.evalTerm (List String)
    (.app (.const ``List [.zero]) (.const ``String [])) names
  for name in xs do
    record name s!"#eval {fnName} {repr name}"

/-- The header each child begins with: a do-not-edit banner, a `public meta
    import` of the suite module, a `meta import all` of it (so a child reaches the
    suite's private test `def`s), and the suite's `open`s. -/
meta def collectHeader (selfMod : Name) : CommandElabM String := do
  let opens := (← getScope).openDecls.reverse.filterMap fun
    | .simple ns _ => some s!"open {ns}"
    | _ => none
  let copyright :=
    "/-\n  Copyright Strata Contributors\n\n  SPDX-License-Identifier: Apache-2.0 OR MIT\n-/"
  let banner :=
    s!"-- This file is auto-generated from {selfMod} by #run_tests_as_modules.\n"
    ++ "-- Do not edit directly; edit the source test. A stale child is regenerated by the\n"
    ++ "-- build, which then fails until the regenerated file is committed."
  -- Import the suite two ways: `public meta import` carries its re-exported public
  -- deps (e.g. a `withPython` the suite re-exports), and `meta import all` exposes
  -- its private test `def`s (which the suite need not export), so a child can
  -- reference either without the suite having to publicize anything.
  let lines := s!"public meta import {selfMod}" :: s!"meta import all {selfMod}" :: opens
  return s!"{copyright}\nmodule\n\n{banner}\n\n" ++ String.intercalate "\n" lines

/-- The child source for one test: the header followed by the command that runs it. -/
meta def childSource (header : String) (e : Entry) : String :=
  s!"{header}\n\n{e.command}\n"

/-- Runs the recorded tests (see the module overview), then clears the accumulator. -/
elab "#run_tests" : command => do
  let st := testsExt.getState (← getEnv)
  modifyEnv fun env => testsExt.modifyState env fun s => { s with entries := #[] }
  let mut failures : Nat := 0
  for e in st.entries do
    match Lean.Parser.runParserCategory (← getEnv) `command e.command with
    | .ok stx =>
      -- `elabCommand` records elaboration errors (a false `#guard`, any `logError`
      -- from a `run_cmd`/`#eval` body) in the message log instead of raising, so run
      -- each test against a cleared log and count the ones that add an error rather
      -- than relying on an exception. The produced messages are kept, so each failure
      -- still surfaces in the build output.
      let prev := (← get).messages
      modify fun s => { s with messages := .empty }
      try
        elabCommand stx
      catch ex =>
        logError m!"{e.name}: {ex.toMessageData}"
      let produced := (← get).messages
      if produced.hasErrors then
        failures := failures + 1
      modify fun s => { s with messages := prev.append produced }
    | .error err =>
      failures := failures + 1
      logError m!"{e.name}: parse error: {err}"
  if failures == 0 then
    logInfo m!"ran {st.entries.size} test(s)"
  else
    logError m!"{failures} of {st.entries.size} test(s) failed"

/-- Check (and, on drift, regenerate) one child module per recorded test under
    `dir`, reconciling against the directory, then clear the accumulator. -/
elab "#run_tests_as_modules " dir:str : command => do
  let st := testsExt.getState (← getEnv)
  -- Clear the accumulator now and work from the captured `st`; this also stops the
  -- unflushed-entries linter from double-reporting when a check below throws. Clear
  -- only `entries`, not `defaultCount`, so later unnamed tests keep getting fresh
  -- `Test<n>` names instead of colliding with ones already generated.
  modifyEnv fun env => testsExt.modifyState env fun s => { s with entries := #[] }
  -- Each name becomes a child filename, so a collision would silently overwrite
  -- (regen) or doubly-satisfy (check) one file. Reject duplicates up front.
  let mut seen : Array String := #[]
  let mut dups : Array String := #[]
  for n in st.entries.map (·.name) do
    if seen.contains n then
      unless dups.contains n do dups := dups.push n
    else seen := seen.push n
  unless dups.isEmpty do
    throwError m!"duplicate test name(s): {String.intercalate ", " dups.toList}; \
      each name becomes a child filename and must be unique"
  let header ← collectHeader (← getMainModule)
  let d : System.FilePath := dir.getString
  let expected := st.entries.map (·.name ++ ".lean")
  let orphans : Array String ←
    if ← d.pathExists then do
      let des ← d.readDir
      pure <| des.filterMap fun de =>
        let fn := de.fileName
        if fn.endsWith ".lean" && !expected.contains fn then some fn else none
    else pure #[]
  -- Always check the committed children against what the recorded tests emit now.
  let mut bad : Array String := #[]
  for e in st.entries do
    let p := d / (e.name ++ ".lean")
    if !(← p.pathExists) then
      bad := bad.push s!"missing {e.name}.lean"
    else if (← IO.FS.readFile p) != childSource header e then
      bad := bad.push s!"stale {e.name}.lean"
  for fn in orphans do
    bad := bad.push s!"unexpected {fn}"
  if bad.isEmpty then
    logInfo m!"{st.entries.size} child module(s) up to date in {dir.getString}/"
  else
    -- Out of date: (re)write the children so one LOCAL build fixes the tree, then
    -- fail so the committed copy stays the source of truth. The write is best-effort:
    -- on a read-only build host it is a no-op and the failure still blocks. Commit the
    -- regenerated files to turn the next build green.
    try
      IO.FS.createDirAll d
      for e in st.entries do
        IO.FS.writeFile (d / (e.name ++ ".lean")) (childSource header e)
      for fn in orphans do
        IO.FS.removeFile (d / fn)
    catch _ => pure ()
    throwError m!"child modules were out of date and have been regenerated in \
      {dir.getString}/ ({String.intercalate ", " bad.toList}); build once locally \
      and commit the result"

/-- Error at end of file if tests were recorded but never flushed by a run command,
    so the entries cannot be silently dropped. -/
meta def unflushedTestsLinter : Linter where
  run := fun stx => do
    unless stx.isOfKind ``Lean.Parser.Command.eoi do return
    let st := testsExt.getState (← getEnv)
    unless st.entries.isEmpty do
      logError m!"{st.entries.size} test(s) were recorded but neither #run_tests nor \
        #run_tests_as_modules was run; add #run_tests to run them here, or \
        #run_tests_as_modules \"<dir>\" to generate or check their child modules"

meta initialize addLinter unflushedTestsLinter

end Strata.IOTests.Tests
