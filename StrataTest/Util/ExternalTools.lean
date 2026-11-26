/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

namespace Strata.TestUtil

/--
Whether tests that need an external tool (a Go toolchain, `javac`, a runtime
jar) must run it rather than skip: inside a Brazil build, or under CI (`CI` set,
as GitHub Actions and most CI systems do).

Test files under `StrataTestExtra/` run as `lean <file>` children of the test
driver, which prints only `PASS: <module>` for a zero exit. A skip warning is
therefore invisible to everyone but a developer running the file by hand, and in
a build that is meant to provide the tool it would turn the suite into a silent
pass. Local development without the tool keeps skipping.

The CBMC tests use their own switch, `CBMC_TESTS_REQUIRED`, which the Brazil
build sets and CI does not, so CI may run without CBMC. Use this predicate for
any new external-tool check rather than adding another switch.
-/
public def externalToolChecksRequired : IO Bool := do
  if (← IO.getEnv "BRAZIL_BUILD_HOME").isSome then return true
  match ← IO.getEnv "CI" with
  | some v => return !v.isEmpty && v != "0" && v.toLower != "false"
  | none => return false

/-- Why the external tool `cmd` is unusable, judged by running `cmd args` (a
cheap probe such as `--version`), or `none` when the probe exits successfully.

The reason quotes the probe's stderr only: when `cmd` cannot be executed, the
forked child can flush this process's buffered stdout into the captured stdout,
which would echo earlier messages into the reason. -/
public def toolUnavailable? (cmd : String) (args : Array String) :
    IO (Option String) := do
  try
    let r ← IO.Process.output { cmd, args }
    if r.exitCode == 0 then return none
    return some s!"`{cmd} {" ".intercalate args.toList}` exited {r.exitCode}: \
      {r.stderr.trimAscii}"
  catch e =>
    return some s!"{cmd} could not be run: {e}"

/-- Fail when `what` is unusable for `reason` in a build that must provide it
(see `externalToolChecksRequired`). Otherwise return, so the caller skips its
check with a warning. -/
public def requireTool (what reason : String) : IO Unit := do
  if ← externalToolChecksRequired then
    throw <| IO.userError s!"{what} is required in Brazil and CI builds, but {reason}"

end Strata.TestUtil
