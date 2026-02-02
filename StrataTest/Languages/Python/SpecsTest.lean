/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Strata.Languages.Python.Specs

namespace Strata.Python.Specs

/--
This runs `mise where {runtime}` to identify where a Mise runtime
is installed.  It returns nothing if `mise` is not installed or
the particular runtime is not installed.

N.B. The `mise` command can be replaced with another command if
needed.
-/
def miseWhere (runtime : String) (miseCmd : String := "mise") : IO (Option System.FilePath) := do
    let spawnArgs : IO.Process.SpawnArgs := {
        cmd := miseCmd
        args := #["where", runtime]
        cwd := none
        inheritEnv := true
        stdin := .null
        stdout := .piped
        stderr := .piped
    }
    let child ←
            match ← IO.Process.spawn spawnArgs |>.toBaseIO with
            | .ok c => pure c
            | .error msg => throw <| .userError s!"Could not run mise: {msg}"
    let stdout ← IO.asTask child.stdout.readToEnd Task.Priority.dedicated
    let stderr ←
          match ← child.stderr.readToEnd |>.toBaseIO with
          | .ok c => pure c
          | .error msg => throw <| .userError s!"Could not read stderr from mise: {msg}"
    let exitCode ←
          match ← child.wait |>.toBaseIO with
          | .ok c => pure c
          | .error msg => throw <| .userError s!"Could not wait for process exit code: {msg}"
    let stdout ←
          match stdout.get with
          | .ok c => pure c
          | .error msg => throw <| .userError s!"Could not read stdout: {msg}"
    if exitCode = 255 then
      return none
    -- This is the exit code if the version is not installed
    if exitCode = 1 then
      return none
    if exitCode ≠ 0 then
      let msg := s!"Internal: mise where failed (exitCode = {exitCode})\n"
      let msg := s!"{msg}Standard output:\n"
      let msg := stdout.splitOn.foldl (init := msg) fun msg ln => s!"{msg}  {ln}\n"
      let msg := s!"{msg}Standard error:\n"
      let msg := stderr.splitOn.foldl (init := msg) fun msg ln => s!"{msg}  {ln}\n"
      throw <| .userError msg
    pure <| some stdout.trim

/--
This runs `{command} --version` to check if Python is installed.

It returns `none` if `command` is not found or the version string
if it is.  It throws an error if the command fails for some other
reasaon.
-/
def getPython3Version (command : String) : IO (Option Nat) := do
    let spawnArgs : IO.Process.SpawnArgs := {
        cmd := command
        args := #["--version"]
        cwd := none
        inheritEnv := true
        stdin := .null
        stdout := .piped
        stderr := .null
    }
    let child ←
            match ← IO.Process.spawn spawnArgs |>.toBaseIO with
            | .ok c => pure c
            | .error msg => throw <| .userError s!"Could not run mise: {msg}"
    let stdout ← IO.asTask child.stdout.readToEnd Task.Priority.dedicated
    let exitCode ←
          match ← child.wait |>.toBaseIO with
          | .ok c => pure c
          | .error msg => throw <| .userError s!"Could not wait for python process exit code: {msg}"
    let stdout ←
          match stdout.get with
          | .ok c => pure c
          | .error msg => throw <| .userError s!"Could not read stdout: {msg}"
    if exitCode = 255 then
      return none
    if exitCode ≠ 0 then
      let msg := s!"Internal: mise where failed (exitCode = {exitCode})\n"
      let msg := s!"{msg}Standard output:\n"
      let msg := stdout.splitOn.foldl (init := msg) fun msg ln => s!"{msg}  {ln}\n"
      throw <| .userError msg
    let msg := stdout.trim
    let pref := "Python 3."
    let some minorReleaseStr := msg.dropPrefix? pref
      | throw <| .userError s!"Unexpected Python 3 version {msg}"

    let minorStr := minorReleaseStr.takeWhile fun c => c.isDigit
    let some minor := minorStr.toNat?
      | throw <| .userError s!"Unexpected Python 3 version {msg}"
    return some minor


/--
info: none
-/
#guard_msgs in
#eval miseWhere "Python@1.0"

/--
info: none
-/
#guard_msgs in
#eval miseWhere "Python@3.12" (miseCmd := "nonexisting-mise")

/--
This attempts to find Python with at least the given minimum version.

It check if the PYTHON environment variable is set, if so it verifies
it satisfies the minimum version.

Next it iterates through versions maxVersion to minVersion and performs
two checks:

1. It attempts to run `mise` to see if the version is installed.
2. Next it looks in the path for python3.{minVersion}.
-/
def findPython3 (minVersion : Nat := 12) (maxVersion : Nat := 14) : IO System.FilePath := do
  assert! minVersion ≤ maxVersion
  if let some path  ← IO.getEnv "PYTHON" then
    let some foundMinor ← getPython3Version path
      | throw <| .userError
          "PYTHON environment variable not set to python executable."
    if foundMinor ≥ foundMinor then
      throw <| .userError
        s!"PYTHON variable is Python 3.{foundMinor} when at least 3.{minVersion} required."
    return path

  -- Search versions in reverse order
  for ⟨i, _⟩ in Fin.range (maxVersion - minVersion + 1) do
    let ver := maxVersion - i

    if let some path ← miseWhere s!"Python@3.{ver}" then
      return path / "bin" / "python"

    let defaultCmd := s!"python3.{ver}"
    if let some _foundMinor ← getPython3Version defaultCmd then
      -- We don't both checking minor version since we already used version in path.
      return defaultCmd

  throw <| IO.userError s!"Python 3.{minVersion} or later not found."


def runTest : IO Unit := do
  let pythonCmd ← findPython3 12
  let dialectFile : System.FilePath := "Tools/Python/dialects/Python.dialect.st.ion"
  let pythonFile : System.FilePath := "StrataTest/Languages/Python/Specs/main.py"
  IO.FS.withTempDir fun strataDir => do
    let r ←
      translateFile
        (pythonCmd := toString pythonCmd)
        (dialectFile := dialectFile)
        (strataDir := strataDir)
        (pythonFile := pythonFile)
        |>.toBaseIO
    match r with
    | .ok specs =>
      pure ()
    | .error e =>
      throw <| IO.userError e

#eval runTest

end Strata.Python.Specs
