/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

module
import all Strata.DDM.Util.Fin

/-
This module provides `findPython3`, a utility that locates
a Python 3 installation with a specific version using multiple methods
including an environment variable, `mise` and the system `'PATH'`.

It also provides a few functions for checking Python versions and
running `mise`.
-/

public section
namespace Strata.Python

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
  pure <| some stdout.trimAscii.toString

/--
This checks to see if a module is found.
-/
def pythonCheckModule (pythonCmd : System.FilePath) (moduleName : String) : IO Bool := do
  let spawnArgs : IO.Process.SpawnArgs := {
      cmd := toString pythonCmd
      args := #["-c", s!"import {moduleName}"]
      cwd := none
      inheritEnv := true
      stdin := .null
      stdout := .null
      stderr := .null
  }
  let child ← IO.Process.spawn spawnArgs
  let exitCode ←
        match ← child.wait |>.toBaseIO with
        | .ok c => pure c
        | .error msg => throw <| .userError s!"Could not wait for process exit code: {msg}"
  match exitCode with
  | 0 =>
    return true
  | 1 =>
    return false
  | 255 =>
    throw <| .userError "{pythonCmd} not found."
  | _ =>
    throw <| .userError
      s!"{pythonCmd} has unexpected exit code {exitCode}"

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
Utility to get Python 3 minor version.

For example, `getPython3Version 'python3.12'` would be expected
to return `some 12` if `python3.12 --version` returns the
expected output `'Python 3.12.12'`.

It returns `none` if `command` is not found, and throws an error
if the command fails for some other reason.
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
    let msg := stdout.trimAscii.toString
    let pref := "Python 3."
    let some minorReleaseStr := msg.dropPrefix? pref
      | throw <| .userError s!"Unexpected Python 3 version {msg}"
    let minorStr := minorReleaseStr.takeWhile Char.isDigit
    let some minor := minorStr.toNat?
      | throw <| .userError s!"Unexpected Python 3 version {msg}"
    return some minor

/--
This attempts to find Python with at least the given minimum version.

It checks if the PYTHON environment variable is set, if so it verifies
it satisfies the minimum version.

Next it iterates through versions maxVersion to minVersion and performs
two checks:

1. It attempts to run `mise` to see if the version is installed.
2. Next it looks in the path for python3.{minVersion}.
-/
def findPython3 (minVersion : Nat) (maxVersion : Nat) : IO System.FilePath := do
  assert! minVersion ≤ maxVersion
  if let some path  ← IO.getEnv "PYTHON" then
    let some foundMinor ← getPython3Version path
      | throw <| .userError
          "PYTHON environment variable not set to python executable."
    if foundMinor < minVersion then
      throw <| .userError
        s!"PYTHON variable is Python 3.{foundMinor} when at least 3.{minVersion} required."
    if foundMinor > maxVersion then
      throw <| .userError
        s!"PYTHON variable is Python 3.{foundMinor} when at most 3.{maxVersion} required."
    return path

  -- Search versions in reverse order
  for ⟨i, _⟩ in Fin.range (maxVersion - minVersion + 1) do
    let ver := maxVersion - i

    if let some path ← miseWhere s!"Python@3.{ver}" then
      return path / "bin" / "python"

    let defaultCmd := s!"python3.{ver}"
    if let some _foundMinor ← getPython3Version defaultCmd then
      -- We don't bother checking minor version since we already
      -- used version in path.
      return defaultCmd

  throw <| IO.userError s!"Python 3.{minVersion} or later not found."

end Strata.Python
end
