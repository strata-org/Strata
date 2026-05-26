/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public section
namespace Strata.Util

/-- Read from stdin if path is "-", otherwise read from file -/
def readInputSource (path : String) : IO String := do
  if path == "-" then
    let stdin ← IO.getStdin
    stdin.readToEnd
  else
    IO.FS.readFile path

/-- Read binary from stdin if path is "-", otherwise read from file -/
def readBinInputSource (path : String) : IO ByteArray := do
  if path == "-" then
    let stdin ← IO.getStdin
    stdin.readBinToEnd
  else
    IO.FS.readBinFile path

/-- Get display name for error messages: "<stdin>" if reading from stdin, otherwise the path -/
def displayName (path : String) : String :=
  if path == "-" then "<stdin>" else path

end Strata.Util
end
