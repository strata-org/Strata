/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

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
    let content ← stdin.readToEnd
    pure content.toUTF8
  else
    IO.FS.readBinFile path

end Strata.Util
