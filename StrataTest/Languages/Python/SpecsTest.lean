/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Strata.Languages.Python.Specs
import StrataTest.Util.Python

namespace Strata.Python.Specs

#eval do
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

end Strata.Python.Specs
