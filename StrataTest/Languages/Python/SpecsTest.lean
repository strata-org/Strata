/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Strata.Languages.Python.Specs
import Strata.Languages.Python.Specs.DDM
import StrataTest.Util.Python

namespace Strata.Python.Specs

/--
info: program PythonSpecs;
function "dict_function"{
  args: [ 
    x : ident(typing.Dict, ident(builtins.int), ident(typing.Any)) [hasDefault: false]
  ]
  kwonly: [ 
  ]
  return: ident(typing.Any)
  overload: false
}
function "list_function"{
  args: [ 
    x : ident(typing.List, ident(builtins.int)) [hasDefault: false]
  ]
  kwonly: [ 
  ]
  return: ident(typing.Any)
  overload: false
}
function "sequence_function"{
  args: [ 
    x : ident(typing.Sequence, ident(builtins.int)) [hasDefault: false]
  ]
  kwonly: [ 
  ]
  return: ident(typing.Any)
  overload: false
}
function "base_function"{
  args: [ 
    x : ident(basetypes.BaseClass) [hasDefault: false]
  ]
  kwonly: [ 
  ]
  return: ident(typing.Any)
  overload: false
}
class "MainClass" {
  function "main_method"{
    args: [ 
      self : class(MainClass) [hasDefault: false]
      x : ident(basetypes.BaseClass) [hasDefault: false]
    ]
    kwonly: [ 
    ]
    return: ident(typing.Any)
    overload: false
  }
}
function "main_function"{
  args: [ 
    x : class(MainClass) [hasDefault: false]
  ]
  kwonly: [ 
  ]
  return: ident(typing.Any)
  overload: false
}
-/
#guard_msgs in
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
    | .ok sigs =>
      let pgm := toDDMProgram sigs
      IO.println <| pgm
    | .error e =>
      throw <| IO.userError e

end Strata.Python.Specs
