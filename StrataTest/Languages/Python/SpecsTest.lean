/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Strata.Languages.Python.Specs
import Strata.Languages.Python.Specs.DDM
import StrataTest.Util.Python

namespace Strata.Python.Specs

def expectedPySpec :=
#strata
program PythonSpecs;
extern "BaseClass" from "basetypes.BaseClass";
function "dict_function" {
  args: [
    x : ident("typing.Dict", ident("builtins.int"), ident("typing.Any")) [hasDefault: false]
  ]
  kwonly: [
  ]
  return: ident("typing.Any")
  overload: false
}
function "list_function" {
  args: [
    x : ident("typing.List", ident("builtins.int")) [hasDefault: false]
  ]
  kwonly: [
  ]
  return: ident("typing.Any")
  overload: false
}
function "sequence_function" {
  args: [
    x : ident("typing.Sequence", ident("builtins.int")) [hasDefault: false]
  ]
  kwonly: [
  ]
  return: ident("typing.Any")
  overload: false
}
function "base_function"{
  args: [
    x : ident("basetypes.BaseClass") [hasDefault: false]
  ]
  kwonly: [
  ]
  return: ident("typing.Any")
  overload: false
}
class "MainClass" {
  function "main_method"{
    args: [
      self : class(MainClass) [hasDefault: false]
      x : ident("basetypes.BaseClass") [hasDefault: false]
    ]
    kwonly: [
    ]
    return: ident("typing.Any")
    overload: false
  }
}
function "main_function"{
  args: [
    x : class(MainClass) [hasDefault: false]
  ]
  kwonly: [
  ]
  return: ident("typing.Any")
  overload: false
}
#end

-- We use an environment variable to allow the build process
-- to require the Python test is run.
def pythonTestRequired : IO Bool :=
  return (← IO.getEnv "PYTHON_TEST").isSome

def testCase : IO Unit := do
  let pythonCmd ←
    match ← findPython3 (minVersion := 11) (maxVersion := 14) |>.toBaseIO with
    | .ok cmd =>
      pure cmd
    | .error msg =>
      -- We may skip tests if Python 3 is not available.
      if ← pythonTestRequired then
        throw msg
      return ()
  if not (← pythonCheckModule pythonCmd "strata.gen") then
    -- We may skip tests if stratal.gen is not available.
    if ← pythonTestRequired then
      throw <| .userError s!"Python Strata libraries not installed in {pythonCmd}."
    return ()
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
      let pgmCommands := pgm.commands.map (·.mapAnn (fun _ => ()))
      let expCommands := expectedPySpec.commands.map (·.mapAnn (fun _ => ()))
      assert! pgmCommands == expCommands
    | .error e =>
      throw <| IO.userError e

#guard_msgs in
#eval testCase

end Strata.Python.Specs
