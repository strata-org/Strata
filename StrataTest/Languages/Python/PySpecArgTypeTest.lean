/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Python.PySpecPipeline
import Strata.Languages.Python.Specs.DDM

/-! ## Test: specArgToFuncDeclArg preserves parameter type info

Verifies that `buildPySpecLaurel` populates `laurelType` and `typeTesters`
on `PyArgInfo` from PySpec `SpecType` atoms.
-/

namespace Strata.Python.PySpecArgTypeTest

open Strata.Python.Specs
open Strata (buildPySpecLaurel)
open Strata.Python (OverloadTable PythonFunctionDecl PyArgInfo highTypeToPyLauType)

private def loc : SourceRange := default

private def identType (nm : PythonIdent) : SpecType :=
  SpecType.ident loc nm

private def mkArg (name : String) (type : SpecType) : Specs.Arg :=
  { name, type }

private def mkFunc (name : String) (args : Array Specs.Arg) (ret : SpecType) : Signature :=
  .functionDecl {
    loc, nameLoc := loc, name
    args := { args, kwonly := #[] }
    returnType := ret
    isOverload := false
    preconditions := #[], postconditions := #[]
  }

/-- Build PySpec signatures, write to temp Ion, read back via buildPySpecLaurel,
    and return the extracted PythonFunctionDecl list. -/
private def getFuncSigs (sigs : Array Signature) : IO (List PythonFunctionDecl) := do
  IO.FS.withTempDir fun dir => do
    let ionFile := dir / "test.pyspec.ion"
    writeDDM ionFile sigs
    let result ← buildPySpecLaurel #[("", ionFile.toString)] {} |>.toBaseIO
    match result with
    | .ok r => pure r.functionSignatures
    | .error msg => throw <| .userError msg

private def unionType (elts : Array SpecType) : SpecType :=
  SpecType.unionArray loc elts

/--
info: typed_func: x=Any[Any..isfrom_int], y=Any[Any..isfrom_str], z=Any[Any..isfrom_bool], w=Any[Any..isfrom_float]
untyped_func: a=Any[]
mixed_func: p=Any[Any..isfrom_str], q=Any[]
optional_func: s=Any[Any..isfrom_None, Any..isfrom_str], n=Any[Any..isfrom_None, Any..isfrom_int]
-/
#guard_msgs in
#eval do
  let sigs ← getFuncSigs #[
    mkFunc "typed_func"
      #[mkArg "x" (identType .builtinsInt),
        mkArg "y" (identType .builtinsStr),
        mkArg "z" (identType .builtinsBool),
        mkArg "w" (identType .builtinsFloat)]
      (identType .noneType),
    mkFunc "untyped_func"
      #[mkArg "a" (identType .typingAny)]
      (identType .noneType),
    mkFunc "mixed_func"
      #[mkArg "p" (identType .builtinsStr),
        mkArg "q" (identType .typingAny)]
      (identType .noneType),
    mkFunc "optional_func"
      #[mkArg "s" (unionType #[identType .noneType, identType .builtinsStr]),
        mkArg "n" (unionType #[identType .noneType, identType .builtinsInt])]
      (identType .noneType)
  ]
  for f in sigs do
    let argStrs := ", ".intercalate (f.args.map fun (a : PyArgInfo) =>
      s!"{a.name}={highTypeToPyLauType a.laurelType.val}{a.typeTesters.toList}")
    IO.println s!"{f.name}: {argStrs}"

end Strata.Python.PySpecArgTypeTest
