/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Tests that the resolution pass detects kind mismatches — e.g. using a variable
where a type is expected, or calling a type as if it were a procedure.
-/

import StrataTest.Util.TestDiagnostics
import Strata.DDM.Elab
import Strata.DDM.BuiltinDialects.Init
import Strata.Languages.Laurel.Grammar.LaurelGrammar
import Strata.Languages.Laurel.Grammar.ConcreteToAbstractTreeTranslator
import Strata.Languages.Laurel.Resolution

open StrataTest.Util
open Strata
open Strata.Elab (parseStrataProgramFromDialect)

namespace Strata.Laurel

/-- Run only parsing + resolution and return diagnostics (no SMT verification). -/
private def processResolution (input : Lean.Parser.InputContext) : IO (Array Diagnostic) := do
  let dialects := Strata.Elab.LoadedDialects.ofDialects! #[initDialect, Laurel]
  let strataProgram ← parseStrataProgramFromDialect dialects Laurel.name input
  let uri := Strata.Uri.file input.fileName
  match Laurel.TransM.run uri (Laurel.parseProgram strataProgram) with
  | .error e => throw (IO.userError s!"Translation errors: {e}")
  | .ok program =>
    let result := resolve program
    let files := Map.insert Map.empty uri input.fileMap
    return result.errors.toList.map (fun dm => dm.toDiagnostic files) |>.toArray

/-! ## Using a variable name where a type is expected -/

def varAsType := r"
procedure foo() opaque {
  var x: int := 1;
  var y: x := 2
//       ^ error: 'x' resolves to variable, but expected composite type, constrained type, datatype definition, type alias
};
"

#guard_msgs (error, drop all) in
#eval testInputWithOffset "VarAsType" varAsType 39 processResolution

/-! ## Using a procedure name where a type is expected -/

def procAsType := r"
procedure bar() opaque { };
procedure foo() opaque {
  var y: bar := 1
//       ^^^ error: 'bar' resolves to static procedure, but expected composite type, constrained type, datatype definition, type alias
};
"

#guard_msgs (error, drop all) in
#eval testInputWithOffset "ProcAsType" procAsType 51 processResolution

/-! ## Calling a composite type as a static call -/

def typeAsStaticCall := r"
composite Foo { }
procedure bar() opaque {
  var x: int := Foo()
//              ^^^^^ error: 'Foo' resolves to composite type, but expected parameter, static procedure, datatype constructor, constant
};
"

#guard_msgs (error, drop all) in
#eval testInputWithOffset "TypeAsStaticCall" typeAsStaticCall 61 processResolution

/-! ## Using a procedure name with `new` -/

def newWithProc := r"
procedure bar() opaque { };
procedure foo() opaque {
  var x: int := new bar
//              ^^^^^^^ error: 'bar' resolves to static procedure, but expected composite type, datatype definition
};
"

#guard_msgs (error, drop all) in
#eval testInputWithOffset "NewWithProc" newWithProc 73 processResolution

/-! ## Extending a non-composite type (e.g. a constrained type) -/

def extendConstrained := r"
constrained nat = x: int where x >= 0 witness 0
composite Foo extends nat { }
//                    ^^^ error: 'nat' resolves to constrained type, but expected composite type
"

#guard_msgs (error, drop all) in
#eval testInputWithOffset "ExtendConstrained" extendConstrained 83 processResolution

end Laurel
