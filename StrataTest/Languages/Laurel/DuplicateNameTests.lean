/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Tests that the resolution pass detects duplicate names in the same scope.
Uses inline error annotations like the other Laurel tests (e.g. T1_AssertFalse).
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

/-! ## Duplicate static procedure names -/

def dupProcedures := r"
procedure foo() { };
procedure foo() { };
//        ^^^ error: Duplicate definition 'foo' is already defined in this scope
"

#guard_msgs (error, drop all) in
#eval testInputWithOffset "DupProcedures" dupProcedures 35 processResolution

/-! ## Duplicate type names -/

def dupTypes := r"
composite Foo { }
composite Foo { }
//        ^^^ error: Duplicate definition 'Foo' is already defined in this scope
"

#guard_msgs (error, drop all) in
#eval testInputWithOffset "DupTypes" dupTypes 43 processResolution

/-! ## Duplicate field names in a composite type -/

def dupFields := r"
composite Foo {
  var f: int
  var f: bool
//    ^ error: Duplicate definition 'Foo.f' is already defined in this scope
}
"

#guard_msgs (error, drop all) in
#eval testInputWithOffset "DupFields" dupFields 51 processResolution

/-! ## Duplicate parameter names in a procedure -/

def dupParams := r"
procedure foo(x: int, x: bool) { };
//                    ^ error: Duplicate definition 'x' is already defined in this scope
"

#guard_msgs (error, drop all) in
#eval testInputWithOffset "DupParams" dupParams 61 processResolution

/-! ## Duplicate instance procedure names in a composite type -/

def dupInstanceProcs := r"
composite Foo {
  procedure bar() { };
  procedure bar() { };
//          ^^^ error: Duplicate definition 'bar' is already defined in this scope
}
"

#guard_msgs (error, drop all) in
#eval testInputWithOffset "DupInstanceProcs" dupInstanceProcs 71 processResolution

/-! ## Duplicate local variable names in the same block -/

def dupLocals := r"
procedure foo() {
  var x: int := 1;
  var x: int := 2
//    ^ error: Duplicate definition 'x' is already defined in this scope
};
"

#guard_msgs (error, drop all) in
#eval testInputWithOffset "DupLocals" dupLocals 81 processResolution

/-! ## Procedure and type with the same name -/

def dupProcType := r"
composite Foo { }
procedure Foo() { };
//        ^^^ error: Duplicate definition 'Foo' is already defined in this scope
"

#guard_msgs (error, drop all) in
#eval testInputWithOffset "DupProcType" dupProcType 91 processResolution

/-! ## Shadowing quantifier variables in nested scopes is OK (no error expected) -/

def shadowQuantifierVars := r"
procedure test() {
  assert forall(x: int) => forall(x: int) => x > 0
};
"

#guard_msgs (error, drop all) in
#eval testInputWithOffset "ShadowQuantifierVars" shadowQuantifierVars 99 processResolution

/-! ## Shadowing in nested blocks is OK (no error expected) -/

def shadowingOk := r"
procedure foo() {
  var x: int := 1;
  {
    var x: int := 2
  }
};
"

#guard_msgs (error, drop all) in
#eval testInputWithOffset "ShadowingOk" shadowingOk 109 processResolution

/-! ## Duplicate constrained type names -/

def dupConstrainedTypes := r"
constrained nat = x: int where x >= 0 witness 0
constrained nat = x: int where x > 0 witness 1
//          ^^^ error: Duplicate definition 'nat' is already defined in this scope
"

#guard_msgs (error, drop all) in
#eval testInputWithOffset "DupConstrainedTypes" dupConstrainedTypes 119 processResolution

/-! ## Duplicate datatype names -/

def dupDatatypes := r"
datatype Foo { A }
datatype Foo { B }
//       ^^^ error: Duplicate definition 'Foo' is already defined in this scope
"

#guard_msgs (error, drop all) in
#eval testInputWithOffset "DupDatatypes" dupDatatypes 127 processResolution

/-! ## Composite type and datatype with the same name -/

def dupCompositeDatatype := r"
composite Foo { }
datatype Foo { A }
//       ^^^ error: Duplicate definition 'Foo' is already defined in this scope
"

#guard_msgs (error, drop all) in
#eval testInputWithOffset "DupCompositeDatatype" dupCompositeDatatype 135 processResolution

/-! ## Field access on non-self object does not produce resolution error

When accessing a field on a non-self object (e.g., `session#region_name`),
the field name should NOT be treated as a variable reference. Previously,
`resolveFieldRef` fell back to `resolveRef` which emitted a spurious
"Resolution failed" error for unknown fields. -/

def fieldAccessKnown := r"
composite Session { var name: int }
procedure test(s: Session) {
  var x: int := s#name
};
"

/--
info: ✓ Test passed: All 0 error(s) matched -/
#guard_msgs in
#eval testInputWithOffset "FieldAccessKnown" fieldAccessKnown 0 processResolution

def fieldAccessUnknown := r"
composite Session { var name: int }
procedure test(s: Session) {
  var x: int := s#region_name
};
"

/--
info: ✓ Test passed: All 0 error(s) matched -/
#guard_msgs in
#eval testInputWithOffset "FieldAccessUnknown" fieldAccessUnknown 0 processResolution

end Laurel
