/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Tests that the resolution pass detects duplicate names in the same scope.
Each test case exercises a different kind of duplicate that can occur in a
Laurel program.
-/

import Strata.DDM.Elab
import Strata.DDM.BuiltinDialects.Init
import Strata.Languages.Laurel.Grammar.LaurelGrammar
import Strata.Languages.Laurel.Grammar.ConcreteToAbstractTreeTranslator
import Strata.Languages.Laurel.Resolution

open Strata
open Strata.Elab (parseStrataProgramFromDialect)

namespace Strata.Laurel

/-- Parse a Laurel source string and return the resolution errors. -/
private def resolveErrors (input : String) : IO (Array String) := do
  let inputCtx := Strata.Parser.stringInputContext "test" input
  let dialects := Strata.Elab.LoadedDialects.ofDialects! #[initDialect, Laurel]
  let strataProgram ← parseStrataProgramFromDialect dialects Laurel.name inputCtx
  let uri := Strata.Uri.file "test"
  match Laurel.TransM.run uri (Laurel.parseProgram strataProgram) with
  | .error e => throw (IO.userError s!"Translation errors: {e}")
  | .ok program =>
    let result := resolve program
    return result.errors.map toString

private def printErrors (input : String) : IO Unit := do
  let errs ← resolveErrors input
  if errs.isEmpty then
    IO.println "no errors"
  else
    for e in errs do
      IO.println e

/-! ## Duplicate static procedure names -/

def dupProcedures := r"
procedure foo() { };
procedure foo() { };
"

#eval printErrors dupProcedures

/-! ## Duplicate type names -/

def dupTypes := r"
composite Foo { }
composite Foo { }
"

#eval printErrors dupTypes

/-! ## Duplicate field names in a composite type -/

def dupFields := r"
composite Foo {
  var f: int
  var f: bool
}
"

#eval printErrors dupFields

/-! ## Duplicate parameter names in a procedure -/

def dupParams := r"
procedure foo(x: int, x: bool) { };
"

#eval printErrors dupParams

/-! ## Duplicate instance procedure names in a composite type -/

def dupInstanceProcs := r"
composite Foo {
  procedure bar() { };
  procedure bar() { };
}
"

#eval printErrors dupInstanceProcs

/-! ## Duplicate datatype constructor names -/

def dupCtors := r"
datatype Foo { A, A }
"

#eval printErrors dupCtors

/-! ## Duplicate local variable names in the same block -/

def dupLocals := r"
procedure foo() {
  var x: int := 1;
  var x: int := 2
};
"

#eval printErrors dupLocals

/-! ## Procedure and type with the same name -/

def dupProcType := r"
composite Foo { }
procedure Foo() { };
"

#eval printErrors dupProcType

/-! ## Duplicate quantifier variable names (nested forall) -/

def dupQuantifierVars := r"
procedure test() {
  assert forall(x: int) => forall(x: int) => x > 0
};
"

#eval printErrors dupQuantifierVars

/-! ## Shadowing in nested scopes is OK (no error expected) -/

def shadowingOk := r"
procedure foo() {
  var x: int := 1;
  {
    var x: int := 2
  }
};
"

#eval printErrors shadowingOk

/-! ## Duplicate constrained type names -/

def dupConstrainedTypes := r"
constrained nat = x: int where x >= 0 witness 0
constrained nat = x: int where x > 0 witness 1
"

#eval printErrors dupConstrainedTypes

/-! ## Duplicate datatype names -/

def dupDatatypes := r"
datatype Foo { A }
datatype Foo { B }
"

#eval printErrors dupDatatypes

/-! ## Composite type and datatype with the same name -/

def dupCompositeDatatype := r"
composite Foo { }
datatype Foo { A }
"

#eval printErrors dupCompositeDatatype

end Laurel
