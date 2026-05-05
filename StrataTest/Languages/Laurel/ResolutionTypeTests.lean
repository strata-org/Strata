/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/-
Tests that the resolution pass detects type checking errors — e.g. using a
multi-output procedure in expression position.
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

/-! ## Multi-output procedure used in expression position -/

def multiOutputInExpr := r"
procedure multi(x: int) returns (a: int, b: int) opaque;
procedure test() opaque {
  assert multi(1) == 1
//       ^^^^^^^^ error: Multi-output procedure 'multi' used in expression position
};
"

#guard_msgs (error, drop all) in
#eval testInputWithOffset "MultiOutputInExpr" multiOutputInExpr 42 processResolution

end Laurel
