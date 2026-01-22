/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Util.TestDiagnostics
import Strata.DDM.Elab
import Strata.DDM.BuiltinDialects.Init
import Strata.Util.IO
import Strata.Languages.Laurel.Grammar.LaurelGrammar
import Strata.Languages.Laurel.Grammar.ConcreteToAbstractTreeTranslator
import Strata.Languages.Laurel.LaurelToCoreTranslator

open StrataTest.Util
open Strata
open Strata.Elab (parseStrataProgramFromDialect)
open Lean.Parser (InputContext)

namespace Strata
namespace Laurel

def processLaurelFile (input : InputContext) : IO (Array Diagnostic) := do
  let dialects := Strata.Elab.LoadedDialects.ofDialects! #[initDialect, Laurel]
  let strataProgram ← parseStrataProgramFromDialect dialects Laurel.name input

  let uri := Strata.Uri.file input.fileName
  let transResult := Laurel.TransM.run uri (Laurel.parseProgram strataProgram)
  match transResult with
  | .error transErrors => throw (IO.userError s!"Translation errors: {transErrors}")
  | .ok laurelProgram =>
    let files := Map.insert Map.empty uri input.fileMap
    let diagnostics ← Laurel.verifyToDiagnostics "z3" files laurelProgram

    pure diagnostics

end Laurel
