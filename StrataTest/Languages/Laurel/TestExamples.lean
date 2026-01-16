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

namespace Laurel

def processLaurelFile (input : InputContext) : IO (Array Diagnostic) := do
  let dialects := Strata.Elab.LoadedDialects.ofDialects! #[initDialect, Laurel]
  let strataProgram ← parseStrataProgramFromDialect dialects Laurel.name input

  -- Convert to Laurel.Program using parseProgram (handles unwrapping the program operation)
  let laurelProgram ← match Laurel.TransM.run input (Laurel.parseProgram strataProgram) with
    | .ok program => pure program
    | .error errMsg => throw (IO.userError s!"Translation error: {errMsg}")

  -- Verify the program
  let diagnostics ← Laurel.verifyToDiagnostics "z3" laurelProgram

  pure diagnostics

end Laurel
