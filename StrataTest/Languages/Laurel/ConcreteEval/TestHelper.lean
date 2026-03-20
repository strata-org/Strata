/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.Elab
import Strata.DDM.BuiltinDialects.Init
import Strata.Languages.Laurel.Grammar.LaurelGrammar
import Strata.Languages.Laurel.Grammar.ConcreteToAbstractTreeTranslator
import Strata.Languages.Laurel.Resolution
import Strata.Languages.Laurel.LaurelConcreteEval

/-!
# Shared Test Helpers for Laurel ConcreteEval Tests

Reusable `parseLaurel` helper and programmatic AST construction utilities
extracted from `LaurelConcreteEvalTest.lean`.
-/

namespace Strata.Laurel.ConcreteEval.TestHelper

open Strata
open Strata.Elab (parseStrataProgramFromDialect)
open Strata.Laurel

/-! ## Parsing Helper -/

def parseLaurel (input : String) : IO Laurel.Program := do
  let inputCtx := Strata.Parser.stringInputContext "test" input
  let dialects := Strata.Elab.LoadedDialects.ofDialects! #[initDialect, Laurel]
  let strataProgram ← parseStrataProgramFromDialect dialects Laurel.name inputCtx
  let uri := Strata.Uri.file "test"
  match Laurel.TransM.run uri (Laurel.parseProgram strataProgram) with
  | .error e => throw (IO.userError s!"Translation errors: {e}")
  | .ok program =>
    let result := resolve program
    return result.program

/-! ## Programmatic AST Helpers -/

abbrev emd : Imperative.MetaData Core.Expression := .empty
def mk (s : StmtExpr) : StmtExprMd := ⟨s, emd⟩

def mkProc (name : String) (inputs : List Parameter := [])
    (body : StmtExpr) : Procedure :=
  { name := mkId name, inputs := inputs, outputs := [],
    preconditions := [], determinism := .deterministic none,
    isFunctional := false, decreases := none,
    body := .Transparent (mk body), md := emd }

def mkProgram (procs : List Procedure) : Program :=
  { staticProcedures := procs, staticFields := [], types := [], constants := [] }

/-! ## Outcome Helper -/

def getOutcome (r : Option (Outcome × LaurelStore × LaurelHeap)) : Option Outcome :=
  r.map (·.1)

end Strata.Laurel.ConcreteEval.TestHelper
