/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.B3.Verifier.Conversion
import Strata.Languages.B3.Verifier.Formatter
import Strata.DL.SMT.Solver

/-!
# B3 Verification State

Manages incremental verification state for interactive debugging.
-/

namespace Strata.B3.Verifier

open Strata.SMT

---------------------------------------------------------------------
-- Verification State
---------------------------------------------------------------------

structure B3VerificationState where
  declaredFunctions : List (String × List String × String)  -- (name, argTypes, returnType)
  assertions : List Term  -- Accumulated assertions (axioms, function definitions)
  context : ConversionContext

structure CheckResult where
  decl : B3AST.Decl SourceRange  -- Source declaration with location info
  sourceStmt : Option (B3AST.Statement SourceRange) := none  -- Specific statement that failed
  decision : Decision
  model : Option String := none

def initVerificationState : B3VerificationState := {
  declaredFunctions := []
  assertions := []
  context := ConversionContext.empty
}

def addFunctionDecl (state : B3VerificationState) (name : String) (argTypes : List String) (returnType : String) : B3VerificationState :=
  { state with declaredFunctions := (name, argTypes, returnType) :: state.declaredFunctions }

def addAssertion (state : B3VerificationState) (term : Term) : B3VerificationState :=
  { state with assertions := term :: state.assertions }

def checkProperty (state : B3VerificationState) (term : Term) (sourceDecl : B3AST.Decl SourceRange) (sourceStmt : Option (B3AST.Statement SourceRange)) (solverPath : String := "z3") : IO CheckResult := do
  let solver ← Solver.spawn solverPath #["-smt2", "-in"]
  let runCheck : SolverM Decision := do
    Solver.setLogic "ALL"
    for (name, argTypes, returnType) in state.declaredFunctions.reverse do
      Solver.declareFun name argTypes returnType
    for assertion in state.assertions.reverse do
      Solver.assert (formatTermDirect assertion)
    Solver.assert s!"(not {formatTermDirect term})"
    Solver.checkSat []
  let decision ← runCheck.run solver
  let _ ← (Solver.exit).run solver
  return {
    decl := sourceDecl
    sourceStmt := sourceStmt
    decision := decision
    model := none
  }

end Strata.B3.Verifier
