/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.B3.Verifier.Conversion
import Strata.DL.SMT.SMT

/-!
# B3 Statement to SMT Conversion

Converts B3 statements to SMT verification conditions via symbolic execution.

## Verification Condition Generation (VCG)

Statements are converted to verification conditions using symbolic execution:
- `var x := e` - introduces a new SMT constant
- `x := e` - updates the variable mapping
- `assert e` - generates a verification condition (check e holds)
- `assume e` - adds e to the path condition
- `check e` - like assert, generates a VC
- `if c then s1 else s2` - symbolic execution on both branches

## State Management

During VCG, we maintain:
- Variable incarnations (SSA-style renaming)
- Path conditions (accumulated assumptions)
- Verification conditions (assertions to check)
-/

namespace Strata.B3.Verifier

open Strata.SMT

structure VCGenState where
  varIncarnations : List (String × Nat)  -- Maps variable name to current incarnation number
  pathConditions : List Term  -- Accumulated assumptions
  verificationConditions : List (Term × B3AST.Statement SourceRange)  -- VCs with source statements

namespace VCGenState

def empty : VCGenState := {
  varIncarnations := []
  pathConditions := []
  verificationConditions := []
}

def freshIncarnation (state : VCGenState) (varName : String) : VCGenState × String :=
  match state.varIncarnations.find? (fun (n, _) => n == varName) with
  | some (_, inc) =>
      let newInc := inc + 1
      let newState := { state with
        varIncarnations := (varName, newInc) :: state.varIncarnations.filter (fun (n, _) => n != varName)
      }
      (newState, s!"{varName}_{newInc}")
  | none =>
      let newState := { state with varIncarnations := (varName, 0) :: state.varIncarnations }
      (newState, s!"{varName}_0")

def getCurrentIncarnation (state : VCGenState) (varName : String) : Option String :=
  match state.varIncarnations.find? (fun (n, _) => n == varName) with
  | some (_, inc) => some s!"{varName}_{inc}"
  | none => none

def addPathCondition (state : VCGenState) (cond : Term) : VCGenState :=
  { state with pathConditions := cond :: state.pathConditions }

def addVC (state : VCGenState) (vc : Term) (source : B3AST.Statement SourceRange) : VCGenState :=
  { state with verificationConditions := (vc, source) :: state.verificationConditions }

end VCGenState

/-- Convert B3 statement to verification conditions -/
partial def statementToVCs (ctx : ConversionContext) (state : VCGenState) : B3AST.Statement SourceRange → VCGenState
  | .check m expr =>
      -- Generate VC: path conditions => expr
      match expressionToSMT ctx expr with
      | some term =>
          let vc := if state.pathConditions.isEmpty then
            term
          else
            let pathCond := state.pathConditions.foldl (fun acc t => Term.app .and [acc, t] .bool) (Term.bool true)
            Term.app .implies [pathCond, term] .bool
          state.addVC vc (.check m expr)
      | none => state
  | .assert m expr =>
      -- Assert = check + assume
      match expressionToSMT ctx expr with
      | some term =>
          -- First, generate VC like check
          let vc := if state.pathConditions.isEmpty then
            term
          else
            let pathCond := state.pathConditions.foldl (fun acc t => Term.app .and [acc, t] .bool) (Term.bool true)
            Term.app .implies [pathCond, term] .bool
          let state' := state.addVC vc (.assert m expr)
          -- Then, add to path conditions like assume
          state'.addPathCondition term
      | none => state
  | .assume _ expr =>
      -- Add to path conditions
      match expressionToSMT ctx expr with
      | some term => state.addPathCondition term
      | none => state
  | .blockStmt _ stmts =>
      -- Process statements sequentially
      stmts.val.toList.foldl (statementToVCs ctx) state
  | _ => state  -- TODO: Other statements

end Strata.B3.Verifier
