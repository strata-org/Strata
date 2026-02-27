/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.SMT.State

namespace Strata.Core.CoreSMT

/-- Configuration for CoreSMT verification -/
structure CoreSMTConfig where
  /-- Continue verification after errors (accumulate all errors) -/
  accumulateErrors : Bool := true
  deriving Repr, Inhabited

/-- CoreSMT verification state -/
structure CoreSMTState where
  /-- SMT solver state -/
  smtState : SMT.VerifierState
  /-- CoreSMT-specific configuration -/
  config : CoreSMTConfig
  /-- Stack of Core expression assumptions (for diagnosis path conditions) -/
  assumptionStack : List (List Core.Expression.Expr) := [[]]

def CoreSMTState.init (solver : SMT.SolverInterface) (config : CoreSMTConfig := {}) : CoreSMTState :=
  { smtState := SMT.VerifierState.init solver, config }

/-- Get current path condition (all assumptions in scope) -/
def CoreSMTState.pathCondition (state : CoreSMTState) : List Core.Expression.Expr :=
  state.assumptionStack.flatten

/-- Add a Core expression assumption to the current scope -/
def CoreSMTState.addAssumption (state : CoreSMTState) (e : Core.Expression.Expr) : CoreSMTState :=
  match state.assumptionStack with
  | [] => { state with assumptionStack := [[e]] }
  | scope :: rest => { state with assumptionStack := (e :: scope) :: rest }

-- Delegate methods to smtState
def CoreSMTState.push (state : CoreSMTState) : IO CoreSMTState := do
  let smtState ← state.smtState.push
  return { state with smtState, assumptionStack := [] :: state.assumptionStack }

def CoreSMTState.pop (state : CoreSMTState) : IO CoreSMTState := do
  let smtState ← state.smtState.pop
  match state.assumptionStack with
  | [] => return { state with smtState }
  | _ :: rest => return { state with smtState, assumptionStack := rest }

def CoreSMTState.addItem (state : CoreSMTState) (item : SMT.ContextItem) : CoreSMTState :=
  { state with smtState := state.smtState.addItem item }

def CoreSMTState.allContextItems (state : CoreSMTState) : List SMT.ContextItem :=
  state.smtState.allContextItems

-- Accessors for SMT state fields (as abbrevs for dot notation)
@[inline] def CoreSMTState.solver (state : CoreSMTState) : SMT.SolverInterface :=
  state.smtState.solver

@[inline] def CoreSMTState.contextStack (state : CoreSMTState) : SMT.ContextStack :=
  state.smtState.contextStack

end Strata.Core.CoreSMT
