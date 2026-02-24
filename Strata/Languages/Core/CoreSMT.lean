/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.SMT.SolverInterface
import Strata.DL.SMT.State
import Strata.Languages.Core.CoreSMT.IsCoreSMT
import Strata.Languages.Core.CoreSMT.ExprTranslator
import Strata.Languages.Core.CoreSMT.StmtVerifier
import Strata.Languages.Core.CoreSMT.Diagnosis
import Strata.Languages.Core.CoreSMT.Verifier

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

def CoreSMTState.init (solver : SMT.SolverInterface) (config : CoreSMTConfig := {}) : CoreSMTState :=
  { smtState := SMT.VerifierState.init solver, config }

-- Delegate methods to smtState
def CoreSMTState.push (state : CoreSMTState) : IO CoreSMTState := do
  let smtState ← state.smtState.push
  return { state with smtState }

def CoreSMTState.pop (state : CoreSMTState) : IO CoreSMTState := do
  let smtState ← state.smtState.pop
  return { state with smtState }

def CoreSMTState.addItem (state : CoreSMTState) (item : SMT.ContextItem) : CoreSMTState :=
  { state with smtState := state.smtState.addItem item }

def CoreSMTState.allContextItems (state : CoreSMTState) : List SMT.ContextItem :=
  state.smtState.allContextItems

def CoreSMTState.solver (state : CoreSMTState) : SMT.SolverInterface :=
  state.smtState.solver

def CoreSMTState.contextStack (state : CoreSMTState) : SMT.ContextStack :=
  state.smtState.contextStack

end Strata.Core.CoreSMT
