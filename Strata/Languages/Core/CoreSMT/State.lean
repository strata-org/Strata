/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core.CoreSMT.SMTSolverInterface
import Strata.Languages.Core.Expressions
import Strata.Languages.Core.Options

/-!
# CoreSMT State and Context Management

Defines the verification state, configuration, and context tracking for the
CoreSMT verifier. The state is returned from verify calls to enable reuse
across multiple verification sessions.
-/

namespace Strata.Core.CoreSMT

open Strata.SMT

/-- Configuration for CoreSMT verification -/
structure CoreSMTConfig where
  /-- Enable automatic diagnosis of failures -/
  diagnosisEnabled : Bool := true
  /-- Continue verification after errors (accumulate all errors) -/
  accumulateErrors : Bool := true
  /-- Verbosity level for reporting -/
  verbose : VerboseMode := .normal
  deriving Repr, Inhabited

/-- A context item represents something added to the SMT solver state -/
inductive ContextItem where
  /-- An assumed expression (as SMT term) -/
  | assumption : Term → ContextItem
  /-- A declared sort (name, arity) -/
  | sortDecl : String → Nat → ContextItem
  /-- A declared function (name, arg types, return type) -/
  | funcDecl : String → List TermType → TermType → ContextItem
  /-- A defined function (name, args, return type, body) -/
  | funcDef : String → List (String × TermType) → TermType → Term → ContextItem
  /-- A declared variable (name, type) -/
  | varDecl : String → TermType → ContextItem
  /-- A defined variable (name, type, value) -/
  | varDef : String → TermType → Term → ContextItem

/-- A scope is a list of context items added at the same push level -/
abbrev ContextScope := List ContextItem

/-- Context stack: a stack of scopes, where each scope corresponds to a push level.
    The head of the list is the current (innermost) scope. -/
abbrev ContextStack := List ContextScope

/-- Verification state that can be reused across calls -/
structure CoreSMTState where
  /-- The SMT solver interface -/
  solver : SMTSolverInterface
  /-- Configuration -/
  config : CoreSMTConfig
  /-- Stack of context scopes (for push/pop support) -/
  contextStack : ContextStack
  /-- Number of verification results accumulated -/
  resultCount : Nat

/-- Create initial state from a solver interface -/
def CoreSMTState.init (solver : SMTSolverInterface) (config : CoreSMTConfig := {}) : CoreSMTState :=
  { solver, config, contextStack := [[]], resultCount := 0 }

/-- Push a new scope onto the context stack -/
def CoreSMTState.push (state : CoreSMTState) : IO CoreSMTState := do
  state.solver.push
  return { state with contextStack := [] :: state.contextStack }

/-- Pop the top scope from the context stack -/
def CoreSMTState.pop (state : CoreSMTState) : IO CoreSMTState := do
  state.solver.pop
  match state.contextStack with
  | []          => return state
  | _ :: rest   => return { state with contextStack := rest }

/-- Add an item to the current scope -/
def CoreSMTState.addItem (state : CoreSMTState) (item : ContextItem) : CoreSMTState :=
  match state.contextStack with
  | []            => { state with contextStack := [[item]] }
  | scope :: rest => { state with contextStack := (item :: scope) :: rest }

/-- Get all context items (flattened from all scopes) for error reporting -/
def CoreSMTState.allContextItems (state : CoreSMTState) : List ContextItem :=
  state.contextStack.flatten

/-- Increment the result count -/
def CoreSMTState.incResultCount (state : CoreSMTState) : CoreSMTState :=
  { state with resultCount := state.resultCount + 1 }

end Strata.Core.CoreSMT
