/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.SMT.SolverInterface
import Strata.Languages.Core.Expressions

/-!
# SMT State and Context Management

Defines the verification state, configuration, and context tracking for SMT-based
verification. The state is returned from verify calls to enable reuse across
multiple verification sessions.
-/

namespace Strata.SMT

open Strata.SMT

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
structure VerifierState where
  /-- The SMT solver interface -/
  solver : SMT.SolverInterface
  /-- Stack of context scopes (for push/pop support) -/
  contextStack : ContextStack
  /-- Number of verification results accumulated -/
  resultCount : Nat

/-- Create initial state from a solver interface -/
def VerifierState.init (solver : SMT.SolverInterface) : VerifierState :=
  { solver, contextStack := [[]], resultCount := 0 }

/-- Push a new scope onto the context stack -/
def VerifierState.push (state : VerifierState) : IO VerifierState := do
  state.solver.push
  return { state with contextStack := [] :: state.contextStack }

/-- Pop the top scope from the context stack -/
def VerifierState.pop (state : VerifierState) : IO VerifierState := do
  state.solver.pop
  match state.contextStack with
  | []          => return state
  | _ :: rest   => return { state with contextStack := rest }

/-- Add an item to the current scope -/
def VerifierState.addItem (state : VerifierState) (item : ContextItem) : VerifierState :=
  match state.contextStack with
  | []            => { state with contextStack := [[item]] }
  | scope :: rest => { state with contextStack := (item :: scope) :: rest }

/-- Get all context items (flattened from all scopes) for error reporting -/
def VerifierState.allContextItems (state : VerifierState) : List ContextItem :=
  state.contextStack.flatten

/-- Increment the result count -/
def VerifierState.incResultCount (state : VerifierState) : VerifierState :=
  { state with resultCount := state.resultCount + 1 }

end Strata.SMT
