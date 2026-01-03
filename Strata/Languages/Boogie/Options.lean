/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

inductive IrrelevantAxiomsMode where
  /--
    Only the functions in the consequent `Q` of a goal `P ==> Q` will be
    taken into account for relevant axiom analysis. This means that axioms
    relevant to some function in `P` (but not in `Q`) may be removed. This is
    sound, but may yield unknown results from the solver.
  -/
  | Aggressive
  /--
   Functions in both `P` and `Q` of a goal `P ==> Q` will be considered for
   relevant axiom analysis.
  -/
  | Precise
  /-- Do not prune any axioms. -/
  | Off
  deriving Repr, DecidableEq, Inhabited

structure Options where
  verbose : Bool
  parseOnly : Bool
  typeCheckOnly : Bool
  checkOnly : Bool
  stopOnFirstError : Bool
  removeIrrelevantAxioms : IrrelevantAxiomsMode
  /-- Solver time limit in seconds -/
  solverTimeout : Nat

def Options.default : Options := {
  verbose := true,
  parseOnly := false,
  typeCheckOnly := false,
  checkOnly := false,
  stopOnFirstError := false,
  removeIrrelevantAxioms := IrrelevantAxiomsMode.Off,
  solverTimeout := 10
}

instance : Inhabited Options where
  default := .default

def Options.quiet : Options :=
  { Options.default with verbose := false }
