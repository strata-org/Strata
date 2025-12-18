/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

structure Z3Options where
  -- Will prepend `(set-option e.fst e.snd)` ... for each `e: String × String` in `options`
  options : List (String × String)

structure Options where
  verbose : Bool
  parseOnly : Bool
  typeCheckOnly : Bool
  checkOnly : Bool
  stopOnFirstError : Bool
  removeIrrelevantAxioms : Bool
  /-- Solver time limit in seconds -/
  solverTimeout : Nat
  z3Options: Option Z3Options


def Options.default : Options := {
  verbose := true,
  parseOnly := false,
  typeCheckOnly := false,
  checkOnly := false,
  stopOnFirstError := false,
  removeIrrelevantAxioms := false,
  solverTimeout := 10,
  z3Options := none,
}

instance : Inhabited Options where
  default := .default

def Options.quiet : Options :=
  { Options.default with verbose := false }
