/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

structure Options where
  verbose : Bool
  checkOnly : Bool
  /-- Solver time limit in seconds -/
  solverTimeout : Nat

def Options.default : Options := {
  verbose := true,
  checkOnly := false,
  solverTimeout := 10
}

instance : Inhabited Options where
  default := .default

def Options.quiet : Options :=
  { Options.default with verbose := false }
