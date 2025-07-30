/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

structure Options where
  verbose : Bool
  checkOnly : Bool
  solverTimeout : Nat -- Solver time limit in seconds

def Options.default : Options := {
  verbose := true,
  checkOnly := false,
  solverTimeout := 10
}

instance : Inhabited Options where
  default := .default

def Options.quiet : Options :=
  { Options.default with verbose := false }
