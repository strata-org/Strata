/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

namespace Strata.SMT

structure Options where
  /-- Path to the SMT solver -/
  solver : String
  verbose : Bool
  checkOnly : Bool
  /-- Solver time limit in seconds -/
  solverTimeout : Nat

/--
The default options assume that `cvc5` is in the path.
-/
def Options.default : Options := {
  solver := "cvc5"
  verbose := true,
  checkOnly := false,
  solverTimeout := 10
}

instance : Inhabited Options where
  default := .default

def Options.quiet : Options :=
  { Options.default with verbose := false }
