/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

inductive VerboseMode where
  | quiet
  | models
  | normal
  | debug
  deriving Inhabited, Repr, DecidableEq

def VerboseMode.toNat (v : VerboseMode) : Nat :=
  match v with
  | .quiet => 0
  | .models => 1
  | .normal => 2
  | .debug => 3

def VerboseMode.ofBool (b : Bool) : VerboseMode :=
  match b with
  | false => .quiet
  | true => .normal

instance : Coe VerboseMode Nat where
  coe := VerboseMode.toNat

instance : LT VerboseMode where
  lt a b := a.toNat < b.toNat

instance : DecidableRel (fun a b : VerboseMode => a < b) :=
  fun a b => decidable_of_iff (a.toNat < b.toNat) Iff.rfl

instance : LE VerboseMode where
  le a b := a.toNat ≤ b.toNat

instance : DecidableRel (fun a b : VerboseMode => a ≤ b) :=
  fun a b => decidable_of_iff (a.toNat ≤ b.toNat) Iff.rfl

/-- Default SMT solver to use -/
def defaultSolver : String := "cvc5"

structure Options where
  verbose : VerboseMode
  parseOnly : Bool
  typeCheckOnly : Bool
  checkOnly : Bool
  stopOnFirstError : Bool
  removeIrrelevantAxioms : Bool
  /-- Solver time limit in seconds -/
  solverTimeout : Nat
  /-- Output results in SARIF format -/
  outputSarif : Bool
  /-- SMT solver executable to use -/
  solver : String

def Options.default : Options := {
  verbose := .normal,
  parseOnly := false,
  typeCheckOnly := false,
  checkOnly := false,
  stopOnFirstError := false,
  removeIrrelevantAxioms := false,
  solverTimeout := 10,
  outputSarif := false,
  solver := defaultSolver
}

instance : Inhabited Options where
  default := .default

def Options.quiet : Options :=
  { Options.default with verbose := .quiet }

def Options.models : Options :=
  { Options.default with verbose := .models }

def Options.debug : Options :=
  { Options.default with verbose := .debug }
