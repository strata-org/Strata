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

/-- Verification mode for SARIF error level mapping -/
inductive VerificationMode where
  | deductive  -- Prove correctness (unknown is error)
  | bugFinding -- Find bugs (provably false if reached/reachable is error, unreachable is warning)
  deriving Inhabited, Repr, DecidableEq

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

/-- Check amount: how much information to gather -/
inductive CheckAmount where
  | minimal  -- Only checks needed for check mode
  | full     -- Both checks for more informative messages
  deriving Inhabited, Repr, DecidableEq

structure Options where
  verbose : VerboseMode
  parseOnly : Bool
  typeCheckOnly : Bool
  checkOnly : Bool
  stopOnFirstError : Bool
  removeIrrelevantAxioms : Bool
  /-- Use SMT-LIB Array theory instead of axiomatized maps -/
  useArrayTheory : Bool
  /-- Solver time limit in seconds -/
  solverTimeout : Nat
  /-- Output results in SARIF format -/
  outputSarif : Bool
  /-- SMT solver executable to use -/
  solver : String
  /-- Directory to store VCs -/
  vcDirectory : Option System.FilePath
  /-- Check mode: deductive (prove correctness) or bugFinding (find bugs) -/
  checkMode : VerificationMode
  /-- Check amount: minimal (only necessary checks) or full (both checks for better messages) -/
  checkAmount : CheckAmount

def Options.default : Options := {
  verbose := .normal,
  parseOnly := false,
  typeCheckOnly := false,
  checkOnly := false,
  stopOnFirstError := false,
  removeIrrelevantAxioms := false,
  useArrayTheory := false,
  solverTimeout := 10,
  outputSarif := false,
  solver := defaultSolver
  vcDirectory := .none
  checkMode := .deductive
  checkAmount := .minimal
}

instance : Inhabited Options where
  default := .default

def Options.quiet : Options :=
  { Options.default with verbose := .quiet }

def Options.models : Options :=
  { Options.default with verbose := .models }

def Options.debug : Options :=
  { Options.default with verbose := .debug }
