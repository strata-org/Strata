/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public section
namespace Core

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
  | bugFinding -- Find bugs assuming incomplete preconditions (only definite bugs are errors)
  | bugFindingAssumingCompleteSpec -- Find bugs assuming complete preconditions (any counterexample is error)
  deriving Repr, DecidableEq

instance : Inhabited VerificationMode where
  default := .deductive

def VerificationMode.ofString? (s : String) : Option VerificationMode :=
  match s with
  | "deductive" => some .deductive
  | "bugFinding" => some .bugFinding
  | "bugFindingAssumingCompleteSpec" => some .bugFindingAssumingCompleteSpec
  | _ => none

def VerificationMode.options : String :=
  "'deductive' (prove correctness), 'bugFinding' (find bugs), or 'bugFindingAssumingCompleteSpec' (find bugs assuming complete preconditions)"

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

/-- Check level: how much information to gather and display -/
inductive CheckLevel where
  | minimal         -- One check, simple messages (pass/fail/unknown)
  | minimalVerbose  -- One check, detailed messages (always true if reached, etc.)
  | full            -- Both checks, detailed messages (all 9 outcomes)
  deriving Repr, DecidableEq

instance : Inhabited CheckLevel where
  default := .minimal

def CheckLevel.ofString? (s : String) : Option CheckLevel :=
  match s with
  | "minimal" => some .minimal
  | "minimalVerbose" => some .minimalVerbose
  | "full" => some .full
  | _ => none

def CheckLevel.options : String :=
  "'minimal' (simple messages), 'minimalVerbose' (detailed messages, one check), or 'full' (both checks, all outcomes)"

structure VerifyOptions where
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
  checkLevel : CheckLevel

def VerifyOptions.default : VerifyOptions := {
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
  checkLevel := .minimal
}

instance : Inhabited VerifyOptions where
  default := .default

def VerifyOptions.quiet : VerifyOptions :=
  { VerifyOptions.default with verbose := .quiet }

def VerifyOptions.models : VerifyOptions :=
  { VerifyOptions.default with verbose := .models }

def VerifyOptions.debug : VerifyOptions :=
  { VerifyOptions.default with verbose := .debug }

end Core
end
