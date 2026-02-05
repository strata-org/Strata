/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public inductive VerboseMode where
  | quiet
  | normal
  | debug
  deriving Inhabited, Repr, DecidableEq

public def VerboseMode.toNat (v : VerboseMode) : Nat :=
  match v with
  | .quiet => 0
  | .normal => 1
  | .debug => 2

public def VerboseMode.ofBool (b : Bool) : VerboseMode :=
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

public structure Options where
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

public def Options.default : Options := {
  verbose := .normal,
  parseOnly := false,
  typeCheckOnly := false,
  checkOnly := false,
  stopOnFirstError := false,
  removeIrrelevantAxioms := false,
  solverTimeout := 10,
  outputSarif := false
}

instance : Inhabited Options where
  default := .default

public def Options.quiet : Options :=
  { Options.default with verbose := .quiet }

public def Options.debug : Options :=
  { Options.default with verbose := .debug }
