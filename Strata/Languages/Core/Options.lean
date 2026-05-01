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

def VerificationMode.toString : VerificationMode → String
  | .deductive => "deductive"
  | .bugFinding => "bugFinding"
  | .bugFindingAssumingCompleteSpec => "bugFindingAssumingCompleteSpec"

instance : ToString VerificationMode := ⟨VerificationMode.toString⟩

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

/--
Control how aggressively irrelevant axioms are pruned from proof obligations.

Axiom removal is **sound for assert obligations**: removing axioms can only
weaken the proof context, so a valid goal remains valid and an invalid goal
cannot become falsely provable. However, valid goals may become **unprovable**
(the solver returns `unknown` instead of `pass`).

Axiom removal is **unsound for cover obligations**: removing axioms weakens
path conditions, potentially making unreachable paths appear satisfiable
and producing spurious "covered" results. Cover obligations always skip
axiom pruning regardless of this setting.

Future improvement: trigger-based pruning could make relevance analysis
more precise by using quantifier triggers to determine which functions
can actually instantiate an axiom (see Boogie PR #427).
-/
inductive IrrelevantAxiomsMode where
  | Off        -- No axiom pruning (default)
  | Aggressive -- Only consequent Q functions used for relevance
  | Precise    -- Both antecedent P and consequent Q functions used
  deriving Repr, DecidableEq, Inhabited

/-- Check level: how much information to gather and display -/
inductive CheckLevel where
  | minimal         -- One check, simple messages (pass/fail/unknown)
  | minimalVerbose  -- One check, detailed messages (always true if reached, etc.)
  | full            -- Both checks, detailed messages (all 9 outcomes)
  deriving Repr, DecidableEq

instance : Inhabited CheckLevel where
  default := .minimal

/-- Configuration for which arithmetic overflow checks to enable.
    Defaults match C/IEEE 754 semantics: signed BV overflow is UB (checked),
    unsigned BV wraps (unchecked), float64 overflows to ±∞ (unchecked). -/
structure OverflowChecks where
  /-- Check signed bitvector overflow (undefined behavior in C). -/
  signedBV   : Bool := true
  /-- Check unsigned bitvector overflow (defined wrapping in C). -/
  unsignedBV : Bool := false
  /-- Check float64 overflow to ±∞ (defined in IEEE 754). -/
  float64    : Bool := false
  deriving Repr, Inhabited

def CheckLevel.ofString? (s : String) : Option CheckLevel :=
  match s with
  | "minimal" => some .minimal
  | "minimalVerbose" => some .minimalVerbose
  | "full" => some .full
  | _ => none

def CheckLevel.options : String :=
  "'minimal' (simple messages), 'minimalVerbose' (detailed messages, one check), or 'full' (both checks, all outcomes)"

/-- Options controlling the verification pipeline.
    When adding or removing fields, keep `verifyOptionsFlags` and
    `parseVerifyOptions` in StrataMain.lean in sync. -/
structure VerifyOptions where
  -- Pipeline stopping points
  /-- How much diagnostic output to emit. -/
  verbose : VerboseMode
  /-- Exit after DDM parsing and type checking (no semantic analysis). -/
  parseOnly : Bool
  /-- Exit after the semantic dialect's type inference/checking. -/
  typeCheckOnly : Bool
  /-- Stop after type-checking; do not generate VCs or invoke the solver. -/
  checkOnly : Bool
  /-- Write SMT-Lib files but do not invoke the solver.
      Requires `vcDirectory` to be set so the files are preserved. -/
  skipSolver : Bool
  -- Solver configuration
  /-- SMT solver executable to use. -/
  solver : String
  /-- Solver time limit in seconds. -/
  solverTimeout : Nat
  /-- Directory to store generated SMT-Lib (`.smt2`) files. -/
  vcDirectory : Option System.FilePath
  /-- Always generate SMT-Lib files, even if the verification
      condition is trivial (i.e. resolved by symbolic evaluation
      without needing the solver). -/
  alwaysGenerateSMT : Bool
  -- Encoding options
  /-- Use globally unique `$__bv{N}` names for quantifier-bound
      variables instead of human-readable names derived from
      user-provided names. -/
  uniqueBoundNames : Bool
  /-- Use SMT-LIB Array theory instead of axiomatized maps. -/
  useArrayTheory : Bool
  -- Verification behavior
  /-- Exit after the first verification error instead of
      continuing. -/
  stopOnFirstError : Bool
  /-- How aggressively to prune irrelevant axioms from proof
      obligations. See `IrrelevantAxiomsMode` for details. -/
  removeIrrelevantAxioms : IrrelevantAxiomsMode
  /-- Verification mode: deductive (prove correctness) or
      bugFinding (find bugs). -/
  checkMode : VerificationMode
  /-- How many checks to run per VC and how detailed the
      messages should be. -/
  checkLevel : CheckLevel
  /-- Overflow check configuration: which arithmetic overflow checks to enable. -/
  overflowChecks : OverflowChecks := {}
  /-- Maximum number of continuing symbolic-evaluation paths allowed
      between statements. When the combined path count from all input
      paths exceeds this cap after a statement, the evaluator merges
      paths down to the cap using splitId matching on `splitConds`
      and `Env.merge`.
      `none` (default) means no cap — paths diverge freely.
      `some 1` is eager merging; `some N` allows bounded exploration.

      The evaluator processes statements in batch: all active paths
      evaluate the current statement, the results are combined, merged
      down to the cap, and then all proceed to the next statement
      together. This bounds both the total path count and the
      evaluation work. Paths with active exit labels are left
      untouched — they skip remaining statements and accumulate at
      most linearly. -/
  pathCap : Option Nat := .none
  -- Output
  /-- Output results in SARIF format. -/
  outputSarif : Bool
  /-- Print elapsed time for each verification sub-step. -/
  profile : Bool

def VerifyOptions.default : VerifyOptions := {
  verbose := .normal,
  parseOnly := false,
  typeCheckOnly := false,
  checkOnly := false,
  stopOnFirstError := false,
  removeIrrelevantAxioms := .Off,
  useArrayTheory := false,
  solverTimeout := 10,
  outputSarif := false,
  solver := defaultSolver
  vcDirectory := .none
  checkMode := .deductive
  checkLevel := .minimal
  alwaysGenerateSMT := false
  uniqueBoundNames := false
  skipSolver := false
  profile := false
  pathCap := .none
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
