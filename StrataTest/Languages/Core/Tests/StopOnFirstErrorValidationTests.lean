/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core
meta import Strata.Languages.Core.DDMTransform.Translate
meta import StrataDDM.Elab
meta import StrataDDM.BuiltinDialects.Init
import StrataDDM.Integration.Lean.HashCommands

meta section

/-! # Stopping at the first error

A back end returns the solver's and the evaluator's answers before any phase validates their
models; `verifyPipeline` validates them afterwards. Under `stopOnFirstError`, the back end stops at
the first obligation its own answer does not prove, and reports every obligation after it as not
checked, naming where it stopped, so each obligation has a result.

Each procedure below asserts `false` with nothing assumed, which the evaluator refutes without a
solver (the evaluator traces each refutation it finds, before any phase reads it). A phase that
rejects every model of `a` demotes `a`'s refutation to unknown. The run stops at `a`, its answer
being a refutation, so `b` and `c` are not checked. -/

namespace StopOnFirstErrorValidationTests

open Core Strata

private def parse (p : StrataDDM.Program) : Core.Program :=
  (TransM.run Inhabited.default (translateProgram p)).fst

private def threeRefutations :=
#strata
program Core;

procedure A()
{
  assert [a]: false;
};

procedure B()
{
  assert [b]: false;
};

procedure C()
{
  assert [c]: false;
};
#end

/-- A phase that rejects every model of the obligation labeled `a` and preserves the others. -/
private def rejectsA : AbstractedPhase :=
  { name := "rejectsA",
    getValidation := fun ob =>
      if ob.label == "a" then .modelToValidate (fun _ _ => none) else .modelPreserving }

/-- Each result's label and outcome, as `Core.verify` reports it. -/
private def run (options : VerifyOptions) : IO Unit := do
  IO.FS.withTempDir fun dir => do
    match ← (Core.verify (parse threeRefutations) dir options
        (externalPhases := [rejectsA])).toBaseIO with
    | .ok rs => for r in rs do IO.println s!"{r.obligation.label}: {r.formatOutcome}"
    | .error e => IO.println s!"error: {e.message}"

/--
info:

Obligation a: failed!

Result obtained during evaluation.
a: ❓ unknown
b: ❓ not checked: the run stopped after a
c: ❓ not checked: the run stopped after a
-/
#guard_msgs in
#eval run { VerifyOptions.quiet with stopOnFirstError := true }

/-! Without `stopOnFirstError`, all three are checked. -/

/--
info:

Obligation a: failed!

Result obtained during evaluation.


Obligation b: failed!

Result obtained during evaluation.


Obligation c: failed!

Result obtained during evaluation.
a: ❓ unknown
b: ❌ fail
c: ❌ fail
-/
#guard_msgs in
#eval run VerifyOptions.quiet

/-! A line that merges a not-checked piece keeps the reason when that piece is why the line is
undecided, and drops it once a checked piece decides the line. -/

private def obA : Imperative.ProofObligation Expression :=
  { label := "a", property := .assert, assumptions := [],
    obligation := .true (ExprSourceLoc.synthesized "test"), metadata := {} }

private def notCheckedA : VCResult := VCResult.ofNotChecked obA VerifyOptions.quiet (some "b")

private def refutedOutcome : VCOutcome :=
  { satisfiabilityProperty := .unknown none, validityProperty := .sat [] }

private def refutedA : VCResult := { obligation := obA, outcome := .ok refutedOutcome }

#guard (notCheckedA.merge notCheckedA).notChecked == some "the run stopped after b"
#guard (notCheckedA.merge refutedA).notChecked == none
#guard (refutedA.merge notCheckedA).notChecked == none

/-! With a piece that passed, the line is undecided only because the other piece was not checked,
so it keeps the reason; with a piece checked and left unknown, it reads a plain unknown. -/

private def provedA : VCResult :=
  { obligation := obA,
    outcome := .ok { satisfiabilityProperty := .unknown none, validityProperty := .unsat } }

private def unknownA : VCResult :=
  { obligation := obA,
    outcome := .ok { satisfiabilityProperty := .unknown none, validityProperty := .unknown none } }

#guard (provedA.merge notCheckedA).notChecked == some "the run stopped after b"
#guard (unknownA.merge notCheckedA).notChecked == none
#guard (notCheckedA.merge unknownA).notChecked == none

/-! A cover a checked path already satisfies is decided, so the merged line drops the reason. -/

private def obK : Imperative.ProofObligation Expression := { obA with property := .cover }

private def coverSat : VCResult :=
  { obligation := obK,
    outcome := .ok { satisfiabilityProperty := .sat [], validityProperty := .unsat } }

private def coverNotChecked : VCResult := VCResult.ofNotChecked obK VerifyOptions.quiet (some "b")

#guard (coverSat.merge coverNotChecked).notChecked == none
#guard (coverNotChecked.merge coverSat).notChecked == none
#guard (coverNotChecked.merge coverNotChecked).notChecked == some "the run stopped after b"

/-! A goal not checked is reported as a warning, neither a failed assertion nor an error. -/

#guard match toMessage notCheckedA with
  | some m => m.kind == .warning && m.message == "not checked: the run stopped after b"
  | none => false

/-! A cover a path satisfies does not stop the run: the asserts after it are checked. -/

private def coverThenAsserts :=
#strata
program Core;
procedure K(x : int) { cover [k]: x == 5; };
procedure B(y : int) { assert [b]: y == 5; };
procedure C(z : int) { assert [c]: z == 5; };
#end

/--
info: k: ✅ pass
b: ❌ fail
c: ❓ not checked: the run stopped after b
-/
#guard_msgs in
#eval show IO Unit from do
  IO.FS.withTempDir fun dir => do
    match ← (Core.verify (parse coverThenAsserts) dir
        { VerifyOptions.quiet with stopOnFirstError := true }).toBaseIO with
    | .ok rs => for r in rs do IO.println s!"{r.obligation.label}: {r.formatOutcome}"
    | .error e => IO.println s!"error: {e.message}"

end StopOnFirstErrorValidationTests

end
