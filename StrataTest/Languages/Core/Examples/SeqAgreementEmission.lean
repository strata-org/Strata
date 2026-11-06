/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public meta import Strata.Languages.Core
meta import Strata.Languages.Core.DDMTransform.Translate
public import StrataDDM.Integration.Lean.HashCommands

meta section

/-! # When the sequence agreement axiom reaches the solver

The axiom stating that `Sequence.select!` equals `Sequence.select` in range belongs
to `Sequence.select`, and the encoder sends a function's axioms only for a query
that uses that function. A query written with `select!` alone therefore carries no
agreement axiom, while a query that uses both selectors carries it. Each program
below prints, for its one query, how many asserted formulas mention both
selectors. -/

namespace Core.SeqAgreementEmission.Tests

/-- The `assert` commands of the queries written for `pgm`, each joined into one line. -/
private def asserts (pgm : StrataDDM.Program) : IO (List String) := do
  let vcDir : System.FilePath := "_test_vcs_seq_agreement_emission"
  if ← vcDir.pathExists then
    IO.FS.removeDirAll vcDir
  IO.FS.createDirAll vcDir
  let _ ← Strata.Core.verify pgm (options := { Core.VerifyOptions.quiet with
    skipSolver := true, vcDirectory := vcDir, alwaysGenerateSMT := true })
  let mut out := []
  for e in ← vcDir.readDir do
    if e.fileName.endsWith ".smt2" then
      let mut current : Option String := none
      for line in (← IO.FS.readFile e.path).splitOn "\n" do
        if line.startsWith "(" then
          if let some a := current then out := a :: out
          current := if line.startsWith "(assert" then some line else none
        else
          current := current.map (· ++ line)
      if let some a := current then out := a :: out
  IO.FS.removeDirAll vcDir
  return out.reverse

private def mentions (a op : String) : Bool := (a.splitOn op).length > 1

/-- The number of asserted formulas, in the queries written for `pgm`, that mention
    both `Sequence.select!` and `Sequence.select`. -/
private def agreementAsserts (pgm : StrataDDM.Program) : IO Unit := do
  let n := (← asserts pgm).filter (fun a =>
    mentions a "Sequence.select!" && mentions a "Sequence.select#") |>.length
  IO.println s!"agreement asserts: {n}"

/-- The number of quantified asserted formulas, in the queries written for `pgm`: in
    total, those that mention an unchecked sequence operation, and among the latter
    those whose trigger mentions one. -/
private def quantifiedAsserts (pgm : StrataDDM.Program) : IO Unit := do
  let qs := (← asserts pgm).filter (mentions · "(forall")
  let unchecked := ["update!", "take!", "drop!", "select!"]
  let bang := qs.filter (fun a => unchecked.any (mentions a))
  let pattern (a : String) : String := ((a.splitOn ":pattern").drop 1).foldl (· ++ ·) ""
  let inert := bang.filter (fun a => unchecked.any (mentions (pattern a)))
  IO.println s!"quantified asserts: {qs.length}, mentioning an unchecked operation: \
    {bang.length}, of those triggered on an unchecked operation: {inert.length}"

/-- Only `select!` appears: the agreement axiom is not sent. -/
def uncheckedOnlyPgm : StrataDDM.Program :=
#strata
program Core;

const s : Sequence int;
axiom [len]: Sequence.length(s) == 1;
axiom [e0]: Sequence.select!(s, 0) == 1;

procedure P()
{
  assert [a]: int.gt(Sequence.select!(s, 0), 0);
};
#end

/-- info: agreement asserts: 0 -/
#guard_msgs in
#eval agreementAsserts uncheckedOnlyPgm

/-- Both selectors appear: the agreement axiom is sent. -/
def bothSelectorsPgm : StrataDDM.Program :=
#strata
program Core;

const s : Sequence int;
axiom [len]: Sequence.length(s) == 1;
axiom [e0]: Sequence.select!(s, 0) == 1;

procedure P()
{
  assert [a]: int.gt(Sequence.select(s, 0), 0);
};
#end

/-- info: agreement asserts: 1 -/
#guard_msgs in
#eval agreementAsserts bothSelectorsPgm

/-- Only checked operations appear. The query receives the agreement axiom of
`Sequence.select`, which mentions `Sequence.select!`; the other quantified formulas
that mention an unchecked operation are the `select!` copies of the select-of-update
and select-of-take axioms, already present without the agreement axiom. All of them
are triggered on an unchecked term, which this query does not contain, so they never
fire here. The counts pin both the axiom set and those triggers. -/
def checkedOnlyPgm : StrataDDM.Program :=
#strata
program Core;

const s : Sequence int;
axiom [len]: Sequence.length(s) == 3;

procedure P()
{
  assert [a]: Sequence.select(Sequence.take(Sequence.update(s, 0, 5), 2), 0) == 5;
};
#end

/-- info: quantified asserts: 28, mentioning an unchecked operation: 11, of those triggered on an unchecked operation: 11 -/
#guard_msgs in
#eval quantifiedAsserts checkedOnlyPgm

end Core.SeqAgreementEmission.Tests

end
