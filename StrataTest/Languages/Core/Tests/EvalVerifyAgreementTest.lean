/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public meta import Strata.Languages.Core.DDMTransform.ASTtoCST
public meta import Strata.Languages.Core.InterpreterEval
public meta import Strata.Languages.Core.DDMTransform.Translate
public meta import StrataTest.Languages.Core.Tests.RandomPrograms
import StrataDDM.Integration.Lean.HashCommands

/-! # Core's concrete interpreter agrees with `Core.verify` on random programs

If `Core.verify` proves an assertion, no run of the program may find it false. This file
checks that on random programs (`RandomPrograms.lean`): it verifies each program, runs each
of its procedures under `EvalM` (Core's concrete interpreter, `InterpreterEval.lean`) on
random inputs, and reports a problem when a run finds false an assertion that the verifier
proved, or one for which it produced no obligation.

Core does not assume an assertion after checking it (of `assert [a]: x > 0; assert [b]:
x > 0;`, both are refuted), so a run continues past a false assertion, and every assertion
it finds false must not be proved. A run stops at a false `assume`. It resolves each
nondeterministic choice (a declaration without a value, `havoc`, `if *`) to the type's
default value, which is still one of the program's executions.

The check also reports a program that does not type-check, a verification that throws,
an obligation with an error, and a run that `EvalM` cannot finish (an expression that does
not evaluate). On this fragment, which both cover, each is a bug in the generator or in
Core.

A program with a problem is shrunk (`RandomPrograms.shrinks`) as long as it still has a
problem of the same kind on the same inputs, and printed with its seed. Program `n` is
`generate n`, and the inputs of its procedures depend only on `n`, the procedure's name and
the run's number, so `checkSeeds n 1` reproduces it. The tests at the end check 40 seeds and
two fixed programs; for a longer run, evaluate, for example,
`checkSeeds 1000 1000 (verbose := true)` in a file that imports this one. -/

meta section
open Strata

namespace Core.EvalVerifyAgreementTest

open Core.RandomPrograms (generate shrinks)
open Lambda (LMonoTy)

/-! ## The verifier's side -/

/-- What `Core.verify` concludes about an assertion. -/
inductive Verdict where
  | proved
  | refuted
  | unknown
  /-- An obligation of the assertion has an encoding error, a solver crash, or a solver
      error in one of its checks. -/
  | error (msg : String)
  deriving BEq, Inhabited

/-- The verdict on an assertion with obligations `rs`: proved when every obligation passes,
    refuted when one fails, otherwise unknown; an obligation with an encoding error, a solver
    crash, or a solver error in one of its checks makes it an error, as for the command line's
    exit code. A solver timeout is not an error (it happens on a loaded machine); it makes the
    verdict unknown, which the check never reports. -/
def Verdict.ofResults (rs : List Core.VCResult) : Verdict :=
  match rs.find? (fun r => r.isImplementationError || r.hasSMTError) with
  | some r => .error r.formatOutcome
  | none =>
    if rs.all (·.isSuccess) then .proved
    else if rs.any (·.isFailure) then .refuted
    else .unknown

/-- An obligation of an assertion `a` whose solver call ended with `error`. -/
def failedWith (error : Core.VCError) : Core.VCResult :=
  { obligation := { label := "a", property := .assert, assumptions := [],
                    obligation := .boolConst valueLoc true, metadata := .empty },
    outcome := .error error }

#guard Verdict.ofResults [failedWith (.solverTimeout "")] == .unknown
#guard Verdict.ofResults [failedWith (.solverCrash "")] matches .error _
#guard Verdict.ofResults [failedWith (.encoding "")] matches .error _

/-- An obligation of an assertion `a` whose solver calls answered `outcome`. -/
def answered (outcome : Core.VCOutcome) : Core.VCResult :=
  { failedWith (.solverTimeout "") with outcome := .ok outcome }

#guard Verdict.ofResults [answered { satisfiabilityProperty := .unknown,
                                     validityProperty := .err "" }] matches .error _

/-- The verdict of `Core.verify` on each assertion label of `program`. The verifier's own
    output is dropped. -/
def verdicts (program : Core.Program) : IO (Except String (Std.HashMap String Verdict)) := do
  let options := { Core.VerifyOptions.quiet with solver := "cvc5" }
  let (_, results) ← IO.FS.withIsolatedStreams (isolateStderr := true)
    (Strata.Core.verifyProgram program options).toBaseIO
  match results with
  | .error e => return .error e
  | .ok results =>
    let byLabel := results.toList.foldl (init := ({} : Std.HashMap String (List Core.VCResult)))
      fun m r => m.alter r.obligation.label fun rs => some (r :: rs.getD [])
    return .ok (byLabel.map fun _ rs => Verdict.ofResults rs)

/-! ## The interpreter's side -/

/-- How a concrete run ends. -/
inductive RunEnd where
  /-- At the end of the body. -/
  | done
  /-- At a false `assume`. -/
  | blocked
  /-- Before the end, for another reason: `EvalM` could not run the body. -/
  | stuck (why : String)

/-- Run the body of `proc` under `EvalM` from the store `inputs`, past false assertions and
    up to the first false `assume`. Return the labels of the assertions found false, in the
    order the run reached them, and how the run ended. -/
def runConcrete (proc : Core.Procedure) (inputs : List (String × Expression.Expr)) :
    List String × RunEnd :=
  match proc.body with
  | .structured body _ =>
    let env := Imperative.IEnv.ofStore (fun (x : CoreIdent) => inputs.lookup x.name) Core.Factory
    let opts : EvalOpts := { fuel := 10000, assertPolicy := .collect, assumePolicy := .enforce }
    let (result, state) := runCoreEvalWith (fun _ => none) opts 10000 (.stmts body env)
    let failed := state.assertFailures.reverse.map (·.1)
    match result with
    | .ok _ => (failed, .done)
    | .error (.stuck (.assumptionFalseUnderReplay _)) => (failed, .blocked)
    | .error h => (failed, .stuck h.describe)
  | _ => ([], .stuck "the body is not structured")

/-- Random values for `params` (`RandomPrograms.value`), the same for the same `seed`:
    integers mostly between `-3` and `3`, Booleans either way; an error for a parameter of
    another type. -/
def inputs (seed : Nat) (params : List (CoreIdent × LMonoTy)) :
    Except String (List (String × Expression.Expr)) :=
  let gen : RandomPrograms.GenM (Except String (List (String × Expression.Expr))) := do
    let mut values := #[]
    for (x, ty) in params do
      let some value := RandomPrograms.value ty
        | return .error s!"no random value of type {ty} for parameter {x.name}"
      values := values.push (x.name, ← value)
    return .ok values.toList
  (gen.run (.ofSeed seed)).1

/-- `inputs` as `a = 1, b = true`. -/
def showInputs (inputs : List (String × Expression.Expr)) : String :=
  ", ".intercalate (inputs.map fun (x, v) => s!"{x} = {Core.formatExprs [v]}")

/-! ## The check -/

/-- What the check found wrong with a program. -/
structure Problem where
  /-- What went wrong, the same for a program and its shrunk versions. -/
  kind : String
  /-- The procedure, inputs and assertion involved, or an error message. -/
  detail : String

/-- Counts over the programs checked. -/
public structure Stats where
  programs : Nat := 0
  assertions : Nat := 0
  proved : Nat := 0
  refuted : Nat := 0
  unknown : Nat := 0
  runs : Nat := 0
  /-- Runs that found an assertion false. -/
  failing : Nat := 0
  /-- Runs that stopped at a false `assume`. -/
  blocked : Nat := 0
  problems : Nat := 0

/-- Check `program`, of seed `seed`: verify it, then run each procedure on `runs` random
    inputs, and return the first problem, if any, with the counts. The check stops at that
    problem, so for a program with a problem the counts cover only what came before it. -/
def check (seed : Nat) (program : Program) (runs : Nat) : IO (Stats × Option Problem) := do
  let stats : Stats := { programs := 1 }
  if let .error e := Core.typeCheck .quiet program then
    return (stats, some ⟨"does not type-check", e.message⟩)
  match ← verdicts program with
  | .error e => return (stats, some ⟨"verification throws", e⟩)
  | .ok vs =>
  let number (v : Verdict) : Nat := vs.fold (fun n _ w => if w == v then n + 1 else n) 0
  let mut stats : Stats := { stats with
    assertions := vs.size, proved := number .proved, refuted := number .refuted,
    unknown := number .unknown }
  for (l, v) in vs do
    if let .error msg := v then
      return (stats, some ⟨"an obligation has an error", s!"assertion {l}: {msg}"⟩)
  for d in program.decls do
    let .proc proc _ := d | continue
    for j in [0:runs] do
      let ins ← match inputs (hash (seed, proc.header.name.name, j)).toNat proc.header.inputs with
        | .ok ins => pure ins
        | .error e => return (stats, some ⟨"no inputs", s!"{proc.header.name.name}: {e}"⟩)
      stats := { stats with runs := stats.runs + 1 }
      let site := s!"{proc.header.name.name}({showInputs ins})"
      let (failed, ending) := runConcrete proc ins
      match ending with
      | .done => pure ()
      | .blocked => stats := { stats with blocked := stats.blocked + 1 }
      | .stuck why => return (stats, some ⟨"EvalM is stuck", s!"{site}: {why}"⟩)
      unless failed.isEmpty do stats := { stats with failing := stats.failing + 1 }
      for l in failed do
        match vs[l]? with
        | some .proved =>
          return (stats, some ⟨"proved but fails", s!"assertion {l} fails on {site}"⟩)
        | none =>
          return (stats, some ⟨"fails without an obligation", s!"assertion {l} fails on {site}"⟩)
        | some _ => pure ()
  return (stats, none)

/-- Shrink `prog`, which has `problem`, greedily: replace it by the first program one step
    smaller that has a problem of the same kind, at most `fuel` times. Return the smallest
    program and its problem. -/
def shrink (seed runs : Nat) (prog : Program) (problem : Problem) :
    (fuel : Nat) → IO (Program × Problem)
  | 0 => return (prog, problem)
  | fuel + 1 => do
    for q in shrinks prog do
      if let (_, some p) ← check seed q runs then
        if p.kind == problem.kind then return ← shrink seed runs q p fuel
    return (prog, problem)

/-- The sums of the counts of `s` and `t`. -/
def Stats.add (s t : Stats) : Stats where
  programs := s.programs + t.programs
  assertions := s.assertions + t.assertions
  proved := s.proved + t.proved
  refuted := s.refuted + t.refuted
  unknown := s.unknown + t.unknown
  runs := s.runs + t.runs
  failing := s.failing + t.failing
  blocked := s.blocked + t.blocked
  problems := s.problems + t.problems

/-- Check the programs of seeds `first`, …, `first + count - 1`, each procedure on `runs`
    random inputs. Print a line and the shrunk program for each problem, then the number
    of programs with a problem, or, with `verbose`, all the counts. -/
public def checkSeeds (first count : Nat) (runs : Nat := 10) (verbose : Bool := false) :
    IO Stats := do
  let mut total : Stats := {}
  for seed in [first:first + count] do
    let prog := generate seed
    let (s, problem) ← check seed prog runs
    total := total.add s
    if let some p := problem then
      total := { total with problems := total.problems + 1 }
      -- Each step makes the printed program shorter, so its length bounds the steps.
      let (small, p) ← shrink seed runs prog p (toString (Strata.Core.formatProgram prog)).length
      IO.println s!"seed {seed}: {p.kind}: {p.detail}"
      IO.println (Strata.Core.formatProgram small)
      (← IO.getStdout).flush
  if verbose then
    IO.println s!"programs {total.programs}, assertions {total.assertions} (proved \
      {total.proved}, refuted {total.refuted}, unknown {total.unknown}), runs {total.runs} \
      (finding an assertion false {total.failing}, stopped by a false assume {total.blocked})"
  let programs := if total.programs == 1 then "1 program" else s!"{total.programs} programs"
  IO.println s!"{programs}, {total.problems} with a problem"
  return total

/-! ## The test

Seeds 0 to 39: 40 programs, 269 assertions (144 proved, 125 refuted), 700 runs, of which 291
find an assertion false. The test also fails when the check is vacuous: when it checks no
assertion or makes no run, or when fewer than a quarter of the assertions are proved, or
refuted, or fewer than a quarter of the runs find an assertion false. -/

/-- info: 40 programs, 0 with a problem -/
#guard_msgs in
#eval do
  let s ← checkSeeds 0 40
  unless 0 < s.assertions && 0 < s.runs && 4 * s.proved ≥ s.assertions &&
      4 * s.refuted ≥ s.assertions && 4 * s.failing ≥ s.runs do
    throw (IO.userError s!"vacuous: {s.proved} proved and {s.refuted} refuted of \
      {s.assertions} assertions, {s.failing} of {s.runs} runs find one false")

/-- Check `program`, each procedure on 10 inputs drawn from `seed`, and print its problem,
    unshrunk, or that it has none, with the counts that show what was checked. -/
def checkProgram (seed : Nat) (program : Program) : IO Unit := do
  match ← check seed program 10 with
  | (_, some p) => IO.println s!"{p.kind}: {p.detail}"
  | (s, none) => IO.println s!"no problem; assertions: {s.assertions} ({s.proved} proved), \
      runs: {s.runs} ({s.failing} finding an assertion false)"

/-- Translate `p` into a Core program, or the empty program if translation reports an
    error (the counts that the test prints then show it). -/
def translate (p : StrataDDM.Program) : Program :=
  match TransM.run Inhabited.default (translateProgram p) with
  | (program, #[]) => program
  | _ => { decls := [] }

/-- The shape of the soundness bug fixed by `3a949942`: an `assume false` and an `exit` out of
    a block in one procedure, and a false assertion in the next. With that fix undone, `a3` is
    proved, and it is false whenever `b ≥ 1`. -/
def exitAfterAssumeFalseParsed : StrataDDM.Program :=
#strata
program Core;
procedure p1 (a : int, b : int)
{
  L2: {
    assume [assume_1]: false;
    if (!(int.mul(int.neg(2), 2) == int.add(a, b))) {
      exit L2;
    }
  }
};
procedure p2 (a : int, b : int)
{
  assert [a3]: int.gt(int.sub(3, b), int.add(b, b));
};
#end

/-- `exitAfterAssumeFalseParsed` as a Core program. -/
def exitAfterAssumeFalse : Program := translate exitAfterAssumeFalseParsed

/-- The shape of the soundness bug fixed by `f5540d7d`: a folded `if` whose live arm declares a
    name that is declared again after it. With that fix undone, verification throws. -/
def foldedIfRedeclaresParsed : StrataDDM.Program :=
#strata
program Core;
procedure p1 (a : int, b : int, c : int)
{
  if (false) {
  } else {
    var w : int := int.mul(int.sub(a, b), 0);
  }
  var w : bool := if true then int.lt(int.neg(2), c) else if true then true else true;
};
#end

/-- `foldedIfRedeclaresParsed` as a Core program. -/
def foldedIfRedeclares : Program := translate foldedIfRedeclaresParsed

/-- info: no problem; assertions: 1 (0 proved), runs: 20 (5 finding an assertion false)
no problem; assertions: 0 (0 proved), runs: 10 (0 finding an assertion false) -/
#guard_msgs in
#eval do
  checkProgram 314 exitAfterAssumeFalse
  checkProgram 604 foldedIfRedeclares

end Core.EvalVerifyAgreementTest

end
