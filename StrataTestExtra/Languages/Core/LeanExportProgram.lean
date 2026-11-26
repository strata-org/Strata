/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
import Strata.Languages.Core
import StrataTest.Util.LeanExport
import Strata.Cli.VerifyOptions
import StrataLaurel.Tests.Util.TestLaurel

/-! # The Lean export through the verifier's entry points

`VerifyOptions.leanExport` reaches the export from `Strata.Core.verify` on the per-obligation
path and on the incremental backend (checks sent alone and checks walked on a shared session),
from Laurel, from a custom discharge function, and from the flags of the compiled executable.

The export adds files and changes nothing else. What each block compares:

- The blocks that verify through the library run every verification twice, without the export
  and with it, and compare the results field by field (`fingerprint`) and what is printed.
  With the solver stand-in they also pin the number of checks the solver answers in each of
  the two runs; with a custom discharge function, the number of calls.
- The blocks that run the executable compare the exit code and standard output with those of
  a run without the flags. The block that runs the examples also pins that baseline to what
  cvc5 decides, and compares standard error.
- An export that repeats another one (two workers instead of one, the per-obligation path
  instead of the walk) has no baseline of its own: its files are compared with the other's.

Wherever files are expected, the directory holds exactly those files and nothing else.
-/

open Lean Strata.SMT.LeanExport Core.LeanExport Core.LeanExport.Tests

private def validProgram :=
#strata
program Core;
procedure P(x : int, y : int) {
  assert [first]: int.gt(int.add(x, 1), x);
  assert [second]: int.gt(int.add(y, 1), y);
};
#end

/-- Two assertions cvc5 refutes, each with a counterexample. -/
private def refutedProgram :=
#strata
program Core;
procedure P(x : int) {
  assert [low]: int.gt(x, 5);
  assert [high]: int.lt(x, 7);
};
#end

/-- Two checks in each arm of a branch, under an assumption of the arm: 111 occurs only in
the queries of the first arm, 222 only in those of the second. -/
private def twoArmProgram :=
#strata
program Core;
procedure P(x : int, y : int) {
  if (int.gt(x, 0)) {
    assume [large]: int.gt(y, 111);
    assert [thenSum]: int.gt(int.add(x, y), 1);
    assert [thenBound]: int.gt(y, 1);
  } else {
    assume [small]: int.lt(y, 222);
    assert [elseSum]: int.lt(int.add(x, y), 333);
    assert [elseBound]: int.lt(y, 333);
  }
};
#end

/-- A cover, a check whose query has a string literal SMT-LIB cannot spell (U+E0001), so that
its encoding fails, and an ordinary check. -/
private def notExportedProgram :=
#strata
program Core;
function f (s : string) : int;
procedure P(x : int) {
  cover [reachable]: int.gt(x, 0);
  assert [unencodable]: f("a󠀁b") == 1;
  assert [plain]: int.gt(int.add(x, 1), x);
};
#end

/-- A check Strata decides by evaluation. -/
private def decidedProgram :=
#strata
program Core;
procedure P(x : int) {
  assert [decided]: true;
};
#end

private def laurelProgram :=
#strata
program Laurel;
procedure P(x: int, y: int) opaque {
  assert x + 1 > x;
  assert y + 1 > y
};
#end

open Lean Elab Term in
/-- The package root as an absolute path, three directories above this file's: the tests
find the executable, the examples and the solver stand-in there, whatever directory they are
run from. -/
elab "package_root%" : term => do
  let file ← IO.FS.realPath (← getFileName)
  let some root := file.parent.bind (·.parent) |>.bind (·.parent) |>.bind (·.parent)
    | throwError "{file} is not three directories below the package root"
  unless ← (root / "lakefile.toml").pathExists do
    throwError "{root}, three directories above {file}, is not the package root"
  return toExpr root.toString

private def packageRoot : System.FilePath := package_root%

/-- The names of the exported files of a directory, sorted; none when it does not exist. -/
private def entries (dir : System.FilePath) : IO (Array String) :=
  return (← leanFiles dir).map (·.fileName.getD "")

/-- The files of a directory with their contents, sorted by name. -/
private def contents (dir : System.FilePath) : IO (Array (String × String)) := do
  (← entries dir).mapM fun (name : String) => return (name, ← IO.FS.readFile (dir / name))

/-- Whether `name` is the name of the file exported for the check `label`: the label, with
`_` for every character other than a letter, a digit, `_`, `-` and `.`, then `_`, a hash of 16
hex digits and `.lean`. -/
private def isFileOf (label name : String) : Bool :=
  let stem := label.map fun c =>
    if c.isAlphanum || c == '_' || c == '-' || c == '.' then c else '_'
  name.startsWith s!"{stem}_" && name.endsWith ".lean" && name.length == stem.length + 22

/-- Fails unless `dir` holds exactly one exported file for each label of `expected` and
nothing else (no second file for a label, no staging file left behind), and each file names
its label and reports the solver's answer given with the label, alone or followed by an
explanation in parentheses. Returns the files, in the order of `expected`. -/
private def expectExported (dir : System.FilePath) (expected : List (String × String)) :
    IO (List System.FilePath) := do
  let names ← entries dir
  unless names.size == expected.length do
    throw <| IO.userError s!"{dir}: expected one file for each of {expected.map (·.1)}, \
      found {names}"
  expected.mapM fun (label, answer) => do
    let some name := names.find? (isFileOf label)
      | throw <| IO.userError s!"{dir}: no file for `{label}` among {names}"
    let lines := (← IO.FS.readFile (dir / name)).splitOn "\n"
    let answers := lines.filterMap fun line =>
      (line.dropPrefix? "-- Solver's answer: ").map (·.toString)
    unless lines.contains s!"-- Strata verification condition: {label}" &&
        answers.length == 1 &&
        answers.all (fun found => found == answer || found.startsWith s!"{answer} (") do
      throw <| IO.userError s!"{dir / name}: expected the label `{label}` and the answer \
        `{answer}`, found {lines.take 2}"
    return dir / name

/-- The two checks of `validProgram`, each with the answer `answer`. -/
private def both (answer : String) : List (String × String) :=
  [("first", answer), ("second", answer)]

/-- A configuration that writes to a fresh directory under `root`, with its events. -/
private def newConfig (root : System.FilePath) (name : String)
    (scope : Scope := .undecided) :
    IO (ExportConfig × System.FilePath × IO.Ref (Array Event)) := do
  let (config, events) ← recording (root / name) scope
  return (config, config.directory, events)

/-- Everything a result carries, as text: the obligation, the outcome with its solver log,
the counterexample, the names of the encoder state and the options it is printed with. The
printed form of a result leaves out the log, the state and, in a quiet run, the
counterexample. -/
private def fingerprint (result : Core.VCResult) : String :=
  let sorted (names : Array String) := names.qsort (· < ·)
  s!"{Core.formatProofObligation result.obligation}\n{reprStr result.outcome}\n\
    {Std.format result.lexprModel}\n\
    {sorted result.estate.usedNames.toArray} {sorted (result.estate.functions.toArray.map (·.2))}\n\
    {reprStr result.verbose} {reprStr result.checkLevel} {reprStr result.checkMode}"

private def sameResults (results baseline : Core.VCResults) : Bool :=
  results.map fingerprint == baseline.map fingerprint

/-- Runs `plain`, a verification without the export, and then `exporting`, the same with it.
Fails unless both give the same results, which it returns, and the calling thread prints the
same on stdout and stderr. What worker threads and the solver print goes past this capture;
the runs of the executable compare the output of the whole process. -/
private def unchangedByExport (plain exporting : IO Core.VCResults) : IO Core.VCResults := do
  let (baselineOutput, baseline) ← IO.FS.withIsolatedStreams (isolateStderr := true) plain
  let (output, results) ← IO.FS.withIsolatedStreams (isolateStderr := true) exporting
  unless sameResults results baseline do
    throw <| IO.userError s!"The Lean export changed the results: \
      {results.map fingerprint} instead of {baseline.map fingerprint}"
  unless output == baselineOutput do
    throw <| IO.userError s!"The Lean export changed the output: \
      {output} instead of {baselineOutput}"
  return results

/-- The solver stand-in `testdata/UndecidedSolver.py`, installed for a test. -/
private structure StandIn where
  /-- The command that starts it, for `VerifyOptions.solver` and `--solver`. -/
  solver : String
  /-- The number of checks it has answered since this action last ran. -/
  answered : IO Nat

/-- Installs the solver stand-in under `name` and runs `action` with it. The name selects the
stand-in's answers, which the header of the script lists; under the default name it answers
`unknown` to every check. -/
private def withSolver (action : StandIn → IO Unit) (name : String := "unknown-solver") :
    IO Unit :=
  IO.FS.withTempDir fun dir => do
    let script := dir / name
    let log := dir / "checks.log"
    let launcher := dir / "launch"
    IO.FS.writeFile script (← IO.FS.readFile
      (packageRoot / "StrataTestExtra/Languages/Core/testdata/UndecidedSolver.py"))
    -- Strata starts the solver with its own environment, so a launcher names the log.
    IO.FS.writeFile launcher
      s!"#!/bin/sh\nSTRATA_TEST_SOLVER_LOG='{log}' exec python3 '{script}' \"$@\"\n"
    IO.setAccessRights launcher { user := { read := true, execution := true } }
    action {
      solver := launcher.toString
      answered := do
        let answers ← if ← log.pathExists then IO.FS.readFile log else pure ""
        IO.FS.writeFile log ""
        return occurrences answers "\n" }

/-- Verifies `program` with `options`. Fails unless the stand-in answers `checks` checks. -/
private def StandIn.verify (standIn : StandIn) (checks : Nat) (options : Core.VerifyOptions)
    (program := validProgram) : IO Core.VCResults := do
  let results ← Strata.Core.verify program (options := options)
  let answered ← standIn.answered
  unless answered == checks do
    throw <| IO.userError s!"The solver answered {answered} checks instead of {checks} \
      (export: {options.leanExport.isSome})"
  return results

/-- Verifies `program` with `options`, without the export and then with `config`. Fails unless
both runs give the same results, which it returns, and the stand-in answers `checks` checks in
each. -/
private def StandIn.unchanged (standIn : StandIn) (checks : Nat) (options : Core.VerifyOptions)
    (config : ExportConfig) (program := validProgram) : IO Core.VCResults :=
  unchangedByExport (standIn.verify checks options program)
    (standIn.verify checks { options with leanExport := some config } program)

private def bothUnknown (results : Core.VCResults) : Bool :=
  results.size == 2 && results.all (·.hasValidityUnknown)

/-- Whether a result is a solver timeout. -/
private def timedOut (result : Core.VCResult) : Bool :=
  match result.outcome with
  | .error (.solverTimeout _) => true
  | _ => false

/-- The per-obligation path, with `solver`: every check has a solver run of its own. -/
private def batch (solver : String) : Core.VerifyOptions :=
  { Core.VerifyOptions.quiet with solver }

/-- The incremental backend after symbolic evaluation, which gives every check a leaf of its
own: each check is sent alone, through the per-obligation discharge on a live solver. -/
private def alone (solver : String) : Core.VerifyOptions :=
  { batch solver with incremental := true }

/-- The incremental backend after the WP generator: one worker walks the checks of a path on
one session. -/
private def walk (solver : String) : Core.VerifyOptions :=
  { batch solver with incremental := true, vcgen := .wp }

/-- The phase names of the default order of `options` with contextual rewriting after
`betaReduce`. -/
private def withRewriteNames (options : Core.VerifyOptions) : List String :=
  (Strata.Core.corePipelinePhases options).map Strata.Core.phaseName |>.flatMap fun n =>
    if n == "betaReduce" then [n, "contextualRewrite"] else [n]

/-- The default order of `options` with contextual rewriting after `betaReduce`
(`withRewriteNames`), checked to compose. -/
private def withRewrite (options : Core.VerifyOptions) :
    IO (Core.ValidatedPipeline Core.ProgramFactSet.empty) :=
  IO.ofExcept (Strata.Core.splicePhasesAfter "betaReduce" [Strata.Core.passContextualRewrite]
    (Strata.Core.corePipelinePhases options) >>= Strata.Core.validatePipeline)

/-- The three ways a check reaches the solver, by name. The walk comes first: when its solver
fails, the solver it starts in its place may still be starting as the run returns, and finds
the stand-in installed while the other two run. -/
private def backends (solver : String) : List (String × Core.VerifyOptions) :=
  [("walk", walk solver), ("batch", batch solver), ("alone", alone solver)]

/-! The stand-in answers `unknown` to every check. -/
#guard_msgs in
run_elab do
  liftM (m := IO) <| withSolver fun standIn => IO.FS.withTempDir fun root => do
    for (backend, options) in backends standIn.solver do
      -- Both undecided checks are exported. Each is asked once, with the export as without.
      let (config, dir, events) ← newConfig root s!"core-{backend}"
      unless bothUnknown (← standIn.unchanged 2 options config) do
        throw <| IO.userError s!"The stand-in did not leave two checks undecided ({backend})"
      let _ ← expectExported dir (both "unknown")
      unless (← events.get).size == 2 && (← events.get).all (·.stage == .exported) do
        throw <| IO.userError s!"Expected two exported checks ({backend}): \
          {(← events.get).map fun event => s!"{event.label}: {event.stage}"}"
      -- For these two checks, which the stand-in leaves `unknown`, two workers write the
      -- files one worker writes: the name and the proposition of a check's file do not
      -- depend on the number of workers. On the walk the number of workers can change which
      -- checks are exported, and how the header words an `unsat`.
      let (parallel, parallelDir, _) ← newConfig root s!"core-parallel-{backend}"
      let _ ← standIn.verify 2 { options with parallelWorkers := 2, leanExport := some parallel }
      unless (← contents parallelDir) == (← contents dir) do
        throw <| IO.userError s!"Two workers exported other files than one ({backend}): \
          {← entries parallelDir} instead of {← entries dir}"
      -- Satisfiability-only verification has no validity check to export.
      let (config, dir, events) ← newConfig root s!"bug-finding-{backend}"
      let _ ← standIn.unchanged 2 { options with checkMode := .bugFinding } config
      let _ ← expectExported dir []
      unless (← events.get).isEmpty do
        throw <| IO.userError s!"Satisfiability-only verification reported an export ({backend})"
    -- Laurel passes the option on to Core.
    for incremental in [false, true] do
      let (config, dir, _) ← newConfig root s!"laurel-{incremental}"
      let parsed ← StrataTest.Util.translateLaurel laurelProgram
      let laurel (leanExport : Option ExportConfig) : IO Core.VCResults := do
        let (results, diagnostics) ← Strata.Laurel.verifyToVcResults parsed {
          verifyOptions := { batch standIn.solver with
            incremental, leanExport, proceduresToVerify := some ["P"] } }
        let some results := results | throw <| IO.userError "Laurel translation failed"
        unless diagnostics.isEmpty && (← standIn.answered) == 2 do
          throw <| IO.userError s!"Laurel (incremental={incremental}, \
            export={leanExport.isSome}): diagnostics={repr diagnostics}, or not two checks"
        return results
      let results ← unchangedByExport (laurel none) (laurel (some config))
      unless bothUnknown results do
        throw <| IO.userError s!"Laurel (incremental={incremental}): {results}"
      let _ ← expectExported dir (results.toList.map (·.obligation.label, "unknown"))
    -- Without a solver run nothing is undecided; the scope `all` exports every check, as not
    -- asked. The solver is not started.
    for (scope, checkOnly) in [(Scope.undecided, false), (.undecided, true), (.all, true),
        (.all, false)] do
      let (config, dir, _) ← newConfig root s!"stop-{repr scope}-{checkOnly}" scope
      IO.FS.withTempDir fun vcDir => do
        let results ← standIn.unchanged 0 { batch standIn.solver with
          checkOnly, skipSolver := !checkOnly, vcDirectory := some vcDir } config
        unless results.size == (if checkOnly then 0 else 2) do
          throw <| IO.userError s!"Unexpected results without a solver run \
            (checkOnly={checkOnly}): {results}"
        let _ ← expectExported dir (if scope == .all && !checkOnly then both "not asked" else [])
    -- With `incremental` as well, a caller that keeps the SMT text takes the batch backend,
    -- which honours `skipSolver`: the checks are not asked.
    let (config, dir, _) ← newConfig root "stop-incremental" .all
    let _ ← standIn.unchanged 0 { batch standIn.solver with
      incremental := true, skipSolver := true, alwaysGenerateSMT := true } config
    let _ ← expectExported dir (both "not asked")
    -- `skipSolver` is honoured by the batch backend only. A library caller that combines it
    -- with `incremental` and keeps no SMT files has its checks asked all the same, and what
    -- the solver leaves undecided is exported with the solver's answer.
    for (backend, options) in [("alone", alone standIn.solver), ("walk", walk standIn.solver)] do
      let (config, dir, _) ← newConfig root s!"skip-{backend}"
      unless bothUnknown (← standIn.unchanged 2 { options with skipSolver := true } config) do
        throw <| IO.userError s!"`skipSolver` kept the incremental backend from asking ({backend})"
      let _ ← expectExported dir (both "unknown")

/-! Whatever a custom discharge function answers, the results are those without the export, and
the function is called as often. Decided answers, crashes and errors are exported only in the
scope `all`; a timeout is undecided. -/
#guard_msgs in
run_elab do
  liftM (m := IO) <| IO.FS.withTempDir fun root => do
    let state := { Strata.SMT.EncoderState.init with
      usedNames := Strata.SMT.EncoderState.init.usedNames.insert "native_state_sentinel" }
    -- The name of a case, the answer its files report, whether it is undecided, and the
    -- discharge function's answer: the satisfiability result, the validity result, the state.
    let answers : List (String × String × Bool × Except Imperative.SMT.SolverError
        (Core.SMT.Result × Core.SMT.Result × Strata.SMT.EncoderState)) := [
      ("proved", "unsat", false, .ok (.sat [], .unsat, state)),
      ("refuted", "sat", false, .ok (.unknown none, .sat [], state)),
      ("error", "error", false, .ok (.unsat, .err "native error", state)),
      ("crash", "error", false, .error (.crash "original crash")),
      ("unknown", "unknown", true, .ok (.sat [], .unknown none, state)),
      -- A structured timeout needs no particular wording to be recognized.
      ("timeout", "timeout", true, .error (.timeout "deadline exceeded"))]
    for (name, header, undecided, answer) in answers do
      let calls ← IO.mkRef 0
      let native : Core.MkDischargeFn := fun _ _ _ _ _ _ _ _ _ =>
        fun _ _ _ _ _ _ _ => do
          calls.modify (· + 1)
          pure answer
      -- One run; fails unless both checks are discharged.
      let run (leanExport : Option ExportConfig) : IO Core.VCResults := do
        calls.set 0
        let results ← Strata.Core.verify validProgram (mkDischarge := native)
          (options := { Core.VerifyOptions.quiet with checkLevel := .full, leanExport })
        unless (← calls.get) == 2 do
          throw <| IO.userError s!"Expected two discharge calls ({name}): {← calls.get}"
        return results
      for scope in [Scope.undecided, .all] do
        let (config, dir, _) ← newConfig root s!"{name}-{repr scope}" scope
        let results ← unchangedByExport (run none) (run (some config))
        if answer.isOk then
          unless results.all (·.estate.usedNames.contains "native_state_sentinel") do
            throw <| IO.userError "The results do not carry the encoder state of the discharge"
        let _ ← expectExported dir (if undecided || scope == .all then both header else [])

/-! A counterexample is part of the results. cvc5 refutes both assertions of `refutedProgram`,
each with a model, and the results with the export, models included, are those without it. -/
#guard_msgs in
run_elab do
  liftM (m := IO) <| IO.FS.withTempDir fun root => do
    for (backend, options) in backends Core.defaultSolver do
      let (config, dir, _) ← newConfig root s!"refuted-{backend}" .all
      let results ← unchangedByExport (Strata.Core.verify refutedProgram (options := options))
        (Strata.Core.verify refutedProgram (options := { options with leanExport := some config }))
      unless results.size == 2 && results.all (!·.lexprModel.isEmpty) do
        throw <| IO.userError s!"cvc5 did not refute both assertions with a counterexample \
          ({backend}): {results.map fingerprint}"
      let _ ← expectExported dir [("low", "sat"), ("high", "sat")]

/-! A solver timeout is undecided: both checks are exported, and the timeouts are reported
as without the export. The stand-in installed as `timeout-solver` answers `timeout` to every
check. -/
#guard_msgs in
run_elab do
  liftM (m := IO) <| withSolver (name := "timeout-solver") fun standIn =>
      IO.FS.withTempDir fun root => do
    for (backend, options) in backends standIn.solver do
      let (config, dir, _) ← newConfig root s!"timeout-{backend}"
      let results ← standIn.unchanged 2 options config
      unless results.size == 2 && results.all timedOut do
        throw <| IO.userError s!"The stand-in did not time out on both checks ({backend}): \
          {results}"
      let _ ← expectExported dir (both "timeout")

/-! Both checks of an obligation are asked (`checkLevel := .full`), and the solver times out on
the first check it is asked, a satisfiability check; the stand-in installed as
`timeout-first-solver` answers `unknown` after that.

On the per-obligation path one solver run answers both checks of an obligation, and its
timeout is the outcome of both: each obligation has a run of its own, so both validity checks
are exported as timeouts. A check sent alone by the incremental backend is not asked again
after the timeout. On a shared session the walk asks every check of both obligations: the
first obligation is reported as a timeout, and both validity checks are exported with the
answer they got, `unknown`. -/
#guard_msgs in
run_elab do
  liftM (m := IO) <| withSolver (name := "timeout-first-solver") fun standIn =>
      IO.FS.withTempDir fun root => do
    -- In the order of `backends`: the checks answered, the timeouts reported, the files' answer.
    for ((backend, options), checks, timeouts, answer) in (backends standIn.solver).zip
        [(4, 1, "unknown"), (4, 2, "timeout"), (2, 2, "timeout")] do
      let (config, dir, _) ← newConfig root s!"timeout-first-{backend}"
      let results ← standIn.unchanged checks { options with checkLevel := .full } config
      unless results.size == 2 && (results.filter timedOut).size == timeouts do
        throw <| IO.userError s!"Expected {timeouts} timeouts of two results ({backend}): \
          {results}"
      let _ ← expectExported dir (both answer)

/-! On the incremental walk a file states the query of its own check, not what the solver
holds: with both arms of a branch walked by one solver, no file has the assumption of the other
arm, and the files are those of two solvers and those of the per-obligation path. -/
#guard_msgs in
run_elab do
  liftM (m := IO) <| IO.FS.withTempDir fun root => do
    -- One solver walks the four checks: only the first check it is asked times out.
    withSolver (name := "timeout-first-solver") fun standIn => do
      let (_, results) ← IO.FS.withIsolatedStreams (isolateStderr := true) <|
        standIn.verify 4 (walk standIn.solver) twoArmProgram
      unless results.size == 4 && (results.filter timedOut).size == 1 do
        throw <| IO.userError s!"The two arms are not walked by one solver: {results}"
    withSolver fun standIn => do
      let (config, dir, _) ← newConfig root "arms-walk"
      let results ← standIn.unchanged 4 (walk standIn.solver) config twoArmProgram
      unless results.size == 4 && results.all (·.hasValidityUnknown) do
        throw <| IO.userError s!"The stand-in did not leave four checks undecided: {results}"
      let files ← expectExported dir [("thenSum", "unknown"), ("thenBound", "unknown"),
        ("elseSum", "unknown"), ("elseBound", "unknown")]
      for file in files, (own, other) in
          [("111", "222"), ("111", "222"), ("222", "111"), ("222", "111")] do
        let text ← IO.FS.readFile file
        unless occurrences text s!"(nat_lit {own})" > 0 &&
            occurrences text s!"(nat_lit {other})" == 0 do
          throw <| IO.userError s!"{file} does not have the assumption of its own arm \
            only:\n{text}"
      for (name, options) in [("two solvers", { walk standIn.solver with parallelWorkers := 2 }),
          ("the per-obligation path", { walk standIn.solver with incremental := false })] do
        let (config, otherDir, _) ← newConfig root s!"arms-{name}"
        let _ ← standIn.verify 4 { options with leanExport := some config } twoArmProgram
        unless (← contents otherDir) == (← contents dir) do
          throw <| IO.userError s!"One walking solver exported other files than {name}: \
            {← entries dir} instead of {← entries otherDir}"

/-! A cover and a check whose SMT encoding fails are not exported and report no event, in
either scope: the stand-in leaves the cover undecided. The encoding error is reported as
without the export. -/
#guard_msgs in
run_elab do
  liftM (m := IO) <| withSolver fun standIn => IO.FS.withTempDir fun root => do
    for (backend, options) in backends standIn.solver do
      for scope in [Scope.undecided, .all] do
        let (config, dir, events) ← newConfig root s!"not-exported-{backend}-{repr scope}" scope
        -- The cover and the ordinary check are each asked both of their checks.
        let results ← standIn.unchanged 4 { options with checkLevel := .full } config
          notExportedProgram
        let encodingErrors := results.filter fun result => match result.outcome with
          | .error (.encoding _) => true
          | _ => false
        unless results.size == 3 &&
            encodingErrors.map (·.obligation.label) == #["unencodable"] do
          throw <| IO.userError s!"Expected three results, one an encoding error ({backend}): \
            {results}"
        let _ ← expectExported dir [("plain", "unknown")]
        unless (← events.get).map (·.label) == #["plain"] do
          throw <| IO.userError s!"Expected one event, for `plain` ({backend}): \
            {(← events.get).map fun event => s!"{event.label}: {event.stage}"}"
    -- With cvc5, which decides the cover and the ordinary check, the cover has no file either.
    for (backend, options) in backends "cvc5" do
      let (config, dir, events) ← newConfig root s!"not-exported-cvc5-{backend}" .all
      let options := { options with checkLevel := .full }
      let _ ← unchangedByExport (Strata.Core.verify notExportedProgram (options := options))
        (Strata.Core.verify notExportedProgram
          (options := { options with leanExport := some config }))
      let files ← expectExported dir [("plain", "unsat")]
      unless (← events.get).map (·.label) == #["plain"] do
        throw <| IO.userError s!"Expected one event, for `plain` (cvc5, {backend})"
      -- An `unsat` of a walking session says that it is one.
      let gloss := if backend == "walk" then
        "in a solver session that may hold more than this query states"
        else "the solver found the query valid"
      unless has (← IO.FS.readFile files.head!) s!"-- Solver's answer: unsat ({gloss})\n" do
        throw <| IO.userError s!"`plain` does not report its `unsat` as `{gloss}` ({backend})"

/-! The walk with contextual rewriting after `betaReduce` (`withRewrite`). A check the phase
proves from the assumptions on its path reaches no solver and is not exported; the others are
walked as with the phase off. For each program, the first line gives the number of checks the
stand-in answers with the phase on and the checks exported; the second, each check's verdict
with cvc5 with the phase off and on (`other` for a cover and for a check whose encoding fails).
The phase proves both checks of `validProgram` and `plain`; every verdict is the same with the
phase off and on. -/
/--
info: valid: stand-in answered 0, exported []
valid: off [first pass, second pass], on [first pass, second pass]
refuted: stand-in answered 2, exported [low, high]
refuted: off [low fail, high fail], on [low fail, high fail]
twoArm: stand-in answered 4, exported [thenSum, thenBound, elseSum, elseBound]
twoArm: off [thenSum pass, thenBound pass, elseSum pass, elseBound pass], on [thenSum pass, thenBound pass, elseSum pass, elseBound pass]
notExported: stand-in answered 1, exported []
notExported: off [reachable other, unencodable other, plain pass], on [reachable other, unencodable other, plain pass]
-/
#guard_msgs in
run_elab do
  let lines ← liftM (m := IO) (IO.mkRef (#[] : Array String))
  liftM (m := IO) <| withSolver fun standIn => IO.FS.withTempDir fun root => do
    let verdict (result : Core.VCResult) : String :=
      let v := if result.isSuccess then "pass" else if result.isFailure then "fail" else "other"
      s!"{result.obligation.label} {v}"
    for (name, program) in [("valid", validProgram), ("refuted", refutedProgram),
        ("twoArm", twoArmProgram), ("notExported", notExportedProgram)] do
      let (config, dir, _) ← newConfig root s!"rewrite-{name}"
      let options := { walk standIn.solver with leanExport := some config }
      let pipeline ← withRewrite options
      let (_, results) ← IO.FS.withIsolatedStreams (isolateStderr := true) <|
        Strata.Core.verify program (options := options) (pipeline := some pipeline)
      let names ← entries dir
      let exported := (results.toList.map (·.obligation.label)).filter fun label =>
        names.any (isFileOf label)
      let answered ← standIn.answered
      lines.modify (·.push s!"{name}: stand-in answered {answered}, exported {exported}")
      let mut verdicts : List String := []
      for phase in [false, true] do
        let pipeline ← if phase then some <$> withRewrite (walk "cvc5") else pure none
        let (_, results) ← IO.FS.withIsolatedStreams (isolateStderr := true) <|
          Strata.Core.verify program (options := walk "cvc5") (pipeline := pipeline)
        let setting := if phase then "on" else "off"
        verdicts := verdicts ++ [s!"{setting} {results.toList.map verdict}"]
      lines.modify (·.push s!"{name}: {", ".intercalate verdicts}")
  logInfo ("\n".intercalate (← liftM (m := IO) lines.get).toList)

/-! A check Strata decides by evaluation is not handed to the solver and is not exported, in
the scope `all` either. -/
#guard_msgs in
run_elab do
  liftM (m := IO) <| withSolver fun standIn => IO.FS.withTempDir fun root => do
    for (backend, options) in [("batch", batch standIn.solver), ("alone", alone standIn.solver)] do
      let (config, dir, events) ← newConfig root s!"decided-{backend}" .all
      let results ← standIn.unchanged 0 options config decidedProgram
      let _ ← expectExported dir []
      unless results.size == 1 && (← events.get).isEmpty do
        throw <| IO.userError s!"A check decided by evaluation was reported ({backend}): {results}"

/-! The solver stops at the first check without an answer: the stand-in installed as
`crash-solver` silently, and as `crash-timeout-solver` with a message that reads as a timeout.
On the per-obligation path, which a check sent alone takes too, a crash is exported in the
scope `all`, as an error, and a failure that reads as a timeout is a timeout of the check. On
the walk a check whose session fails without an answer is not exported. Either way the
failures are reported as without the export. -/
#guard_msgs in
run_elab do
  liftM (m := IO) <| IO.FS.withTempDir fun root => do
    for (solver, answer, undecided) in
        [("crash-solver", "error", false), ("crash-timeout-solver", "timeout", true)] do
      withSolver (name := solver) fun standIn => do
        for (backend, options) in backends standIn.solver do
          for scope in [Scope.undecided, .all] do
            let (config, dir, events) ← newConfig root s!"{solver}-{backend}-{repr scope}" scope
            let results ← standIn.unchanged 0 options config
            unless results.size == 2 && results.all (fun result => match result.outcome with
                | .error (.solverTimeout _) => undecided
                | .error (.solverCrash _) => !undecided
                | _ => false) do
              throw <| IO.userError s!"Expected two failures of the solver ({solver}, \
                {backend}): {results}"
            let exported := backend != "walk" && (undecided || scope == .all)
            let _ ← expectExported dir (if exported then both answer else [])
            unless exported || (← events.get).isEmpty do
              throw <| IO.userError s!"A check that is not exported reported an event \
                ({solver}, {backend})"

/-- The compiled executable. -/
private def exe : System.FilePath := packageRoot / ".lake/build/bin/strataLaurel"

/-- The lines of the executable's stderr that come from the Lean export. -/
private def exportLines (stderr : String) : List String :=
  (stderr.splitOn "\n").filter (·.startsWith "Lean export: ")

/-- The other lines of the executable's stderr. -/
private def otherLines (stderr : String) : List String :=
  (stderr.splitOn "\n").filter (!·.startsWith "Lean export: ")

/-- The lines of the log the flags keep in an export directory, one per check. -/
private def logLines (dir : System.FilePath) : IO (List String) :=
  return ((← IO.FS.readFile (dir / "export.log")).splitOn "\n").filter (!·.isEmpty)

/-- Whether there are exactly `checks` lines, each saying `what` exactly once. -/
private def onePerCheck (lines : List String) (checks : Nat) (what : String) : Bool :=
  lines.length == checks && lines.all (occurrences · what == 1)

/-- Whether a run of the executable has the exit code and the standard output of `baseline`. -/
private def sameOutcome (run baseline : IO.Process.Output) : Bool :=
  run.exitCode == baseline.exitCode && run.stdout == baseline.stdout

/-! The flags and an export that the options already set: without a flag it stays,
`--lean-scope` alone changes its scope and nothing else, and `--lean-directory` replaces it
whole (its size limit is the default again). -/
#guard_msgs in
run_elab do
  liftM (m := IO) do
    let preset : Core.VerifyOptions :=
      { Core.VerifyOptions.quiet with
        leanExport := some { directory := "preset", maxFileBytes := 1 } }
    let parsed (entries : Array (String × Option String)) :
        IO (Option (String × Scope × Nat)) :=
      return (← parseVerifyOptions { entries } preset).leanExport.map fun config =>
        (config.directory.toString, config.scope, config.maxFileBytes)
    let default := ({ directory := "" } : ExportConfig).maxFileBytes
    unless (← parsed #[]) == some ("preset", .undecided, 1) &&
        (← parsed #[("lean-scope", some "all")]) == some ("preset", .all, 1) &&
        (← parsed #[("lean-directory", some "flag")]) == some ("flag", .undecided, default) &&
        (← parsed #[("lean-directory", some "flag"), ("lean-scope", some "all")]) ==
          some ("flag", .all, default) do
      throw <| IO.userError "The flags and the options' own export do not combine as documented"
    -- The flags' observer appends one line per check to `export.log`, whatever the label and
    -- the diagnostic contain. It prints a failed write, and a line it cannot append.
    IO.FS.withTempDir fun root => do
      let printedBy (dir : System.FilePath) (events : List Event) : IO String := do
        let some config := (← parseVerifyOptions
            { entries := #[("lean-directory", some dir.toString)] } preset).leanExport
          | throw <| IO.userError "--lean-directory did not set an export"
        return (← IO.FS.withIsolatedStreams (isolateStderr := true) (events.forM config.observe)).1
      let dir := root / "flag"
      let printed ← printedBy dir [
        { label := "a\nb", stage := .preparationFailure, diagnostic := "c\r\nd" },
        { label := "a\nb", stage := .exported, file := some "f" },
        { label := "a\nb", stage := .kept, file := some "f" },
        { label := "w", stage := .writeFailure, diagnostic := "e" }]
      unless (← logLines dir) == ["a b: no file (preparationFailure): c  d", "a b: wrote f",
          "a b: kept existing f", "w: no file (writeFailure): e"] &&
          printed == "Lean export: w: no file (writeFailure): e\n" do
        throw <| IO.userError s!"The checks are not logged one per line, or more than the \
          failed write is printed: {← logLines dir} {printed.quote}"
      -- A directory stands where the log would be: the line goes to stderr.
      IO.FS.createDirAll (root / "blocked" / "export.log")
      let printed ← printedBy (root / "blocked") [{ label := "a", stage := .exported, file := some "f" }]
      unless printed == "Lean export: a: wrote f (not appended to export.log)\n" do
        throw <| IO.userError s!"A line that cannot be logged is not printed: {printed.quote}"

/-! A variable with the name of a function. The type checker rejects a procedure whose own
variable has a function's name, but the phase that names common subexpressions `$__cse.<n>`
does not look at the functions. The procedure below gets two such variables. With a function
named like the first or like the second, the context of each check has one symbol for the
two: neither check is exported and each is reported, on the per-obligation path and sent alone
by the incremental backend. With another function name both checks are exported. Walked by the
incremental backend under `--vcgen symexec`, which puts the two checks into one session and
merges paths, no phase names common subexpressions, so both checks are exported with every
function name. With contextual rewriting after `betaReduce` in that order (`rewrite`, through
`--phases`), the phase proves `b` from the assumption `h`, so only `a` reaches the solver and is
exported. -/
#guard_msgs in
run_elab do
  liftM (m := IO) <| withSolver fun standIn => IO.FS.withTempDir fun root => do
    for (name, backend) in [("batch", #[]), ("alone", #["--incremental"]),
        ("walk", #["--incremental", "--vcgen", "symexec"]),
        ("rewrite", #["--incremental", "--vcgen", "symexec", "--phases", ",".intercalate
          (withRewriteNames { Core.VerifyOptions.quiet with symExec := some .always })])] do
      for function in ["$__cse.0", "$__cse.1", "c"] do
        let exported := if name == "rewrite" then ["a"]
          else if name == "walk" || function == "c" then ["a", "b"] else []
        let source := root / s!"shadow-{function}.core.st"
        IO.FS.writeFile source s!"program Core;\n\
          function {function}() : bool \{ false }\n\
          procedure p(x : int, y : int, k : int) \{\n\
          assume [h]: (int.add(int.mul(x, x), int.mul(y, y)) == int.add(int.mul(4, k), 1));\n\
          assume [h2]: (int.gt(int.add(x, y), 0));\n\
          assert [a]: ({function}() || (x == k));\n\
          assert [b]: ({function}() || \
            (int.add(int.mul(x, x), int.mul(y, y)) == int.add(int.mul(4, k), 1)) || \
            int.gt(int.add(x, y), 0));\n\
          };\n"
        let run (args : Array String) := outputWithin {
          cmd := exe.toString, env := noLeanEnvironment
          args := #["verify", source.toString, "--solver", standIn.solver] ++ backend ++ args }
        let dir := root / s!"shadow-{name}-{function}"
        let actual ← run #["--lean-directory", dir.toString]
        unless sameOutcome actual (← run #[]) do
          throw <| IO.userError s!"The flags changed the run ({name}, function {function})"
        let _ ← expectExported dir (exported.map (·, "unknown"))
        let log ← logLines dir
        let reported := ["a", "b"].all fun label =>
          log.contains s!"{label}: no file (preparationFailure): '{function}' is the name of \
            a function and of a variable of the check"
        unless reported == exported.isEmpty do
          throw <| IO.userError s!"The checks with the shadowing variable are not reported as \
            expected ({name}, function {function}): {log}"

/-! The compiled executable exports as well, with no Lean environment at run time. Its
standard output, stderr and exit code are those of a run without the flags, and each file it
writes compiles on its own. What became of each check is a line of `export.log`; a check
whose file cannot be written is a line on stderr as well. A second run into the same
directory overwrites nothing. `--lean-directory` alone exports what the solver leaves
undecided, and `--lean-scope all` every check, with `--no-solve` too.

The baseline is pinned to what cvc5 decides: it proves the two checks of `SimpleProc` and
refutes the eight of `SafeBvOps`. -/
#guard_msgs in
run_elab do
  liftM (m := IO) <| withSolver fun standIn => IO.FS.withTempDir fun root => do
    unless ← exe.pathExists do
      throw <| IO.userError s!"{exe} has not been built; run `lake build`."
    for (program, exitCode, summary, answer, labels) in [
        ("SimpleProc", 0, "All 2 goals passed.", "unsat", ["Test_ensures_0", "Test_ensures_1"]),
        ("SafeBvOps", 2, "Finished with 0 goals passed, 8 failed.", "sat", [
          "set_a_calls_Bv32.SafeAdd_0", "set_b_calls_Bv32.SafeSub_0",
          "set_c_calls_Bv32.SafeMul_0", "set_d_calls_Bv32.SafeNeg_0",
          "set_e_calls_Bv32.SafeSDiv_0", "set_e_calls_Bv32.SafeSDiv_1",
          "set_f_calls_Bv32.SafeSMod_0", "set_f_calls_Bv32.SafeSMod_1"])] do
      let checks := labels.length
      let source := (packageRoot / "Examples" / s!"{program}.core.st").toString
      -- The flags of `exportTo` export every check to `dir`.
      let runExe (args : Array String) := outputWithin {
        cmd := exe.toString, args := #["verify", source] ++ args, env := noLeanEnvironment }
      let exportTo (dir : System.FilePath) :=
        #["--lean-directory", dir.toString, "--lean-scope", "all"]
      let baseline ← runExe #[]
      unless baseline.exitCode == exitCode && (baseline.stdout.splitOn "\n").contains summary do
        throw <| IO.userError s!"{program}: expected the exit code {exitCode} and \
          `{summary}` without the flags: {baseline.exitCode} {baseline.stdout} {baseline.stderr}"
      let dir := root / program
      -- Flags that name no directory or no scope are refused, as a user error.
      for (args, message) in [
          (#["--lean-scope", "all"], "--lean-scope requires --lean-directory"),
          (#["--lean-directory", ""], "--lean-directory must be a non-empty directory."),
          (#["--lean-directory", dir.toString, "--lean-scope", "some"],
            "Invalid lean-scope: 'some'.")] do
        let refused ← runExe args
        unless refused.exitCode == 1 && has refused.stderr message do
          throw <| IO.userError s!"{program}: {args} is not refused with `{message}`: \
            {refused.exitCode} {refused.stderr}"
      let actual ← runExe (exportTo dir)
      unless sameOutcome actual baseline do
        throw <| IO.userError s!"{program}: the flags changed the exit code or the output: \
          {actual.exitCode} {actual.stdout} {actual.stderr}"
      let files ← expectExported dir (labels.map (·, answer))
      for file in files do compilesAlone file
      -- The flags add nothing to stderr; the log has one line per file.
      unless actual.stderr == baseline.stderr &&
          onePerCheck (← logLines dir) checks ": wrote " do
        throw <| IO.userError s!"{program}: unexpected stderr or log with the flags: \
          {actual.stderr} {← logLines dir}"
      -- A second run into the same directory keeps the files, one with its proof filled in.
      let names ← entries dir
      let written ← IO.FS.readFile files[0]!
      let filled := written.replace "\n  sorry\n" "\n  simp\n"
      IO.FS.writeFile files[0]! filled
      let rerun ← runExe (exportTo dir)
      unless sameOutcome rerun baseline && filled != written &&
          (← entries dir) == names && (← IO.FS.readFile files[0]!) == filled &&
          onePerCheck ((← logLines dir).drop checks) checks ": kept existing " do
        throw <| IO.userError s!"{program}: a second run did not keep the existing files: \
          {← logLines dir}"
      -- A directory that cannot be created: every check is reported on stderr, nothing else
      -- changes.
      let blocked := root / s!"{program}-blocked"
      IO.FS.writeFile blocked ""
      let failed ← runExe (exportTo (blocked / "out"))
      unless sameOutcome failed baseline &&
          onePerCheck (exportLines failed.stderr) checks ": no file (writeFailure): " &&
          otherLines failed.stderr == otherLines baseline.stderr do
        throw <| IO.userError s!"{program}: a failed write was not reported on one line per \
          check: {failed.stderr}"
      -- Without a solver run every check is exported, as not asked.
      let noSolve := #["--no-solve", "--vc-directory", (root / s!"{program}-vcs").toString]
      let unsolved := root / s!"{program}-no-solve"
      unless sameOutcome (← runExe (noSolve ++ exportTo unsolved)) (← runExe noSolve) do
        throw <| IO.userError s!"{program}: the flags changed a run with --no-solve"
      let _ ← expectExported unsolved (labels.map (·, "not asked"))
      -- `--lean-directory` alone exports the checks the solver leaves undecided: every check
      -- with the stand-in, which answers `unknown`, and none with cvc5, which decides all.
      let standInSolver := #["--solver", standIn.solver]
      let undecided := root / s!"{program}-undecided"
      unless sameOutcome (← runExe (standInSolver ++ #["--lean-directory", undecided.toString]))
          (← runExe standInSolver) && (← standIn.answered) == 2 * checks do
        throw <| IO.userError s!"{program}: --lean-directory changed a run with the stand-in"
      let _ ← expectExported undecided (labels.map (·, "unknown"))
      let decided := root / s!"{program}-decided"
      unless sameOutcome (← runExe #["--lean-directory", decided.toString]) baseline do
        throw <| IO.userError s!"{program}: --lean-directory changed the exit code or the output"
      let _ ← expectExported decided []
