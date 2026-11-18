/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Cli.CoreCommands

/-! # `verify` flags under `--vcgen`

`--display-phases` prints the default order of the options in effect (`displayPhasesFor`), so
under `--vcgen wp` it lists the declaration, WP, SSA and dead-definition phases in place of
symbolic evaluation, and symbolic evaluation among the phases outside the default order.
A path cap, which only symbolic evaluation reads, is refused for a pipeline without a symbolic
evaluation phase, whatever `--vcgen` says (`vcgenFlagIssues`); `--path-cap none` sets no cap and
is accepted. `--vcgen symexec[:MODE]` runs symbolic execution in place of symbolic evaluation
(`symexec` alone means `symexec:merged`); a path cap is refused under it whatever its merge mode,
since `--vcgen symexec:merge-above:N` sets its merging. `--vcgen symexec` is refused for an
explicit pipeline without a symbolic execution phase. Every mode names the same phases
(`nameablePhases`).
`verify --phases` with no input file refuses the same flags (`phasesReport`). -/

meta section

open Strata.Cli

/--
info: To run the phases in the default order:

  --phases typeCheck,assertNoCFGBodies,callElim,termCheck,precondElim,seqTotalize,insertLoopInvariantAsserts,loopElim,genOpaqueTypeParams,monomorphizeFunctions,simplify,nondetElim,declObligations,wp,ssa,deadDefElim,betaReduce

You can change this order. Give it back to --phases with no input file and
Strata reports whether it composes without verifying anything.
To see what each phase requires and delivers, use --display-phase-contracts.

Available, not in the default order:

  symbolicEval
  commonSubexprElim
  inlineProcedures
  unrollBoundedQuantifiers
  functionInlining
  foldAxioms
  equalitySimplification
  symExec
-/
#guard_msgs in
#eval IO.println (displayPhasesFor {} { Core.VerifyOptions.quiet with vcgen := .wp })

/-- The issues `vcgenFlagIssues` reports for the options these flags parse to, for a run of
    `phases` (`none` for the default order). -/
private def issuesOf (flags : List (String × String))
    (phases : Option (List Core.PipelinePhase) := none) : IO (List String) := do
  let pflags := flags.foldl (fun acc (k, v) => ParsedFlags.insert acc k (some v)) {}
  return vcgenFlagIssues (← parseVerifyOptions pflags Core.VerifyOptions.quiet) phases

/-- info: [--path-cap applies only to a pipeline that runs symbolic evaluation, such as the default order of --vcgen symbolic: it bounds the paths symbolic evaluation keeps, and the pipeline of this run keeps none.] -/
#guard_msgs in
#eval do IO.println (← issuesOf [("vcgen", "wp"), ("path-cap", "4")])

/-- info: [] -/
#guard_msgs in
#eval do IO.println (← issuesOf [("vcgen", "wp"), ("path-cap", "none")])

/-! A pipeline with a symbolic evaluation phase reads the path cap whatever `--vcgen` says. -/

/-- info: [] -/
#guard_msgs in
#eval do IO.println (← issuesOf [("vcgen", "wp"), ("path-cap", "4")]
  (some [Core.symbolicEvalPipelinePhase]))

/-- info: [--path-cap applies only to a pipeline that runs symbolic evaluation, such as the default order of --vcgen symbolic: it bounds the paths symbolic evaluation keeps, and the pipeline of this run keeps none.] -/
#guard_msgs in
#eval do IO.println (← issuesOf [("vcgen", "wp"), ("path-cap", "4")]
  (some (Core.wpVCGenPhases Core.VerifyOptions.quiet)))

/-! A pipeline without a symbolic evaluation phase does not read the path cap under
`--vcgen symbolic` either. -/

/-- info: [--path-cap applies only to a pipeline that runs symbolic evaluation, such as the default order of --vcgen symbolic: it bounds the paths symbolic evaluation keeps, and the pipeline of this run keeps none.] -/
#guard_msgs in
#eval do IO.println (← issuesOf [("path-cap", "4")]
  (some (Core.wpVCGenPhases Core.VerifyOptions.quiet)))

/-- info: [] -/
#guard_msgs in
#eval do IO.println (← issuesOf [("path-cap", "4")])

/-- info: [] -/
#guard_msgs in
#eval do IO.println (← issuesOf [("vcgen", "wp")])

/-! The merge modes of `--vcgen symexec` run on the default order, which has a symbolic
execution phase. -/

/-- info: [] -/
#guard_msgs in
#eval do IO.println (← issuesOf [("vcgen", "symexec")])

/-- info: [] -/
#guard_msgs in
#eval do IO.println (← issuesOf [("vcgen", "symexec:merge-above:2")])

/-! An explicit pipeline: refused without a `symExec` phase, accepted with one. -/

/-- info: [--vcgen symexec applies only to a pipeline that runs symbolic execution, such as the
default order of --vcgen symexec: it selects how symbolic execution merges paths, and the pipeline
of this run has no symbolic execution phase.] -/
#guard_msgs (whitespace := lax) in
#eval do IO.println (← issuesOf [("vcgen", "symexec:per-path")]
  (some (Core.wpVCGenPhases Core.VerifyOptions.quiet)))

/-- info: [] -/
#guard_msgs in
#eval do IO.println (← issuesOf [("vcgen", "symexec:per-path")]
  (some [Core.symExecPipelinePhase]))

/-! `--path-cap N` is refused under `--vcgen symexec` whatever the merge mode: it bounds the
legacy symbolic evaluator's paths, and `--vcgen symexec:merge-above:N` sets when symbolic
execution merges. -/

/--
info: [--path-cap bounds the legacy symbolic evaluator's paths; under --vcgen symexec, use
  --vcgen symexec:merge-above:N (merge whenever more than N paths would exist).]
-/
#guard_msgs (whitespace := lax) in
#eval do IO.println (← issuesOf [("vcgen", "symexec:per-path"), ("path-cap", "3")])

/--
info: [--path-cap bounds the legacy symbolic evaluator's paths; under --vcgen symexec, use
  --vcgen symexec:merge-above:N (merge whenever more than N paths would exist).]
-/
#guard_msgs (whitespace := lax) in
#eval do IO.println (← issuesOf [("vcgen", "symexec:merge-above:2"), ("path-cap", "3")])

/--
info: [--path-cap bounds the legacy symbolic evaluator's paths; under --vcgen symexec, use
  --vcgen symexec:merge-above:N (merge whenever more than N paths would exist).]
-/
#guard_msgs (whitespace := lax) in
#eval do IO.println (← issuesOf [("vcgen", "symexec"), ("path-cap", "3")])

/-- info: [] -/
#guard_msgs in
#eval do IO.println (← issuesOf [("vcgen", "symexec:per-path"), ("path-cap", "none")])

/-- The merge mode symbolic execution runs under for these flags. -/
private def modeOf (flags : List (String × String)) : IO Unit := do
  let pflags := flags.foldl (fun acc (k, v) => ParsedFlags.insert acc k (some v)) {}
  IO.println (repr (← parseVerifyOptions pflags Core.VerifyOptions.quiet).symExec)

/-- info: some (Core.MergeMode.pathsAbove 2) -/
#guard_msgs in
#eval modeOf [("vcgen", "symexec:merge-above:2")]

/-- info: some (Core.MergeMode.never) -/
#guard_msgs in
#eval modeOf [("vcgen", "symexec:per-path"), ("path-cap", "none")]

-- `symexec` alone merges at every join.
/-- info: some (Core.MergeMode.always) -/
#guard_msgs in
#eval modeOf [("vcgen", "symexec")]

-- `symbolic` and `wp` run no symbolic execution.
/-- info: none -/
#guard_msgs in
#eval modeOf [("vcgen", "symbolic")]

/-- info: none -/
#guard_msgs in
#eval modeOf [("vcgen", "wp")]

-- Given more than once, the last `--vcgen` counts (`ParsedFlags.getString`).
/-- info: some (Core.MergeMode.always) -/
#guard_msgs in
#eval modeOf [("vcgen", "wp"), ("vcgen", "symexec")]

/-- info: none -/
#guard_msgs in
#eval modeOf [("vcgen", "symexec:per-path"), ("vcgen", "symbolic")]

/-! Every mode names the same phases (`nameablePhases`), each once. -/

/-- Whether `name` resolves against the nameable phases of `o`. -/
private def resolves (o : Core.VerifyOptions) (name : String) : Bool :=
  (Strata.Core.resolvePhases (Strata.Core.nameablePhases o) [name]).isOk

/-- The modes: default, `--vcgen wp`, `--vcgen symexec` under each merge mode, and the
    options of symbolic execution with `vcgen := .wp`, which no flag gives. -/
private def modes : List Core.VerifyOptions :=
  let q := Core.VerifyOptions.quiet
  [q, { q with vcgen := .wp }, { q with symExec := some .never },
    { q with symExec := some .always },
    { q with symExec := some (.pathsAbove 4) },
    { q with symExec := some .never, vcgen := .wp }]

#guard resolves Core.VerifyOptions.quiet "symExec"
#guard resolves { Core.VerifyOptions.quiet with symExec := some .never } "symbolicEval"
#guard modes.all fun o => ["symExec", "symbolicEval", "commonSubexprElim", "wp", "ssa",
  "declObligations", "deadDefElim"].all (resolves o)
#guard modes.all fun o =>
  let names := (Strata.Core.nameablePhases o).map Strata.Core.phaseName
  names.eraseDups.length == names.length
#guard modes.all fun o =>
  ((Strata.Core.nameablePhases o).map Strata.Core.phaseName).mergeSort ==
    ((Strata.Core.nameablePhases Core.VerifyOptions.quiet).map Strata.Core.phaseName).mergeSort

/-! A value that names no generator, or `symexec:` followed by nothing or by a value that names
no merge mode, is refused (`parseVCGenFlag`, which `parseVerifyOptions` exits on). -/

/-- The verdict of `parseVCGenFlag` on `value` over the quiet options. -/
private def vcgenFlagOf (value : String) : String :=
  match parseVCGenFlag (some value) Core.VerifyOptions.quiet with
  | .ok (vcgen, mode) => s!"ok {repr vcgen} {repr mode}"
  | .error msg => s!"refused: {msg}"

/--
info: refused: Invalid vcgen: 'bogus'. Must be 'symbolic', 'wp' or
  'symexec[:per-path|merged|merge-above:N]'.
-/
#guard_msgs (whitespace := lax) in
#eval IO.println (vcgenFlagOf "bogus")

/--
info: refused: Invalid vcgen: 'symexec:bogus'. The merge mode after 'symexec:' must be
  'per-path', 'merged' or 'merge-above:N' (N ≥ 1).
-/
#guard_msgs (whitespace := lax) in
#eval IO.println (vcgenFlagOf "symexec:bogus")

/--
info: refused: Invalid vcgen: 'symexec:merge-above:0'. The merge mode after 'symexec:' must be
  'per-path', 'merged' or 'merge-above:N' (N ≥ 1).
-/
#guard_msgs (whitespace := lax) in
#eval IO.println (vcgenFlagOf "symexec:merge-above:0")

/--
info: refused: Invalid vcgen: 'symexec:never'. The merge mode after 'symexec:' must be
  'per-path', 'merged' or 'merge-above:N' (N ≥ 1).
-/
#guard_msgs (whitespace := lax) in
#eval IO.println (vcgenFlagOf "symexec:never")

/--
info: refused: Invalid vcgen: 'symexec:always'. The merge mode after 'symexec:' must be
  'per-path', 'merged' or 'merge-above:N' (N ≥ 1).
-/
#guard_msgs (whitespace := lax) in
#eval IO.println (vcgenFlagOf "symexec:always")

/--
info: refused: Invalid vcgen: 'symexec:paths:2'. The merge mode after 'symexec:' must be
  'per-path', 'merged' or 'merge-above:N' (N ≥ 1).
-/
#guard_msgs (whitespace := lax) in
#eval IO.println (vcgenFlagOf "symexec:paths:2")

/--
info: refused: Invalid vcgen: 'symexec:'. The merge mode after 'symexec:' must be
  'per-path', 'merged' or 'merge-above:N' (N ≥ 1).
-/
#guard_msgs (whitespace := lax) in
#eval IO.println (vcgenFlagOf "symexec:")

/-- info: ok Core.VCGenMode.symbolic some (Core.MergeMode.always) -/
#guard_msgs in
#eval IO.println (vcgenFlagOf "symexec")

/-- info: ok Core.VCGenMode.symbolic some (Core.MergeMode.always) -/
#guard_msgs in
#eval IO.println (vcgenFlagOf "symexec:merged")

/-- info: ok Core.VCGenMode.symbolic some (Core.MergeMode.never) -/
#guard_msgs in
#eval IO.println (vcgenFlagOf "symexec:per-path")

/-- info: ok Core.VCGenMode.symbolic none -/
#guard_msgs in
#eval IO.println (vcgenFlagOf "symbolic")

/-- info: ok Core.VCGenMode.wp none -/
#guard_msgs in
#eval IO.println (vcgenFlagOf "wp")

/-! `verify --phases` with no input file: the default resolver, the default order of
`--vcgen wp` given by name. -/

/-- The phase names of the default order of `--vcgen wp`, comma-separated. -/
private def wpOrder : String :=
  ",".intercalate ((Core.corePipelinePhases { Core.VerifyOptions.quiet with vcgen := .wp }).map
    Strata.Core.phaseName)

/-- What `verify --phases` with no input file reports for these flags, with the default
    resolver: its lines, or `refused: ` and the refusal. -/
private def reportOf (flags : List (String × String)) : IO Unit := do
  let pflags := flags.foldl (fun acc (k, v) => ParsedFlags.insert acc k (some v)) {}
  match phasesReport {} pflags (← parseVerifyOptions pflags Core.VerifyOptions.quiet) with
  | .ok lines => lines.forM IO.println
  | .error msg => IO.println s!"refused: {msg}"

/-- info: refused: --path-cap applies only to a pipeline that runs symbolic evaluation, such as the default order of --vcgen symbolic: it bounds the paths symbolic evaluation keeps, and the pipeline of this run keeps none. -/
#guard_msgs in
#eval reportOf [("vcgen", "wp"), ("path-cap", "3"), ("phases", wpOrder)]

/-- info: refused: --path-cap applies only to a pipeline that runs symbolic evaluation, such as the default order of --vcgen symbolic: it bounds the paths symbolic evaluation keeps, and the pipeline of this run keeps none. -/
#guard_msgs in
#eval reportOf [("path-cap", "3"), ("phases", wpOrder)]

/--
info: This order composes: typeCheck, assertNoCFGBodies, callElim, termCheck, precondElim, seqTotalize, insertLoopInvariantAsserts, loopElim, genOpaqueTypeParams, monomorphizeFunctions, simplify, nondetElim, declObligations, wp, ssa, deadDefElim, betaReduce
-/
#guard_msgs in
#eval reportOf [("vcgen", "wp"), ("phases", wpOrder)]

end
