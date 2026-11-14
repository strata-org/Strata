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
is accepted. `verify --phases` with no input file refuses the same flags (`phasesReport`). -/

meta section

open Strata.Cli

/--
info: To run the phases in the default order:

  --phases assertWellFormedCalls,assertNoCFGBodies,callElim,termCheck,precondElim,seqTotalize,insertLoopInvariantAsserts,loopElim,genOpaqueTypeParams,typeCheck,monomorphizeFunctions,simplify,nondetElim,declObligations,wp,ssa,deadDefElim,betaReduce

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

/-- info: This order composes: assertWellFormedCalls, assertNoCFGBodies, callElim, termCheck, precondElim, seqTotalize, insertLoopInvariantAsserts, loopElim, genOpaqueTypeParams, typeCheck, monomorphizeFunctions, simplify, nondetElim, declObligations, wp, ssa, deadDefElim, betaReduce -/
#guard_msgs in
#eval reportOf [("vcgen", "wp"), ("phases", wpOrder)]

end
