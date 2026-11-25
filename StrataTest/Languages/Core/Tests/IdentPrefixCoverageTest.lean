/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core
import Strata.Languages.Core.DDMTransform.Translate
import Strata.Examples.EmbeddedData
import StrataDDM.Elab
import StrataDDM.BuiltinDialects.Init
import StrataTest.Languages.Core.Tests.RandomPrograms

/-! # The recorded `$__` prefixes cover the program after every phase

A pass may take the fast path (number its names without looking at the program) only while the
prefixes a program records cover its names in the `$__` namespace
(`Program.identPrefixesCovered`). Every pass that adds such names must record their prefixes.
These tests run the shipped examples and random programs through each verification pipeline,
and through each phase a caller can name, and check after every phase that the program records
its prefixes and that they cover its internal names. A pass that forgets to record a prefix
shows up here with the names it left uncovered. -/

namespace Strata.IdentPrefixCoverageTest

open _root_.Core

/-- The shipped Core example `text` as a Core program. -/
private def parseText (name text : String) : IO Core.Program := do
  let dialects := StrataDDM.Elab.LoadedDialects.ofDialects! #[StrataDDM.initDialect, Strata.Core]
  let body := if text.startsWith "program Core;" then (text.drop "program Core;".length).toString
    else text
  let sp ← StrataDDM.Elab.parseStrataProgramFromDialect dialects "Core"
    (StrataDDM.Parser.stringInputContext ⟨name⟩ body)
  pure (TransM.run Inhabited.default (translateProgram sp)).fst

/-- The shipped Core examples that type check, by name. -/
private def examples : IO (List (String × Core.Program)) := do
  let mut out := []
  for (path, text) in embeddedExampleFiles do
    if path.endsWith ".core.st" && !path.startsWith "expected/" && !path.contains "Error" then
      out := out ++ [(path, ← parseText path text)]
  return out

/-- The programs checked: the shipped examples and 40 random programs. -/
private def programs : IO (List (String × _root_.Core.Program)) := do
  return (← examples) ++
    (List.range 40).map fun seed => (s!"random {seed}", _root_.Core.RandomPrograms.generate seed)

/-- Run `phases` on `p` one by one, as `runTransformsRecording` does, and return a line for each
    phase that maintains the record (`PipelinePhase.maintainsIdentPrefixes`) and ran on a
    trusted record (`CoreTransformState.identPrefixesTrusted`), or is type checking, which
    collects the prefixes, after which `p` records no prefixes, or records prefixes that leave
    some internal name uncovered. Trust is passed on as `runTransformsRecording` passes it. A
    failing phase ends the run. -/
private def uncoveredAfter (name : String) (p : Core.Program)
    (phases : List _root_.Core.PipelinePhase) : List String := Id.run do
  let mut cur := p
  let mut st : _root_.Core.Transform.CoreTransformState :=
    { _root_.Core.Transform.CoreTransformState.emp with
      factory := Core.Factory, currentProgram := some p }
  let mut out := []
  for pp in phases do
    let (r, st') := _root_.Core.Transform.runWith cur (fun q => do
      let (_, q') ← pp.transform q
      return q') st
    match (r : Except Strata.Message _root_.Core.Program) with
    | .error _ => break
    | .ok next =>
      if pp.maintainsIdentPrefixes && (st.identPrefixesTrusted || pp.phase.name == "typeCheck") then
        match next.usedIdentPrefixes with
        | none => out := out ++ [s!"{name}: {pp.phase.name}: records no prefixes"]
        | some known =>
          let missing := next.internalNames.filter fun n => !known.any fun q => n.startsWith q
          unless missing.isEmpty do
            out := out ++ [s!"{name}: {pp.phase.name}: uncovered {missing.eraseDups}"]
      let trusted := pp.maintainsIdentPrefixes &&
        (st.identPrefixesTrusted || next.identPrefixesCovered)
      cur := next
      st := { st' with identPrefixesTrusted := trusted }
  return out

/-- The verification pipelines: symbolic evaluation, `--vcgen wp`, the path explorer with and
    without merging paths, and passive VC generation (`--vcgen uwp`). -/
private def pipelines : List (String × List _root_.Core.PipelinePhase) :=
  [("symbolic", _root_.Core.corePipelinePhases _root_.Core.VerifyOptions.quiet),
   ("wp", _root_.Core.corePipelinePhases { _root_.Core.VerifyOptions.quiet with vcgen := .wp }),
   ("symexec", _root_.Core.corePipelinePhases
      { _root_.Core.VerifyOptions.quiet with symExec := some .default }),
   ("per-path", _root_.Core.corePipelinePhases
      { _root_.Core.VerifyOptions.quiet with symExec := some .never }),
   ("passive", _root_.Core.corePipelinePhases
      { _root_.Core.VerifyOptions.quiet with vcgen := .uwp })]

-- No phase of a verification pipeline leaves a `$__` name of the shipped examples or of the
-- random programs uncovered.
/-- info: pipelines: 0 uncovered -/
#guard_msgs in
#eval show IO Unit from do
  let ps ← programs
  let bad := pipelines.flatMap fun (mode, phases) =>
    ps.flatMap fun (name, p) => uncoveredAfter s!"{mode}: {name}" p phases
  for l in bad do IO.println l
  IO.println s!"pipelines: {bad.length} uncovered"

-- No phase a caller can name, run alone after type checking (as `strata transform --pass`
-- runs it), leaves a `$__` name of the shipped examples or of the random programs uncovered.
-- Some phases trace obligations they discharge; that output is dropped.
/-- info: single phases: 0 uncovered -/
#guard_msgs in
#eval show IO Unit from do
  let ps ← programs
  let (_, bad) ← IO.FS.withIsolatedStreams (isolateStderr := true) do
    IO.lazyPure fun _ => (Strata.Core.nameablePhases _root_.Core.VerifyOptions.quiet).flatMap
      fun pp => ps.flatMap fun (name, p) =>
        uncoveredAfter s!"{pp.phase.name}: {name}" p
          [_root_.Core.typeCheckPipelinePhase .quiet, pp]
  for l in bad do IO.println l
  IO.println s!"single phases: {bad.length} uncovered"

-- The phases a caller can name that do not maintain the record, so that the pipeline drops it
-- after them (`PipelinePhase.maintainsIdentPrefixes`). A new phase starts here until it is
-- shown to record the prefixes of the `$__` names it generates, or to generate none.
/-- info: [] -/
#guard_msgs in
#eval IO.println ((Strata.Core.nameablePhases _root_.Core.VerifyOptions.quiet).filter
  (!·.maintainsIdentPrefixes) |>.map (·.phase.name))

end Strata.IdentPrefixCoverageTest
