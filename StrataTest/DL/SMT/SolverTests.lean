/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.SMT.Solver

/-! ## Tests for Solver.termToSMTString / Solver.typeToSMTString error handling

These tests verify that unencodable terms and types produce a proper IO error
rather than silently returning an empty string.
-/

open Strata.SMT Strata.SMT.Solver

/-- Helper: run a `SolverM` action using a buffer-backed solver. -/
private def runSolverM (act : SolverM α) : IO α := do
  let b ← IO.mkRef ({ } : IO.FS.Stream.Buffer)
  let solver ← Solver.bufferWriter b
  let (a, _) ← act.run solver
  return a

-- termToSMTString throws on Term.none instead of panicking.
/--
info: termToSMTString correctly threw: Solver.termToSMTString failed: don't know how to translate none and some
-/
#guard_msgs in
#eval do
  try
    let _ ← runSolverM (termToSMTString (Term.none .bool))
    IO.println "ERROR: termToSMTString did not throw"
  catch e =>
    IO.println s!"termToSMTString correctly threw: {e}"

-- termToSMTString throws on Term.some instead of panicking.
/--
info: termToSMTString correctly threw: Solver.termToSMTString failed: don't know how to translate none and some
-/
#guard_msgs in
#eval do
  try
    let _ ← runSolverM (termToSMTString (Term.some (Term.prim (.bool true))))
    IO.println "ERROR: termToSMTString did not throw"
  catch e =>
    IO.println s!"termToSMTString correctly threw: {e}"

-- typeToSMTString throws on TermType.trigger instead of panicking.
/--
info: typeToSMTString correctly threw: Solver.typeToSMTString failed: don't know how to translate a trigger type
-/
#guard_msgs in
#eval do
  try
    let _ ← runSolverM (typeToSMTString (.prim .trigger))
    IO.println "ERROR: typeToSMTString did not throw"
  catch e =>
    IO.println s!"typeToSMTString correctly threw: {e}"
