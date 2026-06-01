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

-- termToSMTString succeeds on Term.none producing valid SMT-LIB.
/--
info: termToSMTString Term.none: (as none (Option Bool))
-/
#guard_msgs in
#eval do
  let s ← runSolverM (termToSMTString (Term.none .bool))
  IO.println s!"termToSMTString Term.none: {s}"

-- termToSMTString succeeds on Term.some producing valid SMT-LIB.
/--
info: termToSMTString Term.some: (some true)
-/
#guard_msgs in
#eval do
  let s ← runSolverM (termToSMTString (Term.some (Term.prim (.bool true))))
  IO.println s!"termToSMTString Term.some: {s}"

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
