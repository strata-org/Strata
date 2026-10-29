/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.DL.SMT.Solver
meta import StrataTest.DL.SMT.EncodingTestUtils

meta section

/-! ## Tests for Solver.termToSMTString / Solver.typeToSMTString error handling

These tests verify that unencodable terms and types produce a structured
serialization error rather than silently returning an empty string.
-/

open Strata.SMT Strata.SMT.Solver
open Strata.SMT.TestUtils

-- termToSMTString succeeds on Term.none producing valid SMT-LIB.
/--
info: termToSMTString Term.none: (as none (Option Bool))
-/
#guard_msgs in
#eval do
  let s ← runBufferEncoding (termToSMTString (Term.none .bool))
  IO.println s!"termToSMTString Term.none: {s}"

-- termToSMTString succeeds on Term.some producing valid SMT-LIB.
/--
info: termToSMTString Term.some: (some true)
-/
#guard_msgs in
#eval do
  let s ← runBufferEncoding (termToSMTString (Term.some (Term.prim (.bool true))))
  IO.println s!"termToSMTString Term.some: {s}"

-- Metadata is diagnostic rather than semantic: an unsupported code point is
-- made visible without preventing the query from reaching the solver.
/--
info: (set-info :source "<U+30000>")
-/
#guard_msgs in
#eval show IO _ from do
  let value := String.ofList [Char.ofNat 0x30000]
  let b ← IO.mkRef ({ } : IO.FS.Stream.Buffer)
  let solver ← Solver.bufferWriter b
  let (_, _) ← (setInfoString "source" value).run solver
  let contents ← b.get
  if h : contents.data.IsValidUTF8 then
    IO.print (String.fromUTF8 contents.data h)

/-! ## Tests for `Solver.withFileWriter` flush-on-completion

Commands are buffered; `withFileWriter` guarantees the complete script
is on disk when it returns, including on exception.'
-/

-- The written file is complete (buffered tail included) when the bracket
-- returns: a reader sequenced after `withFileWriter` sees the whole script.
/--
info: (set-logic QF_LIA)
; buffering test
(assert true)
(check-sat)
-/
#guard_msgs in
#eval do
  let dir ← IO.FS.createTempDir
  let path := dir / "withFileWriter.smt2"
  let _ ← Solver.withFileWriter path.toString do
    Solver.setLogic "QF_LIA"
    Solver.comment "buffering test"
    Solver.assertRendered "true"
    let _ ← Solver.checkSat []
  let contents ← IO.FS.readFile path
  IO.FS.removeDirAll dir
  IO.print contents

-- On exception inside the bracket, the `finally` flush still runs: the file
-- preserves everything written before the failure.
/--
info: caught: boom
(set-logic QF_LIA)
(assert x)
-/
#guard_msgs in
#eval do
  let dir ← IO.FS.createTempDir
  let path := dir / "withFileWriterErr.smt2"
  let act : SolverM Unit := do
    Solver.setLogic "QF_LIA"
    Solver.assertRendered "x"
    throw (IO.userError "boom")
  try
    let _ ← Solver.withFileWriter path.toString act
    IO.println "ERROR: no exception"
  catch e =>
    IO.println s!"caught: {e}"
  let contents ← IO.FS.readFile path
  IO.FS.removeDirAll dir
  IO.print contents

end
