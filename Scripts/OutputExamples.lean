/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

/--
Dumps the embedded example files to a target directory.
Usage: OutputExamples <output-dir>

This executable embeds all example files from the Examples/ directory at
elaboration time, so downstream packages can access them without needing
the Strata source tree.
-/

private def examples : Array (String × String) := #[
  ("CFGNondet.core.st", include_str "../Examples/CFGNondet.core.st"),
  ("CFGSimple.core.st", include_str "../Examples/CFGSimple.core.st"),
  ("DoubleTwice.core.st", include_str "../Examples/DoubleTwice.core.st"),
  ("HeapReasoning.core.st", include_str "../Examples/HeapReasoning.core.st"),
  ("IrrelevantAxioms.core.st", include_str "../Examples/IrrelevantAxioms.core.st"),
  ("LoopSimple.core.st", include_str "../Examples/LoopSimple.core.st"),
  ("LoopSimple.csimp.st", include_str "../Examples/LoopSimple.csimp.st"),
  ("NondetCond.core.st", include_str "../Examples/NondetCond.core.st"),
  ("ProcedureTypeError.core.st", include_str "../Examples/ProcedureTypeError.core.st"),
  ("SafeBvOps.core.st", include_str "../Examples/SafeBvOps.core.st"),
  ("SarifTest.core.st", include_str "../Examples/SarifTest.core.st"),
  ("SimpleProc.core.st", include_str "../Examples/SimpleProc.core.st"),
  ("StringTest.laurel.st", include_str "../Examples/StringTest.laurel.st"),
  ("TwoLoops.core.st", include_str "../Examples/TwoLoops.core.st"),
  ("TypeError.core.st", include_str "../Examples/TypeError.core.st"),
  ("dialects/Arith.dialect.st", include_str "../Examples/dialects/Arith.dialect.st"),
  ("dialects/Bool.dialect.st", include_str "../Examples/dialects/Bool.dialect.st"),
  ("expected/DoubleTwice.callElim.core.expected", include_str "../Examples/expected/DoubleTwice.callElim.core.expected"),
  ("expected/DoubleTwice.callElim.core.st", include_str "../Examples/expected/DoubleTwice.callElim.core.st"),
  ("expected/DoubleTwice.inlineProcedures.core.expected", include_str "../Examples/expected/DoubleTwice.inlineProcedures.core.expected"),
  ("expected/DoubleTwice.inlineProcedures.core.st", include_str "../Examples/expected/DoubleTwice.inlineProcedures.core.st"),
  ("expected/DoubleTwice.inlineProcedures.filterProcedures.core.args", include_str "../Examples/expected/DoubleTwice.inlineProcedures.filterProcedures.core.args"),
  ("expected/DoubleTwice.inlineProcedures.filterProcedures.core.expected", include_str "../Examples/expected/DoubleTwice.inlineProcedures.filterProcedures.core.expected"),
  ("expected/DoubleTwice.inlineProcedures.filterProcedures.core.st", include_str "../Examples/expected/DoubleTwice.inlineProcedures.filterProcedures.core.st"),
  ("expected/HeapReasoning.core.expected", include_str "../Examples/expected/HeapReasoning.core.expected"),
  ("expected/IrrelevantAxioms.removeIrrelevantAxioms.core.args", include_str "../Examples/expected/IrrelevantAxioms.removeIrrelevantAxioms.core.args"),
  ("expected/IrrelevantAxioms.removeIrrelevantAxioms.core.expected", include_str "../Examples/expected/IrrelevantAxioms.removeIrrelevantAxioms.core.expected"),
  ("expected/IrrelevantAxioms.removeIrrelevantAxioms.core.st", include_str "../Examples/expected/IrrelevantAxioms.removeIrrelevantAxioms.core.st"),
  ("expected/LoopSimple.core.expected", include_str "../Examples/expected/LoopSimple.core.expected"),
  ("expected/LoopSimple.csimp.expected", include_str "../Examples/expected/LoopSimple.csimp.expected"),
  ("expected/LoopSimple.loopElim.core.expected", include_str "../Examples/expected/LoopSimple.loopElim.core.expected"),
  ("expected/LoopSimple.loopElim.core.st", include_str "../Examples/expected/LoopSimple.loopElim.core.st"),
  ("expected/ProcedureTypeError.core.expected", include_str "../Examples/expected/ProcedureTypeError.core.expected"),
  ("expected/SafeBvOps.callElim.core.expected", include_str "../Examples/expected/SafeBvOps.callElim.core.expected"),
  ("expected/SafeBvOps.callElim.core.st", include_str "../Examples/expected/SafeBvOps.callElim.core.st"),
  ("expected/SimpleProc.core.expected", include_str "../Examples/expected/SimpleProc.core.expected"),
  ("expected/TwoLoops.core.expected", include_str "../Examples/expected/TwoLoops.core.expected"),
  ("expected/TwoLoops.loopElim.core.expected", include_str "../Examples/expected/TwoLoops.loopElim.core.expected"),
  ("expected/TwoLoops.loopElim.core.st", include_str "../Examples/expected/TwoLoops.loopElim.core.st"),
  ("expected/TypeError.core.expected", include_str "../Examples/expected/TypeError.core.expected")
]

def main (args : List String) : IO UInt32 := do
  let outputDir ← match args with
    | [dir] => pure (System.FilePath.mk dir)
    | _ => do
      IO.eprintln "Usage: OutputExamples <output-dir>"
      return 1

  for (relPath, content) in examples do
    let fullPath := outputDir / relPath
    -- Ensure parent directory exists
    if let some parent := fullPath.parent then
      IO.FS.createDirAll parent
    IO.FS.writeFile fullPath content

  IO.println s!"Wrote {examples.size} example files to {outputDir}"
  return 0
