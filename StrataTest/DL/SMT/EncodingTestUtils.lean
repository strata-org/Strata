/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public meta import Strata.DL.SMT.Encoder

meta section

public section

namespace Strata.SMT.TestUtils

/-- Run an SMT encoding action against an existing solver, converting its
    structured serialization error into an ordinary test failure. -/
def runSolverEncoding (solver : Solver) (action : SolverEncodingM α) : IO α := do
  let (result, _) ← action.run.run solver
  match result with
  | .ok value => return value
  | .error error => throw (IO.userError (toString error))

/-- Run an SMT encoding action against a fresh buffer-backed solver. -/
def runBufferEncoding (action : SolverEncodingM α) : IO α := do
  let buffer ← IO.mkRef { : IO.FS.Stream.Buffer }
  let solver ← Solver.bufferWriter buffer
  runSolverEncoding solver action

/-- Run an encoder action against a fresh buffer-backed solver. -/
def runEncoder (action : EncoderM α)
    (state : EncoderState := .init) : IO (α × EncoderState) :=
  runBufferEncoding (action.run state)

/-- Record the text produced by an SMT encoding action and unwrap its
    structured serialization error in the same way as the other test helpers. -/
def recordSolverEncoding (action : SolverEncodingM α)
    (state : SolverState := .init) : IO (α × String × SolverState) := do
  let (result, text, state) ← Solver.recordToString action.run state
  match result with
  | .ok value => return (value, text, state)
  | .error error => throw (IO.userError (toString error))

end Strata.SMT.TestUtils

end

end
