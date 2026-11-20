/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import all StrataTest.DL.Imperative.ArithExpr
meta import Strata.DL.Imperative.SMTUtils

/-! # A verdict answers the query its own run wrote

`Imperative.SMT.dischargeObligation` writes an obligation's query to the file name it is given
and has a solver read it. Two verifications sharing a directory can be given the same name, for
instance two runs with the same `--vc-directory` and an obligation with the same label and
number in each. The test below has the "other run" overwrite that name right after this run's
query is written: the verdict must still be the answer to this run's query, and the file left
under the name must be that query.
-/

meta section

namespace Strata.SharedQueryFileTest

open Strata.SMT

/-- The query this run writes: `1 > 2` asserted, so it is `unsat`. -/
private def ownQuery : String := "(set-logic QF_LIA)\n(assert (> 1 2))\n(check-sat)\n"

/-- The query another run writes under the same name: `1 < 2` asserted, so it is `sat`. -/
private def otherQuery : String := "(set-logic QF_LIA)\n(assert (< 1 2))\n(check-sat)\n"

/-- Write `ownQuery`, then overwrite `filename` with `otherQuery`, as a concurrent run would. -/
private def encodeThenOverwrite (filename : String) :
    SolverEncodingM (List String × EncoderState) := do
  Solver.setLogic "QF_LIA"
  Solver.assertRendered "(> 1 2)"
  discard <| Solver.checkSat []
  Solver.flush
  IO.FS.writeFile filename otherQuery
  return ([], EncoderState.init)

/-- The verdict of the obligation, the text left under its file name, and the other files left
    in its directory. -/
private def run : IO (String × String × List String) := do
  let pctx ← Strata.Pipeline.PipelineContext.create (outputMode := .quiet)
    (profilePipeline := false)
  let dir ← IO.FS.createTempDir
  let filename := dir / "assert_0.smt2"
  let result ← @Imperative.SMT.dischargeObligation Arith.PureExpr _ _
    (encodeThenOverwrite filename.toString) (fun _ _ => .error "no variables") []
    "cvc5" filename.toString #[] false false true (skipSolver := false) (termCache := none)
    (pctx := pctx)
  let verdict := match result with
    | .ok (_, .unsat, _) => "unsat"
    | .ok (_, .sat _, _) => "sat"
    | .ok _ => "other"
    | .error e => s!"error: {e}"
  let left ← IO.FS.readFile filename
  let others := (← dir.readDir).toList.map (·.fileName) |>.filter (· != "assert_0.smt2")
  IO.FS.removeDirAll dir
  return (verdict, left, others)

/-- info: ("unsat", true, []) -/
#guard_msgs in
#eval do
  let (verdict, left, others) ← run
  return (verdict, left == ownQuery, others)

/-- Write part of a query, then fail to encode the rest. -/
private def encodeThenFail : SolverEncodingM (List String × EncoderState) := do
  Solver.setLogic "QF_LIA"
  throwThe StringLit.EncodingError (.termSerialization "unencodable term")

/-! An obligation whose encoding fails reports the encoding error, and its incomplete query
    replaces no file: a complete query another run left under the name stays there, and no
    hidden file is left behind. -/
/-- info: (true, true, []) -/
#guard_msgs in
#eval show IO (Bool × Bool × List String) from do
  let pctx ← Strata.Pipeline.PipelineContext.create (outputMode := .quiet)
    (profilePipeline := false)
  let dir ← IO.FS.createTempDir
  let filename := dir / "assert_0.smt2"
  IO.FS.writeFile filename otherQuery
  let result ← @Imperative.SMT.dischargeObligation Arith.PureExpr _ _
    encodeThenFail (fun _ _ => .error "no variables") []
    "cvc5" filename.toString #[] false false true (skipSolver := false) (termCache := none)
    (pctx := pctx)
  let isEncodingError := match result with
    | .error (.encoding _) => true
    | _ => false
  let left ← IO.FS.readFile filename
  let others := (← dir.readDir).toList.map (·.fileName) |>.filter (· != "assert_0.smt2")
  IO.FS.removeDirAll dir
  return (isEncodingError, left == otherQuery, others)

/-- Write part of a query, then fail with an I/O error, as a full disk would. -/
private def encodeThenThrow : SolverEncodingM (List String × EncoderState) := do
  Solver.setLogic "QF_LIA"
  throwThe IO.Error (IO.userError "disk full")

/-! A write that throws leaves the same way: the exception propagates, the complete query under
    the name stays, and no hidden file is left behind. -/
/-- info: (true, true, []) -/
#guard_msgs in
#eval show IO (Bool × Bool × List String) from do
  let pctx ← Strata.Pipeline.PipelineContext.create (outputMode := .quiet)
    (profilePipeline := false)
  let dir ← IO.FS.createTempDir
  let filename := dir / "assert_0.smt2"
  IO.FS.writeFile filename otherQuery
  let threw ← try
      discard <| @Imperative.SMT.dischargeObligation Arith.PureExpr _ _
        encodeThenThrow (fun _ _ => .error "no variables") []
        "cvc5" filename.toString #[] false false true (skipSolver := false) (termCache := none)
        (pctx := pctx)
      pure false
    catch _ => pure true
  let left ← IO.FS.readFile filename
  let others := (← dir.readDir).toList.map (·.fileName) |>.filter (· != "assert_0.smt2")
  IO.FS.removeDirAll dir
  return (threw, left == otherQuery, others)

/-- Write a query that uses an undeclared symbol, which the solver rejects with a message naming
    the file it read. -/
private def encodeUndeclared : SolverEncodingM (List String × EncoderState) := do
  Solver.setLogic "QF_LIA"
  Solver.assertRendered "undeclared_x"
  discard <| Solver.checkSat []
  return ([], EncoderState.init)

/-- Discharge `encode` into `dir / name` and describe the outcome: the verdict, or for a solver
    error whether its message names the file the user keeps and not the private one. -/
private def outcomeIn (dir : System.FilePath) (name : String)
    (encode : SolverEncodingM (List String × EncoderState)) : IO String := do
  let pctx ← Strata.Pipeline.PipelineContext.create (outputMode := .quiet)
    (profilePipeline := false)
  let filename := dir / name
  let result ← @Imperative.SMT.dischargeObligation Arith.PureExpr _ _
    encode (fun _ _ => .error "no variables") []
    "cvc5" filename.toString #[] false false true (skipSolver := false) (termCache := none)
    (pctx := pctx)
  return match result with
    | .ok (_, .unsat, _) => "unsat"
    | .ok _ => "other verdict"
    | .error e =>
      let msg := toString e
      s!"error naming the kept file: {decide ((msg.splitOn filename.toString).length > 1)}, \
        naming the private file: {decide ((msg.splitOn ".strata-").length > 1)}"

/-! The private name has a fixed length, so a query whose name is close to the file system's
    limit on a name is still solved; and a solver's message names the file the user keeps. -/
/-- info: ("unsat", "error naming the kept file: true, naming the private file: false") -/
#guard_msgs in
#eval show IO (String × String) from do
  let dir ← IO.FS.createTempDir
  let longName := "".pushn 'a' 245 ++ ".smt2"
  let encodeOwn : SolverEncodingM (List String × EncoderState) := do
    Solver.setLogic "QF_LIA"
    Solver.assertRendered "(> 1 2)"
    discard <| Solver.checkSat []
    return ([], EncoderState.init)
  let long ← outcomeIn dir longName encodeOwn
  let rejected ← outcomeIn dir "assert_1.smt2" encodeUndeclared
  IO.FS.removeDirAll dir
  return (long, rejected)

end Strata.SharedQueryFileTest

end
