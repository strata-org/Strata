/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core.InterpreterReplay
meta import Strata.Languages.Core.InterpreterEval
meta import StrataTest.Util.TimeBound

/-! # Replay cost of loops with block-local variables

Each iteration of `loop (x < n) { var t := x; x := t + 1 }` opens and exits a block that defines
`t`, and every iteration reads the loop-invariant bound `n`. The tests replay such a loop for 200
iterations inside a callee (`replayWithM`, the callee body run by `Calls.runCallee`) and at top
level (`replayWithM` and `runCoreEval`), and for 10000 iterations in each of these three runs
within a bound of 60 seconds each (`StrataTest.TimeBound.withinMs`). A replay whose cost per step
grows with the number of iterations already run (store lookups through every earlier write, or a
configuration that deepens by one level per iteration) does not finish 10000 iterations within
the bound. -/

meta section

namespace InterpreterScopeCostTest

open Core Lambda Imperative

private def id (name : String) : CoreIdent := ⟨name, ()⟩
private def int (n : Int) : Expression.Expr := .intConst () n
private def md : MetaData Expression := #[]
private def v (n : String) : Expression.Expr := .fvar () (id n) (some .int)
private def lt (x : String) (e : Expression.Expr) : Expression.Expr :=
  .app () (.app () intLtOp (v x)) e
private def plus1 (x : String) : Expression.Expr := .app () (.app () intAddOp (v x)) (int 1)
private def initS (x : String) (e : Expression.Expr) : Statement :=
  .cmd (.cmd (.init (id x) (.forAll [] .int) (.det e) md))
private def setS (x : String) (e : Expression.Expr) : Statement :=
  .cmd (.cmd (.set (id x) (.det e) md))

/-- `loop (x < bound) { var t := x; x := t + 1 }`. -/
private def countLoop (x : String) (bound : Expression.Expr) : Statement :=
  .loop (.det (lt x bound)) none [] [initS "t" (v x), setS x (plus1 "t")] md

/-- `Count(n : int, out r : int) { var j := 0; loop (j < n) { var t := j; j := t + 1 }; r := j }`.
    -/
private def countProc : Procedure := {
  header := { name := id "Count", typeArgs := [],
              inputs := [(id "n", (.int : Lambda.LMonoTy))],
              outputs := [(id "r", (.int : Lambda.LMonoTy))] }
  spec := { preconditions := [], postconditions := [] }
  body := .structured [initS "j" (int 0), countLoop "j" (v "n"), setS "r" (v "j")] }

/-- Procedure environment resolving `Count`. -/
private def piEnv : String → Option Procedure :=
  fun n => if n == "Count" then some countProc else none

/-- Target assert `x == k`. -/
private def tgt (x : String) (k : Nat) : Statement :=
  .cmd (.cmd (.assert "tgt" (.eq () (v x) (int k)) md))

/-- The target assertion id matching `tgt x k`. -/
private def tgtId (_x : String) (_k : Nat) : AssertId Expression :=
  { label := "tgt", md := md }

/-- An environment defining `y := 0`, `i := 0` and `n := k`. -/
private def env (k : Nat) : IEnv Expression :=
  .ofStore (fun x =>
      if x == id "y" || x == id "i" then some (int 0)
      else if x == id "n" then some (int k) else none) Core.Factory

/-- `call Count(k, out y); assert y == k + 1`: the loop runs `k` times inside the callee. -/
private def cexCallee (k : Nat) : CexA Expression Command :=
  { cfg := .stmts [.cmd (CmdExt.call "Count" [.inArg (int k), .outArg (id "y")] md),
      tgt "y" (k + 1)] (env k), oracle := [] }

/-- `loop (i < n) { var t := i; i := t + 1 }; assert i == k + 1` with `n = k`. -/
private def cexTop (k : Nat) : CexA Expression Command :=
  { cfg := .stmts [countLoop "i" (v "n"), tgt "i" (k + 1)] (env k), oracle := [] }

-- A loop of 200 iterations inside a callee: the callee returns `200`, so `y == 201` fails.
#guard replayWithM (cexCallee 200) (tgtId "y" 201) 100000 piEnv == .genuine

-- The same loop at top level: `i == 201` fails.
#guard replayWithM (cexTop 200) (tgtId "i" 201) 100000 piEnv == .genuine

-- `EvalM` runs the top-level loop and halts at the failing assertion.
#guard (match (runCoreEval piEnv 100000 (cexTop 200).cfg).1 with
  | .error (.assertFailed arg) => arg.label == "tgt"
  | _ => false)

/-- Whether the replay of the callee loop of `k` iterations reaches the target failure, within 60
    seconds (`none` when it does not finish in time). -/
private def calleeWithin (k : Nat) : IO (Option Bool) :=
  StrataTest.TimeBound.withinMs 60000 fun _ =>
    replayWithM (cexCallee k) (tgtId "y" (k + 1)) 1000000 piEnv == .genuine

/-- Whether the replay of the top-level loop of `k` iterations reaches the target failure, within
    60 seconds (`none` when it does not finish in time). -/
private def topWithin (k : Nat) : IO (Option Bool) :=
  StrataTest.TimeBound.withinMs 60000 fun _ =>
    replayWithM (cexTop k) (tgtId "i" (k + 1)) 1000000 piEnv == .genuine

/-- Whether `EvalM` runs the top-level loop of `k` iterations and halts at the failing assertion,
    within 60 seconds (`none` when it does not finish in time). -/
private def evalWithin (k : Nat) : IO (Option Bool) :=
  StrataTest.TimeBound.withinMs 60000 fun _ =>
    match (runCoreEval piEnv 1000000 (cexTop k).cfg).1 with
    | .error (.assertFailed arg) => arg.label == "tgt"
    | _ => false

/-- info: some true -/
#guard_msgs in
#eval calleeWithin 10000

/-- info: some true -/
#guard_msgs in
#eval topWithin 10000

/-- info: some true -/
#guard_msgs in
#eval evalWithin 10000

/-- The number of entries of the interpreter store's map after `runCoreEval` runs `ss` from
    `env 0`, when the run ends normally. -/
private def mapSizeAfter (ss : List Statement) : Option Nat :=
  match (runCoreEval piEnv 1000 (.stmts ss (env 0))).1 with
  | .ok c => some (c.getEnv.store.writes : StoreWrites).size
  | .error _ => none

-- A block's names leave the interpreter store's map when the block exits: the map is empty after
-- `{ var x := 1 }`, and holds only `y` (written over the start store) after
-- `{ var x := 1; y := x }`.
#guard mapSizeAfter [.block "B" [initS "x" (int 1)] md] == some 0
#guard mapSizeAfter [.block "B" [initS "x" (int 1), setS "y" (v "x")] md] == some 1

end InterpreterScopeCostTest

end -- meta section
