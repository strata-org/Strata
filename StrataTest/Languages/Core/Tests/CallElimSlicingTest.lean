/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import StrataTest.Languages.Core.Tests.CounterexampleTestUtils
meta import Strata.Languages.Core.Counterexample.BackLinkPhases
meta import Strata.Languages.Core
import StrataDDM.Integration.Lean.HashCommands

/-! # callElim back-link slicing unit tests

Small synthetic Core units exercising the call-elimination back-link: mapping a
downstream configuration upstream (`uncallElimConfig`) outside and inside an
expansion; the slicing replay (`callElimSlice`) cutting at an eliminated call (at the
top level, inside an `ite` branch, once per loop iteration); a failing callee
precondition claimed at the call entry; a call the pass did not eliminate executed for
real; the per-slice processing of a downstream chain; the real call of an eliminated call
whose callee returns the downstream outputs, through a deterministic callee and through a
callee whose choices aim at those outputs; and, end to end, a counterexample whose callee
must choose the downstream output. -/

meta section

namespace CallElimSlicingTest

open Core Lambda Imperative
open Core.CexTestUtils
open Core.CallElim (CallOrigin)

private def id (name : String) : CoreIdent := ⟨name, ()⟩
/-- A store defining `a` and `y` (and, optionally, the fresh temporary `tmp_x`). -/
private def env (a y : Int) (tmp : Option Int := none) : IEnv Expression :=
  .ofStore (fun n =>
      if n == id "a" then some (int a) else if n == id "y" then some (int y)
      else if n == id "tmp_x" then tmp.map int else none) Core.Factory

/-! ## The callee and the call site -/

/-- `callee(x : int, out r : int) requires [pre]: x == 3 { r := x; }` when `withPre`,
    else without the precondition. -/
private def calleeProc (withPre : Bool := false) : Procedure := {
  header := { name := id "callee", typeArgs := [],
              inputs := [(id "x", (.int : Lambda.LMonoTy))],
              outputs := [(id "r", (.int : Lambda.LMonoTy))] }
  spec := { preconditions :=
              if withPre then [("pre", { expr := .eq default (v "x") (int 3), attr := .Default })]
              else [],
            postconditions := [] }
  body := .structured
    [ .cmd (.cmd (.set (id "r") (.det (.fvar default (id "x") (some .int))) md)) ] false }

/-- `nondetCallee(x : int, out r : int) { var t : int := *; r := x; }`: draws one value,
    then is deterministic. -/
private def nondetCalleeProc : Procedure := {
  header := { name := id "callee", typeArgs := [],
              inputs := [(id "x", (.int : Lambda.LMonoTy))],
              outputs := [(id "r", (.int : Lambda.LMonoTy))] }
  spec := { preconditions := [], postconditions := [] }
  body := .structured
    [ .cmd (.cmd (.init (id "t") (.forAll [] .int) .nondet md)),
      .cmd (.cmd (.set (id "r") (.det (.fvar default (id "x") (some .int))) md)) ] false }

/-- The procedure table resolving `callee` to `p`. -/
private def piOf (p : Procedure) : String → Option Procedure :=
  fun n => if n == "callee" then some p else none

/-- `call callee(a; out y)`. -/
private def callS : Statement :=
  .cmd (CmdExt.call "callee" none [.inArg (v "a"), .outArg (id "y")] md)
private def tgtY : Statement := .cmd (.cmd (.assert "tgtY" (.eq default (v "y") (int 0)) md))
private def tgtIdY : AssertId Expression := { label := "tgtY", md := md }
private def preId : AssertId Expression := { label := "pre", md := #[] }

/-- The expansion the pass put in place of `callS` (illustrative shape:
    `init tmp_x := a; havoc y; assume post`). -/
private def initTmp : Statement :=
  .cmd (.cmd (.init (id "tmp_x") (.forAll [] .int) (.det (v "a")) md))
private def havocY : Statement := .cmd (.cmd (.set (id "y") .nondet md))
private def assumePost : Statement :=
  .cmd (.cmd (.assume "callElimAssume_post" (.eq default (v "y") (v "tmp_x")) md))
private def expansion : List Statement := [initTmp, havocY, assumePost]

private def origin : CallOrigin := {
  procName := "callee", callee := calleeProc, args := [v "a"], lhs := [id "y"],
  inputParams := [id "x"], outputParams := [id "r"], typeArgs := [],
  freshNames := [id "tmp_x"], source := callS, expansion := expansion,
  havocStart := 1, sourceRest := [tgtY] }

private def origins : List CallOrigin := [origin]

/-! ## `uncallElimConfig` -/

/-- The statements a configuration still executes at its innermost level followed by
    its enclosing continuation (enough to identify the program point here). -/
private def shape : IConfig Expression Command → String
  | .stmts ss _ => s!"stmts {ss.length}"
  | .stmt s _ => if s == callS then "stmt call" else "stmt"
  | .seq (.stmt s _) rest => s!"seq (stmt{if s == callS then " call" else ""}) {rest.length}"
  | .seq (.terminal _) rest => s!"seq terminal {rest.length}"
  | .seq _ rest => s!"seq {rest.length}"
  | .terminal _ => "terminal"
  | .exiting _ _ => "exiting"
  | .block _ _ _ => "block"
  | .seqs _ _ => "seqs"

-- Outside expansions: the identity (with the fresh temporaries dropped).
#guard match uncallElimConfig origins (.stmts [tgtY] (env 1 2)) with
  | some (.stmts ss e) => ss == [tgtY] && e.store.get (id "y") == some (int 2)
  | _ => false

-- A top-level downstream start maps to the top of the source unit.
#guard match uncallElimConfig origins (.stmts (expansion ++ [tgtY]) (env 1 2)) with
  | some (.stmts ss _) => ss == [callS, tgtY]
  | _ => false

-- Inside the expansion, before the havocs: upstream is *at* the call; `tmp_x` is dropped.
#guard match uncallElimConfig origins
    (.seq (.stmt havocY (env 1 2 (some 1))) [assumePost, tgtY]) with
  | some c => shape c == "seq (stmt call) 1" && valueOf c "tmp_x" == none
  | none => false

-- Inside the expansion, after the havocs: upstream is right *after* the call, and the
-- lhs keeps the value the downstream havoc drew.
#guard match uncallElimConfig origins (.seq (.stmt assumePost (env 1 7 (some 1))) [tgtY]) with
  | some c => shape c == "seq terminal 1" && valueOf c "y" == some (int 7)
  | none => false

/-- A second call site with two outputs, so that a start between its havocs exists. -/
private def havocZ : Statement := .cmd (.cmd (.set (id "z") .nondet md))
private def origin2 : CallOrigin :=
  { origin with lhs := [id "y", id "z"], expansion := [initTmp, havocY, havocZ],
                source := .cmd (CmdExt.call "callee2" none [] md) }

-- Between the havocs there is no upstream counterpart: the slice is dropped.
#guard (uncallElimConfig [origin2] (.seq (.stmt havocZ (env 1 7)) [tgtY])).isNone

/-- A call site whose expansion ends with its havoc (no postcondition), in the source unit
    `[callS, havocY, tgtY]`: downstream `[initTmp, havocY, havocY, tgtY]`, where the
    second `havocY` is the source's own statement. -/
private def origin3 : CallOrigin :=
  { origin with expansion := [initTmp, havocY], sourceRest := [havocY, tgtY] }

-- The source `havoc y` looks like the expansion's last statement, but it is continued by
-- `[tgtY]`, not by the call's source continuation `[havocY, tgtY]`: not recognized as
-- inside the expansion, it maps to itself.
#guard match uncallElimConfig [origin3] (.seq (.stmt havocY (env 1 7)) [tgtY]) with
  | some (.seq (.stmt s _) rest) => s == havocY && rest == [tgtY]
  | _ => false
-- The expansion's own havoc (continued by the source continuation): at the call.
#guard match uncallElimConfig [origin3] (.seq (.stmt havocY (env 1 7 (some 1))) [havocY, tgtY]) with
  | some c => shape c == "seq (stmt call) 2"
  | none => false
-- The whole downstream unit maps to the source unit.
#guard match uncallElimConfig [origin3] (.stmts [initTmp, havocY, havocY, tgtY] (env 1 7)) with
  | some (.stmts ss _) => ss == [callS, havocY, tgtY]
  | _ => false
-- A lone source `havoc y`, equal to an expansion statement and mentioning no fresh
-- variable, is ambiguous: no upstream image.
#guard (uncallElimConfig [origin3] (.stmt havocY (env 1 7))).isNone

/-! ## The slicing replay -/

/-- A counterexample at the top of `st` (by default `[callS, tgtY]`), with `a` set and
    `y = 0`, and the given oracle. -/
private def top (a : Int) (oracle : List Expression.Expr) (st : List Statement := [callS, tgtY]) :
    CexA Expression Command :=
  { cfg := .stmts st (env a 0), oracle := oracle }

/-- A chain summary: the `shape` of each unconfirmed slice and, for the claim, its `shape`,
    the value of `y` in its store, its fuel, and its oracle. -/
private def summary (slices : List (CexA Expression Command))
    (claim : Option (CexA Expression Command × Nat)) :
    List String × Option (String × Option Expression.Expr × Nat × List Expression.Expr) :=
  (slices.map (shape ·.cfg), claim.map fun (c, f) => (shape c.cfg, valueOf c.cfg "y", f, c.oracle))

/-- The `summary` of a slicing result. -/
private def sliceSummary (r : SliceResult) := summary r.slices r.claim

/-- The `summary` of a back-link outcome. -/
private def outSummary (o : BackLinkOutcome Expression Command) := summary o.slices o.claim

-- One eliminated call whose callee does not return the downstream output (`r = a = 1`, the
-- output `5`): cut into two slices; the second starts right after the call with the lhs set
-- from the oracle, and fires the target (`y = 5 ≠ 0`).
#guard sliceSummary (callElimSlice (piOf (calleeProc)) tgtIdY origins (top 1 [int 5])) ==
  (["stmts 2"], some ("seq terminal 1", some (int 5), replayFuelGuess, []))
-- With `y = 0` from the oracle the target does not fire: two unconfirmed slices.
#guard sliceSummary (callElimSlice (piOf (calleeProc)) tgtIdY origins (top 1 [int 0])) ==
  (["stmts 2", "seq terminal 1"], none)

-- A call inside an `ite` branch: the cut takes the continuation config (inside the
-- branch's block), and the target after the `ite` fires on the second slice.
private def iteUnit : List Statement :=
  [.ite (.det (HasBool.tt (P := Expression))) [callS] [] md, tgtY]
#guard sliceSummary (callElimSlice (piOf (calleeProc)) tgtIdY origins (top 1 [int 5] iteUnit)) ==
  (["stmts 2"], some ("seq 1", some (int 5), replayFuelGuess, []))

-- A call inside a loop (nondeterministic guard): one cut per iteration.  Oracle: enter,
-- output 4, enter, output 6, exit — two iterations, three slices, the last one claims.
private def loopUnit : List Statement := [.loop .nondet none [] [callS] md, tgtY]
private def tt : Expression.Expr := HasBool.tt (P := Expression)
private def ff : Expression.Expr := HasBool.ff (P := Expression)
#guard sliceSummary (callElimSlice (piOf (calleeProc)) tgtIdY origins
          (top 1 [tt, int 4, tt, int 6, ff] loopUnit)) ==
  (["stmts 2", "seq 1"], some ("seq 1", some (int 6), replayFuelGuess, [ff]))

-- A failing precondition: claimed at the call entry, before any cut.
#guard sliceSummary (callElimSlice (piOf (calleeProc true)) preId origins (top 1 [int 5])) ==
  ([], some ("stmts 2", some (int 0), replayFuelGuess, []))
#guard match (callElimSlice (piOf (calleeProc true)) preId origins (top 1 [int 5])).claim with
  | some (c, _) => isTopLevelAtB [callS, tgtY] c.cfg
  | none => false
-- A passing precondition (`a = 3`): no claim for it, the call is cut.
#guard sliceSummary (callElimSlice (piOf (calleeProc true)) preId origins (top 3 [int 5])) ==
  (["stmts 2", "seq terminal 1"], none)

-- A call the pass did not eliminate (no origin) is executed for real: `y := a = 1`
-- fires the target on the top slice, with no cut.
#guard sliceSummary (callElimSlice (piOf (calleeProc)) tgtIdY [] (top 1 [])) ==
  ([], some ("stmts 2", some (int 0), replayFuelGuess, []))
#guard match (callElimSlice (piOf (calleeProc)) tgtIdY [] (top 1 [])).claim with
  | some (c, _) => isTopLevelAtB [callS, tgtY] c.cfg
  | none => false

/-! ## Processing a downstream chain -/

-- Two downstream slices, each sliced upstream: the head (at the top) and a second slice
-- starting at the top of the downstream unit again with its own oracle; each is cut at
-- the call, giving four upstream slices and no claim (`y = 0` both times).
private def dsTop : CexA Expression Command :=
  { cfg := .stmts (expansion ++ [tgtY]) (env 1 0), oracle := [int 0] }
#guard outSummary (callElimConcatPieces (piOf (calleeProc)) tgtIdY origins [] [dsTop, dsTop]) ==
  (["stmts 2", "seq terminal 1", "stmts 2", "seq terminal 1"], none)
-- A downstream slice starting between havocs is dropped, never invented.
private def dsMid : CexA Expression Command :=
  { cfg := .seq (.stmt havocZ (env 1 7)) [tgtY], oracle := [] }
#guard outSummary (callElimConcatPieces (piOf (calleeProc)) tgtIdY [origin2] [] [dsMid]) ==
  ([], none)

/-! ## The back-link: chain replay through the real call -/

/-- The downstream outcome: the top of the downstream unit with the havoc drawing `y`. -/
private def incoming (a y : Int) : BackLinkOutcome Expression Command :=
  ⟨[{ cfg := .stmts (expansion ++ [tgtY]) (env a 0), oracle := [int y] }], none⟩

-- Deterministic callee, downstream output = the real output (`y = a = 3`): the slicer runs
-- the real call, no gap opens, and the claim is at the top (`Fail`).
#guard sliceSummary (callElimSlice (piOf (calleeProc)) tgtIdY origins (top 3 [int 3])) ==
  ([], some ("stmts 2", some (int 0), replayFuelGuess, []))
#guard outSummary ((callElimBackLink (piOf (calleeProc)) tgtIdY origins).lift [callS, tgtY]
          (incoming 3 3)) == ([], some ("stmts 2", some (int 0), replayFuelGuess, []))
-- Downstream output ≠ real output, target `y == 3` (fails downstream at `y = 5`, holds
-- upstream at the real `y = 3`): the gap stays open, the claim is inner, not `Fail`.
private def tgtY3 : Statement := .cmd (.cmd (.assert "tgtY3" (.eq default (v "y") (int 3)) md))
private def tgtIdY3 : AssertId Expression := { label := "tgtY3", md := md }
private def incoming3 (a y : Int) : BackLinkOutcome Expression Command :=
  ⟨[{ cfg := .stmts (expansion ++ [tgtY3]) (env a 0), oracle := [int y] }], none⟩
#guard outSummary ((callElimBackLink (piOf (calleeProc)) tgtIdY3 origins).lift [callS, tgtY3]
          (incoming3 3 5)) ==
  (["stmts 2"], some ("seq terminal 1", some (int 5), replayFuelGuess, []))
-- A failing callee precondition is a `Fail` for the upstream precondition id.
#guard outSummary ((callElimBackLink (piOf (calleeProc true)) preId origins).lift [callS, tgtY]
          (incoming 1 5)) == ([], some ("stmts 2", some (int 0), replayFuelGuess, []))

-- A callee with internal nondeterminism: its draw takes the downstream output (`3`, an
-- `int`), the real call returns `r := x = 3`, and the claim at the top records the draw.
#guard outSummary ((callElimBackLink (piOf nondetCalleeProc) tgtIdY origins).lift [callS, tgtY]
          (incoming 3 3)) ==
  ([], some ("stmts 2", some (int 0), replayFuelGuess, [int 3]))

end CallElimSlicingTest

end -- meta section
