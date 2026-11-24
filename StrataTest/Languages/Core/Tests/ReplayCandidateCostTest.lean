/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core.Counterexample.BackLinkChainReplay

/-! # Cost of re-validating a counterexample through a loop

`replayCandidate` re-validates a claim with two replays of the program. The test re-validates
a claim behind a loop of `n` iterations whose guard reads a variable the body does not write,
and bounds the cost in heartbeats (`IO.getNumHeartbeats`, deterministic: the replay runs on this
thread). The cost must grow about linearly in `n`: at 20 iterations a replay linear in `n` costs
about 0.07M heartbeats, and one whose cost doubles per iteration costs over 4M. The bound is
1M. -/

meta section

namespace Core.ReplayCandidateCostTest

open Core _root_.Lambda Imperative

private def int (n : Int) : Expression.Expr := .intConst default n
private def v (x : String) : Expression.Expr := .fvar default ⟨x, ()⟩ (some .int)
private def md : MetaData Expression := #[]

/-- `a := 0; n := k; while (a < n) { a := a + 1 }; assert [end]: a == -1`. -/
private def program (k : Int) : List Statement :=
  [.cmd (.cmd (.set ⟨"a", ()⟩ (.det (int 0)) md)),
   .cmd (.cmd (.set ⟨"n", ()⟩ (.det (int k)) md)),
   .loop (.det (.app default (.app default intLtOp (v "a")) (v "n"))) none []
     [.cmd (.cmd (.set ⟨"a", ()⟩
       (.det (.app default (.app default intAddOp (v "a")) (int 1))) md))] md,
   .cmd (.cmd (.assert "end" (.eq default (v "a") (int (-1))) md))]

private def target : AssertId Expression := { label := "end", md := md }

private def env0 : IEnv Expression :=
  .ofStore (fun x => if x.name == "a" || x.name == "n" then some (int 0) else none) Core.Factory

/-- Bound on the re-validation cost in heartbeats; see the module doc. -/
private def maxHeartbeats : Nat := 1000000

/-- Whether the claim behind `k` iterations re-validates, and whether its cost is within
    `maxHeartbeats`.  The iteration count is read back from an `IO.Ref`, so the program is known
    only at run time and its replay runs between the two heartbeat readings. -/
private def check (k : Nat) : IO Unit := do
  let input ← IO.mkRef k
  let n ← input.get
  let h0 ← IO.getNumHeartbeats
  let ok ← IO.lazyPure fun _ =>
    (replayCandidate (fun _ => none) target (fun _ _ _ => none)
      { cfg := .stmts (program n) env0 } replayFuelGuess).isSome
  IO.println s!"re-validated: {ok}"
  let h1 ← IO.getNumHeartbeats
  IO.println s!"within bound: {decide (h1 - h0 ≤ maxHeartbeats)}"

/--
info: re-validated: true
within bound: true
-/
#guard_msgs in
#eval check 20

end Core.ReplayCandidateCostTest

end
