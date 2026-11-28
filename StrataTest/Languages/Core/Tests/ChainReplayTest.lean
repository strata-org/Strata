/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import StrataTest.Languages.Core.Tests.CounterexampleTestUtils
meta import Strata.Languages.Core.Counterexample.BackLinkChainReplay

/-! # Chain replay (`Core.chainWalk` / `Core.chainReplayClaim`) unit tests

Small synthetic Core programs exercising slice merging: a merge when replay from one
slice reaches the next slice's start with stores agreeing on the read set; no merge
when they differ on a variable read later; the target firing first; fuel exhaustion;
a pending `.call` in the continuation (read set = the call's actuals); and a claim
the final re-validation rejects. -/

meta section

namespace ChainReplayTest

open Core Lambda Imperative
open Core.CexTestUtils

private def id (name : String) : CoreIdent := ⟨name, ()⟩
private def setS (x : String) (n : Int) : Statement :=
  .cmd (.cmd (.set (id x) (.det (int n)) md))
/-- Target assert `a == rhs`. -/
private def tgtA (rhs : Int) : Statement :=
  .cmd (.cmd (.assert "tgt" (.eq default (v "a") (int rhs)) md))
private def tgtId : AssertId Expression :=
  { label := "tgt", md := md }

/-- A store defining `a`, `b`, `c`, `y` with the given values. -/
private def env (a b c : Int) (y : Int := 0) : IEnv Expression :=
  .ofStore (fun n =>
      if n == id "a" then some (int a) else if n == id "b" then some (int b)
      else if n == id "c" then some (int c) else if n == id "y" then some (int y) else none)
      Core.Factory

/-- A chain walk's result as a back-link outcome. -/
private def walkOut
    (w : List (CexA Expression Command) × Option (CexA Expression Command × Nat)) :
    BackLinkOutcome Expression Command := ⟨w.1, w.2⟩

/-- The program `c := 7; b := 2; assert tgt (a == rhs)`, and its tail after the
    first statement. -/
private def prog (rhs : Int) : List Statement := [setS "c" 7, setS "b" 2, tgtA rhs]
private def tail (rhs : Int) : List Statement := [setS "b" 2, tgtA rhs]

private def s0 (rhs : Int) : CexA Expression Command :=
  { cfg := .stmts (prog rhs) (env 1 0 0), oracle := [] }

/-! ### Merge: s₁ is the claim, reached from s₀ ⇒ single top claim (`isFail`) -/

-- s₁ agrees with the post-step store of s₀ everywhere (`c = 7`).
private def s1Same (rhs : Int) : CexA Expression Command :=
  { cfg := .stmts (tail rhs) (env 1 0 7), oracle := [] }

-- The merged claim starts at s₀'s configuration (the top of `prog`); its fuel is the sum of
-- the walk's fuel and the claim's fuel.
#guard summary (walkOut (chainWalk noPi tgtId noDefaults replayFuelGuess [s0 0]
          (some (s1Same 0, replayFuelGuess)))) ==
  ([], some (some (prog 0), 2 * replayFuelGuess, []))

/-! ### Merge of two unconfirmed slices (no claim; target never fires) -/

#guard summary (walkOut (chainWalk noPi tgtId noDefaults replayFuelGuess [s0 1, s1Same 1]
          none)) == ([some (prog 1)], none)

/-! ### Store differs only on a variable never read later (`c`) ⇒ still merges -/

private def s1DiffC (rhs : Int) : CexA Expression Command :=
  { cfg := .stmts (tail rhs) (env 1 0 99), oracle := [] }

#guard IConfig.readVars (s1DiffC 0).cfg == [id "a", id "b"]
#guard summary (walkOut (chainWalk noPi tgtId noDefaults replayFuelGuess [s0 0]
          (some (s1DiffC 0, replayFuelGuess)))) ==
  ([], some (some (prog 0), 2 * replayFuelGuess, []))
#guard summary (walkOut (chainWalk noPi tgtId noDefaults replayFuelGuess [s0 1, s1DiffC 1]
          none)) == ([some (prog 1)], none)

/-! ### Store differs on a variable read later (`a`) ⇒ no merge -/

private def s1DiffA (rhs : Int) : CexA Expression Command :=
  { cfg := .stmts (tail rhs) (env 5 0 7), oracle := [] }

-- Unconfirmed pair: no merge, so s₀ is kept unconfirmed; s₁ (where `a = 5`) then
-- fires `a == 1` on its own, so the claim starts at s₁, not at s₀.
#guard summary (walkOut (chainWalk noPi tgtId noDefaults replayFuelGuess [s0 1, s1DiffA 1]
          none)) == ([some (prog 1)], some (some (tail 1), replayFuelGuess, []))
-- With s₁ as the claim: no merge, s₀ stays unconfirmed ⇒ not `isFail`.
#guard (walkOut (chainWalk noPi tgtId noDefaults replayFuelGuess [s0 1]
          (some (s1DiffA 1, replayFuelGuess)))).isFail == false
#guard summary (walkOut (chainWalk noPi tgtId noDefaults replayFuelGuess [s0 1]
          (some (s1DiffA 1, replayFuelGuess)))) ==
  ([some (prog 1)], some (some (tail 1), replayFuelGuess, []))

/-! ### Target fires before the next slice ⇒ current slice is the claim -/

private def earlyProg : List Statement := [tgtA 0, setS "c" 7, setS "b" 2]
private def early : CexA Expression Command :=
  { cfg := .stmts earlyProg (env 1 0 0), oracle := [] }
private def later : CexA Expression Command :=
  { cfg := .stmts [setS "b" 2] (env 1 0 7), oracle := [] }

#guard summary (walkOut (chainWalk noPi tgtId noDefaults replayFuelGuess [early, later]
          none)) == ([], some (some earlyProg, replayFuelGuess, []))

/-! ### Fuel exhausted on a slice ⇒ kept unconfirmed, the walk moves on -/

/-- A per-attempt step budget too small for `long` to reach `last`, but enough for
    `last` to fire its target.  Pinned: this test is about fuel exhaustion. -/
private def smallFuel : Nat := 3

private def long : CexA Expression Command :=
  { cfg := .stmts [setS "c" 1, setS "c" 2, setS "c" 3, setS "c" 4, tgtA 0] (env 1 0 0),
    oracle := [] }
private def last : CexA Expression Command :=
  { cfg := .stmts [tgtA 0] (env 1 0 4), oracle := [] }

-- At `smallFuel`, `long` is stuck (kept), `last` fires and becomes the claim.
#guard summary (walkOut (chainWalk noPi tgtId noDefaults smallFuel [long, last] none)) ==
  ([stmtsOf long.cfg], some (some [tgtA 0], smallFuel, []))
-- At the guessed fuel, `long` reaches `last` and they merge into a single claim.
#guard summary (walkOut (chainWalk noPi tgtId noDefaults replayFuelGuess [long, last]
          none)) == ([], some (stmtsOf long.cfg, replayFuelGuess, []))

/-! ### A pending `.call` in the continuation -/

/-- `callee(x : int, out r : int) { r := x; }` — reads only its input. -/
private def calleeProc : Procedure := {
  header := { name := id "callee", typeArgs := [],
              inputs := [(id "x", (.int : Lambda.LMonoTy))],
              outputs := [(id "r", (.int : Lambda.LMonoTy))] }
  spec := { preconditions := [], postconditions := [] }
  body := .structured
    [ .cmd (.cmd (.set (id "r") (.det (.fvar default (id "x") (some .int))) md)) ] false }

private def piCallee : String → Option Procedure :=
  fun n => if n == "callee" then some calleeProc else none

/-- `call callee(a; out y)`. -/
private def callS : Statement :=
  .cmd (CmdExt.call "callee" none [.inArg (v "a"), .outArg (id "y")] md)
private def tgtY : Statement := .cmd (.cmd (.assert "tgtY" (.eq default (v "y") (int 0)) md))
private def tgtIdY : AssertId Expression := { label := "tgtY", md := md }

-- The read set of a pending call is its actuals: input `a`, write-back target `y`.
#guard IConfig.readVars (.stmts [callS] (env 1 0 0)) == [id "a", id "y"]
#guard IConfig.readVars (.stmts [callS, tgtY] (env 1 0 0)) == [id "a", id "y", id "y"]

private def cs0 : CexA Expression Command :=
  { cfg := .stmts [setS "c" 7, callS, tgtY] (env 1 0 0), oracle := [] }
-- Differs from the post-step store only on the unrelated caller variable `c`.
private def cs1 : CexA Expression Command :=
  { cfg := .stmts [callS, tgtY] (env 1 0 42), oracle := [] }

#guard summary (walkOut (chainWalk piCallee tgtIdY noDefaults replayFuelGuess [cs0]
          (some (cs1, replayFuelGuess)))) ==
  ([], some (stmtsOf cs0.cfg, 2 * replayFuelGuess, []))
#guard summary (walkOut (chainWalk piCallee tgtIdY noDefaults replayFuelGuess [cs0, cs1]
          none)) == ([], some (stmtsOf cs0.cfg, replayFuelGuess, []))

/-! ### Failed re-check: the walk's proposal does not re-validate ⇒ no claim -/

/-- The claim slice `assert a == 1` at `a = 1` does not actually fail, but the walk
    trusts it on merging.  `chainReplayClaim` re-validates and rejects it.  `stmts`
    is `[]`, so the proposal is strictly inside it. -/
private def bogusClaim : CexA Expression Command :=
  { cfg := .stmts (tail 1) (env 1 0 7), oracle := [] }

#guard summary (walkOut (chainWalk noPi tgtId noDefaults replayFuelGuess [s0 1]
          (some (bogusClaim, replayFuelGuess)))) ==
  ([], some (some (prog 1), 2 * replayFuelGuess, []))
#guard (chainReplayClaim noPi tgtId noDefaults []
          ⟨[s0 1], some (bogusClaim, replayFuelGuess)⟩).isNone
-- Contrast: a real failing claim re-validates.
#guard summary ⟨[], chainReplayClaim noPi tgtId noDefaults []
          ⟨[s0 0], some (s1Same 0, replayFuelGuess)⟩⟩ ==
  ([], some (some (prog 0), 2 * replayFuelGuess, []))

end ChainReplayTest

end -- meta section
