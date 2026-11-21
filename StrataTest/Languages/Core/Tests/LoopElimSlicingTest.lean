/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import StrataTest.Languages.Core.Tests.CounterexampleTestUtils
meta import Strata.Languages.Core.Counterexample.BackLinkPhases

/-! # loopElim back-link slicing unit tests

Small synthetic Core units exercising the loop-elimination back-link: the loop origins
recovered by the parallel walk; `unloopElimConfig` outside, at and inside an expansion;
the slicing replay (`loopElimSlice`) with a false guard (no cut), a deterministic and a
nondeterministic guard (three slices, mid-loop and exit states from the oracle), a nested
loop; the target before, inside and after the loop; and the chain replay closing gap 1
at iteration 0 and at iteration k, and both gaps (the claim reaches the top ⇒ `Fail`). -/

meta section

namespace LoopElimSlicingTest

open Core Lambda Imperative
open Core.CexTestUtils

private def id (name : String) : CoreIdent := ⟨name, ()⟩
private def tt : Expression.Expr := HasBool.tt (P := Expression)
private def ff : Expression.Expr := HasBool.ff (P := Expression)

private def env (a : Int) (b : Int := 0) : IEnv Expression :=
  .ofStore (fun n =>
      if n == id "a" then some (int a) else if n == id "b" then some (int b) else none) Core.Factory

private def setS (x : String) (e : Expression.Expr) : Statement :=
  .cmd (.cmd (.set (id x) (.det e) md))
private def plus1 (x : String) : Expression.Expr :=
  .app default (.app default intAddOp (v x)) (int 1)
private def lt (x : String) (n : Int) : Expression.Expr :=
  .app default (.app default intLtOp (v x)) (int n)
private def assertS (label : String) (e : Expression.Expr) : Statement :=
  .cmd (.cmd (.assert label e md))
private def aEq (n : Int) : Expression.Expr := .eq default (v "a") (int n)
private def tgtA (n : Int) : Statement := assertS "tgt" (aEq n)
private def tgtId : AssertId Expression := { label := "tgt", md := md }

private def loopS (guard : ExprOrNondet Expression) (body : List Statement) : Statement :=
  .loop guard none [] body md

/-! ## Loop origins and `unloopElimConfig` -/

/-- `loop (a < 3) { a := a + 1 }`. -/
private def countLoop : Statement := loopS (.det (lt "a" 3)) [setS "a" (plus1 "a")]
private def arbLabel : String := "$__loopElim_arbitrary_iter_facts_7"
private def havocBlock : Statement :=
  .block "$__loopElim_havoc_7" [.cmd (.cmd (.set (id "a") .nondet md))] {}
private def assumeGuard : Statement :=
  .cmd (.cmd (.assume "$__loopElimAssume_guard_7" (lt "a" 3) md))
private def assumeNotGuard : Statement :=
  .cmd (.cmd (.assume "$__loopElimAssume_not_guard_7" (lt "a" 3) md))
private def arbBlock : Statement :=
  .block arbLabel [havocBlock, assumeGuard, setS "a" (plus1 "a")] {}
/-- The pass's image of `countLoop` (illustrative of `removeLoop`'s shape). -/
private def expansion : Statement :=
  .ite (.det (lt "a" 3)) [arbBlock, havocBlock, assumeNotGuard] [] {}

private def origins : LoopOrigins := loopOriginsStmts [countLoop, tgtA 0] [expansion, tgtA 0]

-- The parallel walk recovers the source loop of the expansion.
#guard origins.map (·.1) == [arbLabel]
#guard origins.lookup arbLabel == some countLoop

/-- The pass's image of a loop numbered `n` with guard `g` and image body `body'`, as
    `removeLoop` builds it: the arbitrary iteration opens with the havoc block and the guard
    assumption, which is `true` for a nondeterministic guard. -/
private def expansionAt (n : Nat) (g : ExprOrNondet Expression) (body' : List Statement) :
    Statement :=
  let havoc : Statement :=
    .block s!"$__loopElim_havoc_{n}" [.cmd (.cmd (.set (id "a") .nondet md))] {}
  let enter : Expression.Expr := match g with | .det e => e | .nondet => tt
  .ite g [.block s!"$__loopElim_arbitrary_iter_facts_{n}"
      ([havoc, .cmd (.cmd (.assume s!"$__loopElimAssume_guard_{n}" enter md))] ++ body') {},
    havoc] [] {}

-- A nondeterministic loop whose body holds two loops: each body loop is paired with its own
-- expansion, after the havoc block and the `assume true` of the outer iteration.
private def innerLoop (n : Int) : Statement := loopS (.det (lt "a" n)) [setS "a" (plus1 "a")]
private def ndOuter : Statement := loopS .nondet [innerLoop 3, innerLoop 5]
private def ndOuterImage : Statement :=
  expansionAt 1 .nondet
    [expansionAt 2 (.det (lt "a" 3)) [setS "a" (plus1 "a")],
     expansionAt 3 (.det (lt "a" 5)) [setS "a" (plus1 "a")]]
private def ndOrigins : LoopOrigins := loopOriginsStmts [ndOuter] [ndOuterImage]
#guard ndOrigins.map (·.1) == ["$__loopElim_arbitrary_iter_facts_1",
  "$__loopElim_arbitrary_iter_facts_2", "$__loopElim_arbitrary_iter_facts_3"]
#guard ndOrigins.lookup "$__loopElim_arbitrary_iter_facts_2" == some (innerLoop 3)
#guard ndOrigins.lookup "$__loopElim_arbitrary_iter_facts_3" == some (innerLoop 5)

-- Outside expansions: the identity.
#guard match unloopElimConfig origins (.stmts [tgtA 0] (env 1)) with
  | some (.stmts ss _) => ss == [tgtA 0]
  | _ => false
-- At the expansion `if`: the source loop.
#guard match unloopElimConfig origins (.stmts [expansion, tgtA 0] (env 1)) with
  | some (.stmts ss _) => ss == [countLoop, tgtA 0]
  | _ => false
-- Inside the one iteration: the same point of an upstream iteration, continued by the loop.
private def insideIter : IConfig Expression Command :=
  .seq (.block none ⟨(env 0).store, none⟩
      (.seq (.block (some arbLabel) ⟨(env 0).store, none⟩
          (.seq (.stmt (setS "a" (plus1 "a")) (env 1)) []))
        [havocBlock, assumeNotGuard]))
    [tgtA 0]
#guard match unloopElimConfig origins insideIter with
  | some (.seq (.seq (.block none _ (.seq (.stmt s e) [])) [l]) rest) =>
    s == setS "a" (plus1 "a") && l == countLoop && rest == [tgtA 0] &&
      e.store.get (id "a") == some (int 1)
  | _ => false
-- At a havoc block or a guard assumption: no upstream counterpart.
#guard (unloopElimConfig origins
          (.seq (.block none ⟨(env 0).store, none⟩
              (.seq (.block (some arbLabel) ⟨(env 0).store, none⟩
                  (.seq (.stmt havocBlock (env 1)) [assumeGuard])) [havocBlock]))
            [tgtA 0])).isNone
#guard (unloopElimConfig origins
          (.seq (.block none ⟨(env 0).store, none⟩
              (.seq (.block (some arbLabel) ⟨(env 0).store, none⟩
                  (.seq (.stmt assumeGuard (env 1)) [])) [havocBlock]))
            [tgtA 0])).isNone

/-! ## The loop cut rule -/

private def top (a : Int) (oracle : List Expression.Expr) (st : List Statement) :
    CexA Expression Command :=
  { cfg := .stmts st (env a), oracle := oracle }

-- Guard false: no cut; the target after the loop fires on the top slice.
#guard (loopElimSlice noPi tgtId (top 5 [] [countLoop, tgtA 0])).slices.isEmpty
#guard match (loopElimSlice noPi tgtId (top 5 [] [countLoop, tgtA 0])).claim with
  | some (c, _) => isTopLevelAtB [countLoop, tgtA 0] c.cfg
  | none => false

-- Deterministic guard: three slices; the mid-loop state (`a = 1`) and the exit state
-- (`a = 3`) come from the oracle.
private def detRun := loopElimSlice noPi tgtId (top 0 [int 1, int 3] [countLoop, tgtA 0])
#guard detRun.slices.length == 2
#guard match detRun.slices with
  | [_, iter] => valueOf iter.cfg "a" == some (int 1)
  | _ => false
#guard match detRun.claim with
  | some (c, _) => valueOf c.cfg "a" == some (int 3)
  | none => false

-- Nondeterministic guard: the entry choice is drawn (and kept in the pre-loop slice).
private def ndLoop : Statement := loopS .nondet [setS "a" (plus1 "a")]
private def ndRun := loopElimSlice noPi tgtId (top 0 [tt, int 4, int 7] [ndLoop, tgtA 0])
#guard ndRun.slices.length == 2
#guard match ndRun.slices with
  | [pre, iter] => pre.oracle == [tt] && valueOf iter.cfg "a" == some (int 4)
  | _ => false
#guard match ndRun.claim with
  | some (c, _) => valueOf c.cfg "a" == some (int 7)
  | none => false
-- Nondeterministic guard, not entered: no cut.
#guard (loopElimSlice noPi tgtId (top 1 [ff] [ndLoop, tgtA 0])).slices.isEmpty

-- A nested loop: outer entry, inner entry, inner exit, outer exit — four slices and the
-- claim (outer exit state `a = 4`).
private def nested : Statement := loopS .nondet [loopS .nondet [setS "a" (plus1 "a")]]
private def nestedRun :=
  loopElimSlice noPi tgtId (top 0 [tt, int 1, tt, int 2, int 3, int 4] [nested, tgtA 0])
#guard match nestedRun with
  | { slices := [pre, outerIter, innerIter, innerExit], claim := some (c, _) } =>
    valueOf pre.cfg "a" == some (int 0) && pre.oracle == [tt] &&
      valueOf outerIter.cfg "a" == some (int 1) && outerIter.oracle == [tt] &&
      valueOf innerIter.cfg "a" == some (int 2) && innerIter.oracle == [] &&
      valueOf innerExit.cfg "a" == some (int 3) && innerExit.oracle == [] &&
      valueOf c.cfg "a" == some (int 4) && c.oracle == []
  | _ => false

-- An inner loop left by `exit` mid-iteration: `loop * { block L { loop * { a := a + 1;
-- exit L } } }`.  The `exit` leaves the inner loop's iteration, so the inner loop is
-- popped from the active-loop stack; back at the outer loop's head, the outer loop is on
-- top: cut 2 (exit state `a = 3` from the oracle), and the target after the loop fires.
-- Slices: before the outer loop (its guard draw), the outer iteration (mid-loop
-- `a = 1`, the inner guard draw), the inner iteration (mid-loop `a = 2`).
private def exitInner : Statement :=
  loopS .nondet [.block "L" [loopS .nondet [setS "a" (plus1 "a"), .exit "L" md]] md]
private def exitRun :=
  loopElimSlice noPi tgtId (top 0 [tt, int 1, tt, int 2, int 3] [exitInner, tgtA 0])
#guard match exitRun with
  | { slices := [pre, outerIter, innerIter], claim := some (c, _) } =>
    pre.oracle == [tt] && valueOf outerIter.cfg "a" == some (int 1) &&
      outerIter.oracle == [tt] && valueOf innerIter.cfg "a" == some (int 2) &&
      valueOf c.cfg "a" == some (int 3)
  | _ => false

-- The target before the loop (VC1-like): the claim is the top slice, no cut.
#guard match loopElimSlice noPi tgtId (top 0 [int 1, int 3] [tgtA 1, countLoop]) with
  | { slices := [], claim := some (c, _) } => isTopLevelAtB [tgtA 1, countLoop] c.cfg
  | _ => false
-- The target inside the body (VC2-like): the claim is the iteration slice.
private def bodyAssert : Statement := loopS (.det (lt "a" 3)) [tgtA 1, setS "a" (plus1 "a")]
#guard match loopElimSlice noPi tgtId (top 0 [int 2, int 3] [bodyAssert]) with
  | { slices := [_], claim := some (c, _) } => valueOf c.cfg "a" == some (int 2)
  | _ => false

/-! ## Loops ending a nested statement list -/

-- `block B { b := 1; loop (a < 3) { a := a + 1 } }` and the target after the block: the loop
-- is the last statement of the block's list.  Slices: before the loop (`a = 0`, `b = 0`), the
-- iteration (mid-loop `a = 1`, `b = 1`); the claim at the exit state `a = 3`.
private def lastInBlock : Statement := .block "B" [setS "b" (int 1), countLoop] {}
#guard match loopElimSlice noPi tgtId (top 0 [int 1, int 3] [lastInBlock, tgtA 0]) with
  | { slices := [pre, iter], claim := some (c, _) } =>
    valueOf pre.cfg "a" == some (int 0) && valueOf pre.cfg "b" == some (int 0) &&
      valueOf iter.cfg "a" == some (int 1) && valueOf iter.cfg "b" == some (int 1) &&
      valueOf c.cfg "a" == some (int 3) && valueOf c.cfg "b" == some (int 1) && c.oracle == []
  | _ => false

-- The nested loop `nested` (its inner loop the last statement of the outer body) as the last
-- statement of `block B { b := 1; nested }`: the four slices and the claim of `nestedRun`, under
-- the block.
private def nestedLastInBlock : Statement := .block "B" [setS "b" (int 1), nested] {}
#guard match loopElimSlice noPi tgtId
    (top 0 [tt, int 1, tt, int 2, int 3, int 4] [nestedLastInBlock, tgtA 0]) with
  | { slices := [pre, outerIter, innerIter, innerExit], claim := some (c, _) } =>
    valueOf pre.cfg "a" == some (int 0) && pre.oracle == [tt] &&
      valueOf outerIter.cfg "a" == some (int 1) && outerIter.oracle == [tt] &&
      valueOf innerIter.cfg "a" == some (int 2) && innerIter.oracle == [] &&
      valueOf innerExit.cfg "a" == some (int 3) && innerExit.oracle == [] &&
      valueOf c.cfg "a" == some (int 4) && valueOf c.cfg "b" == some (int 1) && c.oracle == []
  | _ => false

/-! ## The back-link: closing the gaps -/

/-- The downstream outcome: the top of the downstream unit, with the mid-loop and exit
    states of the counterexample in the oracle. -/
private def incoming (aMid aExit : Int) : BackLinkOutcome Expression Command :=
  ⟨[{ cfg := .stmts [expansion, tgtA 0] (env 0), oracle := [int aMid, int aExit] }], none⟩

-- Mid-loop state reached at iteration 0 (`a = 0`) and exit state reached (`a = 3`): both
-- gaps close, the claim reaches the top (`Fail`).
#guard ((loopElimBackLink noPi tgtId origins).lift [countLoop, tgtA 0] (incoming 0 3)).isFail
-- Mid-loop state reached at iteration 2 (`a = 2`).
#guard ((loopElimBackLink noPi tgtId origins).lift [countLoop, tgtA 0] (incoming 2 3)).isFail
-- An unreachable mid-loop state (`a = 5`) and exit state (`a = 4`), for the target
-- `a == 3`, which the real run (exiting at `a = 3`) never fails: the gaps stay open; the
-- exit slice's claim is inner, not `Fail`.
private def incoming3 (aMid aExit : Int) : BackLinkOutcome Expression Command :=
  ⟨[{ cfg := .stmts [expansion, tgtA 3] (env 0), oracle := [int aMid, int aExit] }], none⟩
private def openRun := (loopElimBackLink noPi tgtId origins).lift [countLoop, tgtA 3]
    (incoming3 5 4)
#guard openRun.isFail == false
#guard match openRun with
  | { slices := [s0], claim := some (c, _) } =>
    valueOf s0.cfg "a" == some (int 0) && s0.oracle == [int 5, int 4] &&
      valueOf c.cfg "a" == some (int 5) && c.oracle == []
  | _ => false

end LoopElimSlicingTest

end -- meta section
