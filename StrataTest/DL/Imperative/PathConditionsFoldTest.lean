/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.DL.Imperative.PureExpr
meta import Strata.DL.Imperative.EvalContext
meta import Strata.DL.Imperative.PathConditionsFold

meta section

/-! # Tests for the incremental `PathConditions` fold

Exercises the generic engine with a toy backend: the checkpoint is
the count of entries processed so far, and each frame's output is the list of
entry labels it processed. Covers the three `advance` shapes:

* **extension** — the target extends the current top frame;
* **new frame** — the target opens `PathCondition`s above the current ones;
* **rewind** — the target diverges, so the engine pops to the shared prefix
  (restoring the checkpoint) and reprocesses only the divergent tail. -/

namespace PathConditionsFoldTest
open Imperative Imperative.PathConditions

---------------------------------------------------------------------

/-- A minimal `PureExpr`: expressions and types are trivial; entries are
    distinguished by their labels alone. -/
abbrev ToyPureExpr : PureExpr :=
  { Ident := String,
    EqIdent := instDecidableEqString,
    Expr := Unit,
    Ty := Unit,
    ExprMetadata := Unit,
    TyEnv := Unit,
    TyContext := Unit,
    Factory := Unit,
    eval := fun _ _ e => some e }

/-- An `.assumption` entry with the given label; the expression is trivial
    (`ToyPureExpr.Expr = Unit`), so entries are distinguished by label. -/
def mkAssumption (label : String) : PathConditionEntry ToyPureExpr :=
  .assumption label ()

/-- The toy backend: the checkpoint counts processed entries; the frame
    output records the labels processed into that frame. -/
def toyBackend : Fold String Nat (List String) ToyPureExpr where
  stepEntry := fun n out e => .ok (n + 1, out ++ [e.name])
  emptyOutput := []

/-- The recorded labels, oldest frame first (for readable assertions). -/
def frameLabels (st : FoldState Nat (List String) ToyPureExpr) : List (List String) :=
  st.frames.reverse.map (·.output)

/-- Advance a fresh state (checkpoint `0`, no frames) over `target`. -/
def advanceFromInit (target : PathConditions ToyPureExpr) :
    Except String (FoldState Nat (List String) ToyPureExpr) :=
  (toyBackend.advance target).exec (FoldState.init 0)

/-- Advance the state produced by a previous `advanceFromInit`/`advanceFrom`
    over `target`, propagating its failure if there was one. -/
def advanceFrom (st : Except String (FoldState Nat (List String) ToyPureExpr))
    (target : PathConditions ToyPureExpr) :
    Except String (FoldState Nat (List String) ToyPureExpr) := do
  (toyBackend.advance target).exec (← st)

---------------------------------------------------------------------

/-! ## Initial fill: all `PathCondition`s are new -/

/-- The target `[[a], [b, c]]` (oldest first) yields two frames with those
    labels, and a checkpoint of 3 processed entries. -/
example : (advanceFromInit [[mkAssumption "a"], [mkAssumption "b", mkAssumption "c"]]).toOption.map frameLabels
    = some [["a"], ["b", "c"]] := by native_decide

example : (advanceFromInit [[mkAssumption "a"], [mkAssumption "b", mkAssumption "c"]]).toOption.map (·.current)
    = some 3 := by native_decide

/-! ## Extension: the target grows the top frame and opens a new one -/

def st₁ := advanceFromInit [[mkAssumption "a"], [mkAssumption "b"]]
def st₂ := advanceFrom st₁ [[mkAssumption "a"], [mkAssumption "b", mkAssumption "c"], [mkAssumption "d"]]

/-- The shared prefix `[a]`/`[b]` is kept; only `c` and the new frame `[d]`
    are processed. -/
example : st₂.toOption.map frameLabels = some [["a"], ["b", "c"], ["d"]] := by
  native_decide

/-- The checkpoint counts every entry of the target exactly once — the same
    value a from-scratch fold of the target would give. -/
example : st₂.toOption.map (·.current) = some 4 := by native_decide

/-! ## Rewind: the target diverges above a shared prefix -/

/-- Descend into a "branch" `[c]`, then switch to the sibling `[c']`. -/
def stThen := advanceFromInit [[mkAssumption "a"], [mkAssumption "b"], [mkAssumption "c"]]
def stElse := advanceFrom stThen [[mkAssumption "a"], [mkAssumption "b"], [mkAssumption "c'"]]

/-- The divergent frame `[c]` is popped and `[c']` is processed fresh;
    the shared `[a]`/`[b]` frames survive untouched. -/
example : stElse.toOption.map frameLabels = some [["a"], ["b"], ["c'"]] := by
  native_decide

/-- The rewind restored the checkpoint to the branch point (2 entries) before
    processing `c'`: the result is 3, as a from-scratch fold would give —
    *not* 4, which would mean the popped `c` step leaked into the state. -/
example : stElse.toOption.map (·.current) = some 3 := by native_decide

/-! ## Rewind to fewer frames: target above a descended branch -/

/-- The next target has fewer `PathCondition`s than the state has frames
    (e.g. the next obligation sits above a branch a previous target descended
    into): deeper frames are popped, nothing is reprocessed. -/
def stShallow := advanceFrom stThen [[mkAssumption "a"], [mkAssumption "b"]]

example : stShallow.toOption.map frameLabels = some [["a"], ["b"]] := by
  native_decide

example : stShallow.toOption.map (·.current) = some 2 := by native_decide

/-! ## `collectOutputs` accumulates newest frame first -/

example : (advanceFromInit [[mkAssumption "a"], [mkAssumption "b", mkAssumption "c"]]).toOption.map
      (·.collectOutputs (· ++ ·) [])
    = some ["b", "c", "a"] := by native_decide

/-! ## Failure propagation: a failing step surfaces the backend's error -/

def failingBackend : Fold String Nat (List String) ToyPureExpr where
  stepEntry := fun n out e =>
    if e.name == "boom" then .error s!"failed at {e.name}"
    else .ok (n + 1, out ++ [e.name])
  emptyOutput := []

/-- The failing step's concrete error text propagates out of the fold. -/
example : (match ((failingBackend.advance [[mkAssumption "a", mkAssumption "boom"]]).exec
      (FoldState.init 0) : Except String _) with
    | .error e => e
    | .ok _ => "UNEXPECTED ok") = "failed at boom" := by native_decide

end PathConditionsFoldTest
