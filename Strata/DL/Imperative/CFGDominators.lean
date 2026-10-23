/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.CFG
import Std.Data.HashSet

/-! # CFG dominator analysis (generic)

Dominator computation over a `CFG String (DetBlock String CmdT P)`, generic in
the command type `CmdT`. The analysis reads only `blk.transfer`, so it is
command-agnostic; `CmdT` only shapes the input `CFG`. The generic graph
traversal it builds on (`predMap`, `succMap`, `reversePostorderFrom`) lives in
`Strata.DL.Imperative.CFG`; this file adds only the dominance layer. The entry
points (`computeIdoms`, `dominatorsOfIdoms`, `computeDominators`) are in
`Imperative.CFG`, so they read as `cfg.computeDominators`; the helpers are in
`Imperative.CFG.Dom`.

`computeDominators` is not proved to compute true dominance; callers, including
`WFCFGProp`, treat it as the definition of dominance.

Proof debt. The direction the CFG type checker relies on is unproved: for a block
`b` reachable from the entry, `dominates computeDominators a b = true` implies
that every path from the entry to `b` passes through `a`. Until it is proved, the
differential test in `CFGTypeCheck.lean`, which compares `computeDominators`
with the textbook set-dataflow fixpoint on every test CFG, is the evidence that
the two agree. Those CFGs are small, hand-written and reducible, so it is weak
evidence for irreducible or deeply nested graphs.
Target: rung 4 (Lean proof). Budget: one follow-up CR. Fallback: the differential
test against `computeDominatorsFullFuel`. -/

namespace Imperative
namespace CFG
namespace Dom

public section


/-- Walk two nodes up their immediate-dominator chains to their common ancestor,
using reverse-postorder numbers as the "finger" (a node with a larger RPO number
is deeper, so it is advanced up via `idom` until the fingers meet). `idom` must
already be defined for every node on both chains; `rpoNum` gives each node's
index in the reverse-postorder. Fuel-bounded by the node count on each inner
walk, so it is total. This is the Cooper-Harvey-Kennedy intersection. -/
def idomIntersect (idom : Std.HashMap String String)
    (rpoNum : Std.HashMap String Nat) (fuel : Nat) : String → String → String :=
  fun b1 b2 => Id.run do
    let mut f1 := b1
    let mut f2 := b2
    for _ in [0:fuel] do
      if f1 == f2 then
        break
      -- advance the deeper finger (larger RPO number) up its idom chain.
      let mut inner1 := f1
      for _ in [0:fuel] do
        if rpoNum.getD inner1 0 > rpoNum.getD f2 0 then
          inner1 := idom.getD inner1 inner1
        else
          break
      f1 := inner1
      let mut inner2 := f2
      for _ in [0:fuel] do
        if rpoNum.getD inner2 0 > rpoNum.getD f1 0 then
          inner2 := idom.getD inner2 inner2
        else
          break
      f2 := inner2
    return f1

/-- Does `a` dominate `b` in the computed map? -/
def dominates (dom : Std.HashMap String (List String)) (a b : String) : Bool :=
  (dom.getD b []).contains a

end -- public section

end Dom

public section

variable {P : PureExpr} {CmdT : Type}

/-- The dominator tree of the reachable nodes, via the Cooper-Harvey-Kennedy
immediate-dominator algorithm. Returns the reachable labels in reverse postorder
(entry first) and a map from each reachable label to its immediate dominator
(the entry maps to itself). Unreachable labels are absent from both.

    The idoms are computed by a reverse-postorder fixpoint (near-linear on
    reducible CFGs: a node's idom is the common idom-chain ancestor of its
    already-processed predecessors). In reverse postorder every dominator of a
    node precedes it, so walking the returned list visits each node after its
    parent in the dominator tree. -/
def computeIdoms (cfg : CFG String (DetBlock String CmdT P)) :
    List String × Std.HashMap String String := Id.run do
  let preds := cfg.predMap
  -- Every node is listed after its parent in the depth-first tree, which is
  -- what the fixpoint below needs.
  let rpo := reversePostorderFrom cfg.succMap [cfg.entry]
  -- reverse-postorder numbers (entry = 0); a reachable node's number is its
  -- index in `rpo`, so a deeper node has a larger number.
  let mut rpoNum : Std.HashMap String Nat := {}
  for (l, i) in rpo.zipIdx do
    rpoNum := rpoNum.insert l i
  let fuel := rpo.length + 1
  -- CHK idom fixpoint. `idom[entry] = entry`; other reachable nodes start
  -- undefined and are filled from their predecessors' idoms in RPO order.
  let mut idom : Std.HashMap String String :=
    Std.HashMap.emptyWithCapacity.insert cfg.entry cfg.entry
  for _ in [0:fuel] do
    let mut changed := false
    for l in rpo do
      if l != cfg.entry then
        let ps := preds.getD l []
        -- new idom = intersection (over already-processed preds) of pred idoms.
        -- Seed with the first predecessor that already has an idom, then fold the
        -- rest through `idomIntersect`.
        let mut newIdom : Option String := none
        for p in ps do
          if idom.contains p then
            match newIdom with
            | none => newIdom := some p
            | some cur => newIdom := some (Dom.idomIntersect idom rpoNum fuel cur p)
        match newIdom with
        | none => pure ()
        | some ni =>
          if idom.getD l "" != ni || !idom.contains l then
            idom := idom.insert l ni
            changed := true
    if !changed then break
  return (rpo, idom)

/-- The dominator map built from `idoms`, the reverse postorder and immediate
dominators that `computeIdoms cfg` returns. A reachable block maps to its
immediate-dominator chain up to the entry; an unreachable block maps to every
label. -/
def dominatorsOfIdoms (cfg : CFG String (DetBlock String CmdT P))
    (idoms : List String × Std.HashMap String String) :
    Std.HashMap String (List String) := Id.run do
  let allLabels := cfg.labels
  let (rpo, idom) := idoms
  let fuel := rpo.length + 1
  -- derive dominator sets: reachable node ↦ its idom chain to entry; unreachable
  -- node ↦ ⊤ (all labels).
  let mut dom : Std.HashMap String (List String) := {}
  for l in allLabels do
    if l == cfg.entry then
      dom := dom.insert l [cfg.entry]
    else if idom.contains l then
      -- walk the idom chain from `l` up to (and including) entry.
      let mut chain : List String := [l]
      let mut cur := l
      for _ in [0:fuel] do
        if cur == cfg.entry then
          break
        let nxt := idom.getD cur cfg.entry
        chain := nxt :: chain
        cur := nxt
      dom := dom.insert l chain
    else
      -- unreachable: dominated by everything (⊤).
      dom := dom.insert l allLabels
  return dom

/-- Dominator analysis via the Cooper-Harvey-Kennedy immediate-dominator
algorithm. Returns a map label ↦ set of dominators (as a label list), intended
to be set-equal to the textbook `dom(entry) = {entry}`,
`dom(n) = {n} ∪ ⋂_{p ∈ preds(n)} dom(p)` fixpoint (checked by a differential
test, not proved; see the module header).

    Every block is in the domain, unreachable ones included. An unreachable
    non-entry block has no entry-to-`b` path, so the CHK fixpoint never assigns
    it an idom; it is mapped to every label (⊤) — i.e. dominated by all blocks.
    This is the faithful reading of the dominance definition (for an unreachable
    `b` the set of entry-to-`b` paths is empty, so "on every such path" holds
    vacuously for every candidate), not a sentinel. -/
def computeDominators (cfg : CFG String (DetBlock String CmdT P)) :
    Std.HashMap String (List String) :=
  cfg.dominatorsOfIdoms cfg.computeIdoms

end -- public section

end CFG
end Imperative
