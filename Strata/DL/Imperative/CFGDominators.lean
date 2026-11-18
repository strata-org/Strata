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
points (`computeIdoms`, `dominatorsOfIdoms`, `computeDominators`, and the
post-dominator analysis `computePostIdoms`) are in `Imperative.CFG`, so they
read as `cfg.computeDominators`; so are `idomsFrom` (the algorithm on any
successor and predecessor maps) and `freshLabel`. The other helpers are in
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

/-- The immediate dominators of the nodes reachable from `root` in the graph whose successor
map is `succs` and whose predecessor map is `preds` (the same edges reversed), via the
Cooper-Harvey-Kennedy algorithm. Returns the reachable nodes in reverse postorder (`root`
first) and a map from each to its immediate dominator (`root` maps to itself). Unreachable
nodes are absent from both. Only keys of `succs` are nodes (`reversePostorderFrom`).

    The idoms are computed by a reverse-postorder fixpoint (near-linear on
    reducible graphs: a node's idom is the common idom-chain ancestor of its
    already-processed predecessors). In reverse postorder every dominator of a
    node precedes it, so walking the returned list visits each node after its
    parent in the dominator tree. -/
def idomsFrom (succs preds : Std.HashMap String (List String)) (root : String) :
    List String × Std.HashMap String String := Id.run do
  -- Every node is listed after its parent in the depth-first tree, which is
  -- what the fixpoint below needs.
  let rpo := reversePostorderFrom succs [root]
  -- reverse-postorder numbers (root = 0); a reachable node's number is its
  -- index in `rpo`, so a deeper node has a larger number.
  let mut rpoNum : Std.HashMap String Nat := {}
  for (l, i) in rpo.zipIdx do
    rpoNum := rpoNum.insert l i
  let fuel := rpo.length + 1
  -- CHK idom fixpoint. `idom[root] = root`; other reachable nodes start
  -- undefined and are filled from their predecessors' idoms in RPO order.
  let mut idom : Std.HashMap String String :=
    Std.HashMap.emptyWithCapacity.insert root root
  for _ in [0:fuel] do
    let mut changed := false
    for l in rpo do
      if l != root then
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

/-- The dominator tree of the reachable nodes (`idomsFrom` from the entry over the transfer
edges). Returns the reachable labels in reverse postorder (entry first) and a map from each
reachable label to its immediate dominator (the entry maps to itself). Unreachable labels are
absent from both. -/
def computeIdoms (cfg : CFG String (DetBlock String CmdT P)) :
    List String × Std.HashMap String String :=
  idomsFrom cfg.succMap cfg.predMap cfg.entry

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

/-- A label not in `labels`: `base`, extended by underscores until it is none of them. The
fuel, `labels.length`, suffices: of the `labels.length + 1` candidates, at most
`labels.length` are taken. -/
def freshLabel (labels : List String) (base : String) : String :=
  let rec go : Nat → String → String
    | 0, l => l
    | n + 1, l => if labels.contains l then go n (l ++ "_") else l
  go labels.length base

/-- The immediate post-dominator of each block of `cfg` from which a `finish` block is
reachable: `some l` when it is the block `l`, and `none` when it is the end of the procedure
(no other block lies on every path from the block to a `finish`). Blocks from which no
`finish` is reachable are absent.

The post-dominators are the dominators of the reversed graph from one added node (the end,
labelled by `freshLabel`) that every `finish` block jumps to: `idomsFrom` over the reversed
edges, as `computeIdoms` over the edges.

Like `computeDominators`, this is not proved to compute true post-dominance: no theorem states
that every path from a block to a `finish` passes through its immediate post-dominator. The
evidence is a differential test against the textbook set-dataflow fixpoint
(`StrataTest/Languages/Core/Tests/SymExecCFGTest.lean`). -/
def computePostIdoms (cfg : CFG String (DetBlock String CmdT P)) :
    Std.HashMap String (Option String) := Id.run do
  let exit := freshLabel cfg.labels "$__exit"
  let finishes := cfg.blocks.filterMap fun (l, b) =>
    match b.transfer with
    | .finish _ => some l
    | .condGoto .. => none
  -- Reversed edges: a block's successors are its predecessors, and the end's are the
  -- `finish` blocks.
  let rsuccs := cfg.predMap.insert exit finishes
  let mut rpreds := cfg.succMap.insert exit []
  for l in finishes do
    rpreds := rpreds.insert l (exit :: rpreds.getD l [])
  let (_, idom) := idomsFrom rsuccs rpreds exit
  let mut out : Std.HashMap String (Option String) := {}
  for (l, _) in cfg.blocks do
    match idom.get? l with
    | some d => out := out.insert l (if d == exit then none else some d)
    | none => pure ()
  return out

end -- public section

end CFG
end Imperative
