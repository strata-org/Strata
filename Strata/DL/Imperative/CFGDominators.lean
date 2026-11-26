/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.CFG
public import Strata.Util.Name
import Std.Data.HashSet

/-! # CFG dominator analysis (generic)

Dominator computation over a `CFG String (DetBlock String CmdT P)`, generic in
the command type `CmdT`. The analysis reads only `blk.transfer`, so it is
command-agnostic; `CmdT` only shapes the input `CFG`. The generic graph
traversal it builds on (`predMap`, `succMap`, `reversePostorderFrom`) lives in
`Strata.DL.Imperative.CFG`; this file adds only the dominance layer. The entry
points (`computeIdoms`, `dominatorsOfIdoms`, `computeDominators`, and the
post-dominator analysis `computePostIdoms`) are in `Imperative.CFG`, so they
read as `cfg.computeDominators`; so is `idomsFrom` (the algorithm on any
successor and predecessor maps). The other helpers are in
`Imperative.CFG.Dom`.
The dominator map numbers the dominator tree, so `dominates` answers a query from
the numbers in constant time; `computeIdomsDag` is the one-pass computation for
acyclic graphs. `CFGDominatorsTest` compares them with the textbook fixpoint on
random graphs.

`computeDominators` is not proved to compute true dominance; callers, including
`WFCFGProp`, treat it as the definition of dominance.

Proof debt. The direction the CFG type checker relies on is unproved: for a block
`b` reachable from the entry, `dominates computeDominators a b = true` implies
that every path from the entry to `b` passes through `a`. Until it is proved, the
differential test `CFGDominatorsTest`, which compares `computeDominators` with
the textbook set-dataflow fixpoint on many random graphs (irreducible ones, with
self-loops, unreachable blocks and an entry that is a loop header, included), is
the evidence that the two agree.
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

/-- The dominators of every block, as the pre/post numbers of the dominator tree:
a reachable block maps to an interval, and `a` dominates `b` exactly when `a`'s
interval contains `b`'s. An unreachable block maps to the interval
`(n, 0)`, with `n` above every pre-number: it lies inside every interval and
contains only unreachable blocks, so every block dominates it. See
`dominatorsOfIdoms`. -/
abbrev DomMap := Std.HashMap String (Nat × Nat)

/-- Does `a` dominate `b` in the computed map? A label the map does not have is
dominated by nothing and dominates nothing. -/
def dominates (dom : DomMap) (a b : String) : Bool :=
  match dom.get? a, dom.get? b with
  | some (ia, oa), some (ib, ob) => ia ≤ ib && ob ≤ oa
  | _, _ => false

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

/-- The immediate dominators of an acyclic graph, from its nodes in topological
    order (entry first, every node after all its predecessors) and its
    predecessor map. The entry maps to itself; a node in `order` that is
    unreachable from the entry is absent.

    One pass suffices, since each node's predecessors are final when it is
    reached. A node's idom is the common ancestor, in the tree built so far, of
    its predecessors. To find a common ancestor in logarithmic time whatever the
    shape of the tree, each node keeps its depth and a skip pointer to an
    ancestor (the skew-binary jump pointers of Myers). The fixpoint of
    `idomsFrom` re-climbs a node's whole chain for each predecessor, which
    is quadratic for a join with many predecessors and a shallow idom.

    Contract: on an acyclic graph, each reachable node maps to its immediate
    dominator. Passification (`PassiveVCGen.passifyWith`) relies on it in two ways:
    the variables it reconciles at a join (written since the join's `since` bound) and
    the path facts it takes from a block's dominator need only some dominator, while
    its test of a variable declared below the join's dominator (`declaredBelow`) needs
    the immediate one. -/
def computeIdomsDag (order : List String) (preds : Std.HashMap String (List String))
    (entry : String) : Std.HashMap String String := Id.run do
  let fuel := 2 * order.length + 2
  let mut idom : Std.HashMap String String := Std.HashMap.emptyWithCapacity.insert entry entry
  let mut depth : Std.HashMap String Nat := Std.HashMap.emptyWithCapacity.insert entry 0
  let mut jump : Std.HashMap String String := Std.HashMap.emptyWithCapacity.insert entry entry
  for l in order do
    if l == entry then continue
    let mut cur : Option String := none
    for p in preds.getD l [] do
      if idom.contains p then
        match cur with
        | none => cur := some p
        | some c =>
          let mut a := c
          let mut b := p
          for _ in [0:fuel] do
            if a == b then break
            if depth.getD a 0 < depth.getD b 0 then
              let t := a; a := b; b := t
            if depth.getD a 0 > depth.getD b 0 then
              -- Bring the deeper one up to the other's depth: its skip pointer when
              -- that does not pass the depth, otherwise its parent.
              let j := jump.getD a a
              if depth.getD j 0 ≥ depth.getD b 0 then a := j else a := idom.getD a a
            else
              -- At one depth the skip pointers are at one depth too (a pointer's
              -- depth depends on the node's depth alone). Different targets mean
              -- the common ancestor is above them, so both jump; equal ones mean
              -- it is at or below them, so both take their parents.
              let ja := jump.getD a a
              let jb := jump.getD b b
              if ja != jb then
                a := ja
                b := jb
              else
                a := idom.getD a a
                b := idom.getD b b
          cur := some a
    if let some r := cur then
      let j := jump.getD r r
      let jj := jump.getD j j
      let dr := depth.getD r 0
      idom := idom.insert l r
      depth := depth.insert l (dr + 1)
      jump := jump.insert l
        (if dr - depth.getD j 0 == depth.getD j 0 - depth.getD jj 0 then jj else r)
  return idom

/-- The dominator tree of the reachable nodes (`idomsFrom` from the entry over the transfer
edges). Returns the reachable labels in reverse postorder (entry first) and a map from each
reachable label to its immediate dominator (the entry maps to itself). Unreachable labels are
absent from both. -/
def computeIdoms (cfg : CFG String (DetBlock String CmdT P)) :
    List String × Std.HashMap String String :=
  idomsFrom cfg.succMap cfg.predMap cfg.entry

/-- The dominator map built from `idoms`, the reverse postorder and immediate
dominators that `computeIdoms cfg` returns: a depth-first numbering of the
dominator tree. A reachable block maps to its pre/post interval, so one block
dominates another exactly when its interval contains the other's (`Dom.dominates`);
an unreachable block maps to `(n, 0)` for `n` above every pre-number, so every
block dominates it. The map takes linear time and space, and answers a query in
constant time. -/
def dominatorsOfIdoms (cfg : CFG String (DetBlock String CmdT P))
    (idoms : List String × Std.HashMap String String) : Dom.DomMap := Id.run do
  let (rpo, idom) := idoms
  let mut kids : Std.HashMap String (Array String) := {}
  for l in rpo do
    if l != cfg.entry then
      let p := idom.getD l cfg.entry
      kids := kids.insert p ((kids.getD p #[]).push l)
  let mut tin : Std.HashMap String Nat := Std.HashMap.ofList [(cfg.entry, 0)]
  let mut iv : Dom.DomMap := {}
  let mut stack : Array (String × Nat) := #[(cfg.entry, 0)]
  let mut clock := 1
  -- Each step pushes a child or pops a node, so 2 steps per block suffice.
  for _ in [0:2 * rpo.length + 2] do
    match stack.back? with
    | none => break
    | some (n, i) =>
      let ks := kids.getD n #[]
      if h : i < ks.size then
        stack := stack.pop.push (n, i + 1)
        tin := tin.insert ks[i] clock
        clock := clock + 1
        stack := stack.push (ks[i], 0)
      else
        iv := iv.insert n (tin.getD n 0, clock)
        clock := clock + 1
        stack := stack.pop
  for l in cfg.labels do
    if !iv.contains l then
      iv := iv.insert l (clock + 1, 0)
  return iv

/-- Dominator analysis via the Cooper-Harvey-Kennedy immediate-dominator
algorithm. Returns the dominator tree's interval map (`dominatorsOfIdoms`), whose
`dominates` is intended to agree with the textbook
`dom(entry) = {entry}`, `dom(n) = {n} ∪ ⋂_{p ∈ preds(n)} dom(p)` fixpoint
(checked by a differential test, not proved; see the module header).

    Every block is in the domain, unreachable ones included. An unreachable
    non-entry block has no entry-to-`b` path, so the CHK fixpoint never assigns
    it an idom; it is mapped to an interval inside every other (see `Dom.DomMap`),
    so every block dominates it. This is the faithful reading of the dominance
    definition (for an unreachable `b` the set of entry-to-`b` paths is empty, so
    "on every such path" holds vacuously for every candidate). -/
def computeDominators (cfg : CFG String (DetBlock String CmdT P)) : Dom.DomMap :=
  cfg.dominatorsOfIdoms cfg.computeIdoms

/-- The immediate post-dominator of each block of `cfg` from which a `finish` block is
reachable: `some l` when it is the block `l`, and `none` when it is the end of the procedure
(no other block lies on every path from the block to a `finish`). Blocks from which no
`finish` is reachable are absent.

The post-dominators are the dominators of the reversed graph from one added node (the end,
labelled by `Strata.Name.freshName`, distinct from every block label and branch target) that every
`finish` block jumps to: `idomsFrom` over the reversed edges, as `computeIdoms` over the
edges.

Like `computeDominators`, this is not proved to compute true post-dominance: no theorem states
that every path from a block to a `finish` passes through its immediate post-dominator. The
evidence is a differential test against the textbook set-dataflow fixpoint
(`StrataTest/Languages/Core/Tests/SymExecCFGTest.lean`). -/
def computePostIdoms (cfg : CFG String (DetBlock String CmdT P)) :
    Std.HashMap String (Option String) := Id.run do
  let preds := cfg.predMap
  -- The keys of `preds` are every block label and every branch target.
  let exit := Strata.Name.freshName (.ofList preds.keys) "$__exit"
  let finishes := cfg.blocks.filterMap fun (l, b) =>
    match b.transfer with
    | .finish _ => some l
    | .condGoto .. => none
  -- Reversed edges: a block's successors are its predecessors, and the end's are the
  -- `finish` blocks.
  let rsuccs := preds.insert exit finishes
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

/-- The back edges of `cfg`, by loop header: each edge `b → h` from a block `b` in `reachable`
to a block `h` that dominates it (`dom`, from `computeDominators`) makes `h` a loop header.
The headers come in the order of their first back edge in block order, each with the sources
of its back edges in block order. -/
def backEdges (dom : Dom.DomMap) (reachable : Std.HashSet String)
    (cfg : CFG String (DetBlock String CmdT P)) : Array (String × Array String) := Id.run do
  let mut headers : Array String := #[]
  let mut srcs : Std.HashMap String (Array String) := {}
  for (b, blk) in cfg.blocks do
    if reachable.contains b then
      for t in blk.transfer.targets do
        if Dom.dominates dom t b then
          if !srcs.contains t then headers := headers.push t
          srcs := srcs.insert t ((srcs.getD t #[]).push b)
  return headers.map fun h => (h, srcs.getD h #[])

/-- The blocks in `reachable` that carry a `loopInvariant` but are not loop headers
(`backEdges`), in block order. A loop invariant means something only on a header. -/
def misplacedInvariants (dom : Dom.DomMap)
    (reachable : Std.HashSet String) (cfg : CFG String (DetBlock String CmdT P)) :
    List String :=
  let headers : Std.HashSet String := .ofList ((backEdges dom reachable cfg).toList.map (·.1))
  cfg.blocks.filterMap fun (l, blk) =>
    if reachable.contains l && !headers.contains l && !blk.md.loopInvariantValues.isEmpty then
      some l
    else none

end -- public section

end CFG
end Imperative
