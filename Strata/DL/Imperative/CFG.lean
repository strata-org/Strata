/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.BasicBlock
import Std.Data.HashSet

/-! # CFG traversal and reachability (generic)

Successor/predecessor construction, reachability, depth-first ordering, and cycle
detection over a `CFG String (DetBlock String CmdT P)`, generic in the command
type `CmdT`. These read only `blk.transfer`, so they are command-agnostic; `CmdT`
only shapes the input `CFG`. They do not depend on dominance, so any CFG analysis
that needs plain graph traversal can use them. Names are in the `Imperative.CFG`
namespace, so a function taking the CFG first can be called as `cfg.succMap`. -/

namespace Imperative
namespace CFG

public section

variable {P : PureExpr} {CmdT : Type}

/-- Predecessor map: for each label, the labels that jump to it. Every block
label and every transfer target is a key, so the keys are exactly the labels
only when every target names a block. -/
def predMap (cfg : CFG String (DetBlock String CmdT P)) :
    Std.HashMap String (List String) := Id.run do
  let mut m : Std.HashMap String (List String) := {}
  for (l, _) in cfg.blocks do
    if !m.contains l then m := m.insert l []
  for (l, blk) in cfg.blocks do
    for s in blk.transfer.targets do
      let cur := m.getD s []
      m := m.insert s (l :: cur)
  return m

/-- Successor map: each label ↦ its transfer successors. Assumes unique labels:
for a repeated label, the last block wins. -/
def succMap (cfg : CFG String (DetBlock String CmdT P)) :
    Std.HashMap String (List String) := Id.run do
  let mut m : Std.HashMap String (List String) := {}
  for (l, blk) in cfg.blocks do
    m := m.insert l blk.transfer.targets
  return m

/-- The labels reachable in one or more steps from `start`, using a successor map
`succs` and a breadth-first search bound `fuel`. A search of at least the node
count reaches every such label. -/
def reachableSetFromSuccsWith (succs : Std.HashMap String (List String))
    (fuel : Nat) (start : String) : Std.HashSet String := Id.run do
  let seed := succs.getD start []
  let mut visited : Std.HashSet String := Std.HashSet.ofList seed
  let mut frontier : List String := seed
  for _ in [0:fuel] do
    let mut next : List String := []
    for l in frontier do
      for s in succs.getD l [] do
        if !visited.contains s then
          visited := visited.insert s
          next := s :: next
    frontier := next
  return visited

/-- Labels reachable from `cfg.entry` by following transfer successors, the
entry included. -/
def reachableLabels (cfg : CFG String (DetBlock String CmdT P)) : Std.HashSet String :=
  (reachableSetFromSuccsWith cfg.succMap cfg.blocks.length cfg.entry).insert cfg.entry

/-- Is `l` reachable from `cfg.entry`? -/
def isReachable (cfg : CFG String (DetBlock String CmdT P)) (l : String) : Bool :=
  cfg.reachableLabels.contains l

/-- Number of nodes plus twice the number of edges of the successor map `succs`.
Bounds the pops of a traversal that visits each node once and pushes each edge
at most once. -/
def succMapSize (succs : Std.HashMap String (List String)) : Nat :=
  succs.fold (init := 0) fun acc _ ss => acc + 1 + 2 * ss.length

/-- A reverse postorder of the nodes of `succs` reachable from `roots`: an
iterative depth-first search from each root in turn, prepending each node when it
finishes. Only keys of `succs` are visited; a successor that is not a key is not
a node. Each node is expanded once, so the result lists each visited node once,
and every node appears after any node that reaches it along tree edges. -/
def reversePostorderFrom (succs : Std.HashMap String (List String))
    (roots : List String) : List String := Id.run do
  -- Each pop is a root, an edge push, or a node's finish marker, so
  -- `roots.length + succMapSize succs + 1` pops drain the stack.
  let fuel := roots.length + succMapSize succs + 1
  let mut visited : Std.HashSet String := {}
  let mut rpo : List String := []
  -- Work stack of `(label, finished?)`. A node's finish marker sits below its
  -- children, so the node is prepended to `rpo` only after they all finish.
  let mut stack : List (String × Bool) := (roots.filter succs.contains).map (·, false)
  for _ in [0:fuel] do
    match stack with
    | [] => break
    | (l, true) :: rest =>
      rpo := l :: rpo
      stack := rest
    | (l, false) :: rest =>
      if visited.contains l then
        stack := rest
      else
        visited := visited.insert l
        let kids := (succs.getD l []).filter fun s => succs.contains s && !visited.contains s
        stack := kids.map (·, false) ++ (l, true) :: rest
  return rpo

/-- The labels that lie on a cycle: those reachable from the roots `labels` that
can leave and return to themselves. Computed for all labels at once, in time
linear in the size of `succs`, with Kosaraju's algorithm: a reverse postorder
(`reversePostorderFrom`), then a pass over the reversed edges, in that order,
collecting each strongly connected component. A label lies on a cycle iff its
component has at least two labels or it has a self-loop. -/
def cycleLabelsWith (succs : Std.HashMap String (List String)) (labels : List String) :
    Std.HashSet String := Id.run do
  let fuel := labels.length + succMapSize succs + 1
  let rpo := reversePostorderFrom succs labels
  -- Reversed edges between visited nodes.
  let mut preds : Std.HashMap String (List String) := {}
  for l in rpo do
    for s in succs.getD l [] do
      preds := preds.insert s (l :: preds.getD s [])
  -- In reverse postorder, flood each unassigned node's component over the
  -- reversed edges.
  let mut assigned : Std.HashSet String := {}
  let mut onCyc : Std.HashSet String := {}
  for root in rpo do
    if assigned.contains root then continue
    assigned := assigned.insert root
    let mut comp : List String := []
    let mut work : List String := [root]
    for _ in [0:fuel] do
      match work with
      | [] => break
      | u :: rest =>
        work := rest
        comp := u :: comp
        for p in preds.getD u [] do
          if !assigned.contains p then
            assigned := assigned.insert p
            work := p :: work
    let multi := match comp with
      | _ :: _ :: _ => true
      | _ => false
    for u in comp do
      if multi || (succs.getD u []).contains u then
        onCyc := onCyc.insert u
  return onCyc

end -- public section

end CFG
end Imperative
