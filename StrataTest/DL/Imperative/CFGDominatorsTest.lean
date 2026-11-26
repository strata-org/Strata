/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Languages.Core

meta section

/-! # Differential test of the dominator map

`CFG.computeDominators` numbers the dominator tree (pre and post numbers), so that
`CFG.Dom.dominates` is an interval containment test. This test compares it, on
every pair of blocks of many random CFGs, with the textbook fixpoint
`dom(entry) = {entry}`, `dom(n) = {n} ∪ ⋂ dom(p)` over the reachable predecessors.
The graphs are small, random and unconstrained, so they include irreducible
cycles, self-loops, unreachable blocks, repeated successors and an entry that is
a loop header (the last checks below count them, among the graphs compared).

`CFG.computeIdomsDag`, the one-pass computation for acyclic graphs that the
passive VC generator uses, is compared with the fixpoint `CFG.idomsFrom`
on random acyclic graphs. -/

namespace Strata.Test.CFGDominators

open Imperative

abbrev Cfg := CFG String (DetBlock String Core.Command Core.Expression)

/-- A deterministic pseudo-random sequence (a linear congruential generator). -/
private def next (seed : Nat) : Nat := (seed * 1103515245 + 12345) % 2147483648

/-- A CFG of `n` blocks `b0` (the entry) to `b{n-1}`, each with no, one or two
    successors chosen at random. -/
private def randomCfg (seed n : Nat) : Cfg × Nat := Id.run do
  let mut s := seed
  let mut blocks : List (String × DetBlock String Core.Command Core.Expression) := []
  for i in [0:n] do
    s := next s
    let kind := (s / 65536) % 4
    s := next s
    let t1 := s_label ((s / 65536) % n)
    s := next s
    let t2 := s_label ((s / 65536) % n)
    let transfer : DetTransferCmd String Core.Expression :=
      match kind with
      | 0 => .finish .empty
      | 1 => .goto t1
      | _ => .condGoto (Lambda.LExpr.boolConst default true) t1 t2 .empty
    blocks := blocks ++ [(s!"b{i}", { cmds := [], transfer := transfer })]
  return ({ entry := "b0", blocks := blocks }, s)
where
  s_label (k : Nat) : String := s!"b{k}"

/-- The textbook dominator sets of the reachable blocks. -/
private def referenceDom (cfg : Cfg) : Std.HashMap String (List String) := Id.run do
  let reach := cfg.reachableLabels
  let labels := cfg.labels.filter reach.contains
  let preds := cfg.predMap
  let mut dom : Std.HashMap String (List String) := {}
  for l in labels do
    dom := dom.insert l (if l == cfg.entry then [cfg.entry] else labels)
  for _ in [0:labels.length * labels.length + 1] do
    for l in labels do
      if l != cfg.entry then
        let ps := (preds.getD l []).filter reach.contains
        let inter := match ps with
          | [] => []
          | p :: rest => rest.foldl (fun acc q => acc.filter ((dom.getD q []).contains ·)) (dom.getD p [])
        dom := dom.insert l (l :: inter.filter (· != l))
  return dom

/-- The random CFGs of `n` blocks that `mismatches count n` compares. -/
private def sample (count n : Nat) : List Cfg := Id.run do
  let mut seed := 7
  let mut out := []
  for _ in [0:count] do
    let (cfg, s') := randomCfg seed n
    seed := s'
    out := cfg :: out
  return out.reverse

/-- The number of ordered pairs of blocks on which `dominates` disagrees with the
    reference, over `count` random CFGs of `n` blocks. A pair with an unreachable
    second block is true (every block dominates it), and a pair with only the
    first unreachable is false. -/
private def mismatches (count n : Nat) : Nat := Id.run do
  let mut bad := 0
  for cfg in sample count n do
    let reach := cfg.reachableLabels
    let dom := cfg.computeDominators
    let ref := referenceDom cfg
    for a in cfg.labels do
      for b in cfg.labels do
        let want :=
          if !reach.contains b then true
          else reach.contains a && (ref.getD b []).contains a
        if CFG.Dom.dominates dom a b != want then bad := bad + 1
  return bad

/-- info: 0 -/
#guard_msgs in #eval mismatches 400 4

/-- info: 0 -/
#guard_msgs in #eval mismatches 400 7

/-- info: 0 -/
#guard_msgs in #eval mismatches 200 11

/-- Does the CFG have a cycle that survives removing every edge to a dominator (the
    back edges of the dominator tree)? Such a cycle has no header: irreducible. -/
private def irreducible (g : Cfg) : Bool :=
  let dom := g.computeDominators
  let reach := g.reachableLabels
  let succs : Std.HashMap String (List String) :=
    g.blocks.foldl (fun m (b, blk) =>
      m.insert b (if reach.contains b then blk.transfer.targets.filter (!CFG.Dom.dominates dom · b) else []))
      {}
  !(CFG.cycleLabelsWith succs [g.entry]).isEmpty

-- The graphs compared include the shapes the comparison is meant to cover: a
-- cycle, an unreachable block, an irreducible graph, a self-loop, an entry that
-- is a loop header (the target of an edge from a block it dominates), and a
-- block that lists one successor twice.
/-- info: (true, true, true, true, true, true) -/
#guard_msgs in #eval
  let graphs := sample 400 4 ++ sample 400 7 ++ sample 200 11
  (graphs.any fun g => !(CFG.cycleLabelsWith g.succMap [g.entry]).isEmpty,
   graphs.any fun g => g.labels.any fun l => !(g.reachableLabels.contains l),
   graphs.any irreducible,
   graphs.any fun g => g.blocks.any fun (b, blk) => blk.transfer.targets.contains b,
   graphs.any fun g => g.blocks.any fun (b, blk) =>
     g.reachableLabels.contains b && blk.transfer.targets.contains g.entry,
   graphs.any fun g => g.blocks.any fun (_, blk) => match blk.transfer with
     | .condGoto _ t f _ => t == f
     | _ => false)

/-! ### The one-pass computation on acyclic graphs -/

/-- A random acyclic CFG of `n` blocks: every edge goes to a later block. -/
private def randomDag (seed n : Nat) : Cfg × Nat := Id.run do
  let mut s := seed
  let mut blocks : List (String × DetBlock String Core.Command Core.Expression) := []
  for i in [0:n] do
    s := next s
    let kind := (s / 65536) % 3
    s := next s
    let t1 := i + 1 + (s / 65536) % (n - i)
    s := next s
    let t2 := i + 1 + (s / 65536) % (n - i)
    let ok := fun (t : Nat) => t < n
    let transfer : DetTransferCmd String Core.Expression :=
      match kind with
      | 0 => .finish .empty
      | 1 => if ok t1 then .goto s!"b{t1}" else .finish .empty
      | _ => if ok t1 && ok t2 then .condGoto (Lambda.LExpr.boolConst default true) s!"b{t1}" s!"b{t2}" .empty
             else .finish .empty
    blocks := blocks ++ [(s!"b{i}", { cmds := [], transfer := transfer })]
  return ({ entry := "b0", blocks := blocks }, s)

/-- The number of acyclic graphs of `n` blocks, among `count`, on which
    `computeIdomsDag` (given the reverse postorder) differs from the fixpoint
    on the reachable blocks. -/
private def dagMismatches (count n : Nat) : Nat := Id.run do
  let mut seed := 11
  let mut bad := 0
  for _ in [0:count] do
    let (cfg, s') := randomDag seed n
    seed := s'
    let (rpo, want) := cfg.computeIdoms
    let got := CFG.computeIdomsDag rpo cfg.predMap cfg.entry
    if rpo.any (fun l => got.get? l != want.get? l) then bad := bad + 1
  return bad

/-- info: (0, 0, 0) -/
#guard_msgs in #eval (dagMismatches 300 5, dagMismatches 300 9, dagMismatches 100 30)

/-- A join of `k` predecessors, each at the end of a chain of its own, so that the
    idom of the join is the entry and the chains are deep: the shape on which
    climbing a chain per predecessor is quadratic. Blocks are listed in a topological
    order that visits the chains one after the other. -/
private def wideJoin (k len : Nat) : List String × Std.HashMap String (List String) := Id.run do
  -- Built in reverse and reversed once, so the order is linear to build.
  let mut orderRev := ["e"]
  let mut preds : Std.HashMap String (List String) := {}
  let mut lastsRev : List String := []
  for c in [0:k] do
    let mut prev := "e"
    for j in [0:len] do
      let l := s!"c{c}_{j}"
      orderRev := l :: orderRev
      preds := preds.insert l [prev]
      prev := l
    lastsRev := prev :: lastsRev
  orderRev := "join" :: orderRev
  preds := preds.insert "join" lastsRev.reverse
  return (orderRev.reverse, preds)

-- The join's idom is the entry, found without a climb per predecessor.
/-- info: "e" -/
#guard_msgs in #eval
  let (order, preds) := wideJoin 300 40
  (CFG.computeIdomsDag order preds "e").getD "join" "?"

-- Two long branches: the search compares the two at one depth, by skip pointers.
/-- info: "e" -/
#guard_msgs in #eval
  let (order, preds) := wideJoin 2 20000
  (CFG.computeIdomsDag order preds "e").getD "join" "?"

end Strata.Test.CFGDominators

end
