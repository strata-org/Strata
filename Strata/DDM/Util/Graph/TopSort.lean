/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

-- Topological sort implementation (not currently used)
import Strata.DDM.Util.Fin
import Strata.DDM.Util.Vector

namespace Strata

structure Graph where
  nodeCount : Nat
  edges : Vector (Array (Fin nodeCount)) nodeCount
  deriving Inhabited

namespace Graph

protected def empty (count : Nat) : Graph where
  nodeCount := count
  edges := .mkVector count ∅

protected def addEdge (g : Graph) (f : Nat) (t : Nat) : Graph :=
  if p : f ≥ g.nodeCount then
    @panic _ ⟨g⟩ s!"Invalid from edge {f}"
  else if q : t ≥ g.nodeCount then
    @panic _ ⟨g⟩ s!"Invalid to edge {t}"
  else
    { nodeCount := g.nodeCount,
      edges := g.edges.modify ⟨t, by omega⟩ (·.push ⟨f, by omega⟩)
    }

protected def ofEdges (count : Nat) (edges : List (Nat × Nat)) : Graph :=
  let g : Graph := edges.foldl (fun g (f, t) => g.addEdge f t) (.empty count)
  g

def nodesInto (g : Graph) (node : Fin g.nodeCount) : Array (Fin g.nodeCount) :=
  g.edges[node]

protected def addPre (p : Vector Bool n × Array (Fin n)) (pre : Fin n) :=
  if p.fst[pre] then
    p
  else
    (p.fst.set pre true, p.snd.push pre)

def topSort (g : Graph) : Array (Fin g.nodeCount) := Id.run do
  -- Quick sort all edges to ensure they are sorted.
  let g : Graph := { edges := g.edges.map (fun a => a.qsort) }

  let mut res : Array (Fin g.nodeCount) := #[]
  let mut added : Vector Bool g.nodeCount := Vector.mkVector g.nodeCount false
  -- Iterate through nodes in order
  for init in Fin.range g.nodeCount do
    -- Skip node already added.
    if added[init] then
      continue
    added := added.set init true
    -- Stack to store nodes to visit
    let mut ctx : Array (Fin g.nodeCount) := #[init]
    let mut stk : Array (Fin g.nodeCount) := #[]
    while !ctx.isEmpty do
      let c := ctx.getD (ctx.size - 1) init
      ctx := ctx.pop
      stk := stk.push c
      -- Add all nodes into
      let (added2, ctx2) := g.nodesInto c |>.foldl Graph.addPre (added, ctx)
      added := added2
      ctx := ctx2
    res := stk.foldr (fun c r => r.push c) res
  return res

abbrev Node (g : Graph) : Type := Fin g.nodeCount

end Graph

/--
info: #[3, 2, 1, 0]
-/
#guard_msgs in
#eval Graph.ofEdges 4 [(2, 1), (1, 3), (1, 0), (3, 2)] |>.topSort

/--
info: #[1, 2, 0, 3]
-/
#guard_msgs in
#eval Graph.ofEdges 4 [(2, 0), (1,0)] |>.topSort

/--
info: #[1, 2, 0, 3]
-/
#guard_msgs in
#eval Graph.ofEdges 4 [(1, 0), (2,0)] |>.topSort

/--
info: #[1, 0]
-/
#guard_msgs in
#eval Graph.ofEdges 2 [(1, 0), (0,1)] |>.topSort

/--
info: #[1, 0]
-/
#guard_msgs in
#eval Graph.ofEdges 2 [(0, 1), (1, 0)] |>.topSort

end Strata
