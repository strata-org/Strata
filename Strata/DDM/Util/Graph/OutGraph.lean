module

import all Strata.DDM.Util.Vector

public section
namespace Strata

structure OutGraph (nodeCount : Nat) where
  /-- For each edge `s -> t` in the graph, we have `s ∈ edges[t]` -/
  edges : Vector (Array (Fin nodeCount)) nodeCount
  deriving Inhabited, Repr

namespace OutGraph

abbrev Node n := Fin n

protected def empty (n : Nat) : OutGraph n where
  edges := .replicate n ∅

protected def addEdge {n} (g : OutGraph n) (f t : Node n) : OutGraph n :=
  { edges := Vector.modify g.edges ⟨t, by omega⟩ (·.push ⟨f, by omega⟩)
  }

protected def addEdge! {n} (g : OutGraph n) (f t : Nat) : OutGraph n :=
  if fp : f ≥ n then
    @panic _ ⟨g⟩ s!"Invalid from edge {f}"
  else if tp : t ≥ n then
    @panic _ ⟨g⟩ s!"Invalid to edge {t}"
  else
    g.addEdge ⟨f, Nat.lt_of_not_le fp⟩ ⟨t, Nat.lt_of_not_le tp⟩

protected def ofEdges! (n : Nat) (edges : List (Nat × Nat)) : OutGraph n :=
  edges.foldl (fun g (f, t) => g.addEdge! f t) (.empty n)

def nodesOut {n} (g : OutGraph n) (node : Node n) : Array (Node n) :=
    g.edges[node]

end Strata.OutGraph
end
