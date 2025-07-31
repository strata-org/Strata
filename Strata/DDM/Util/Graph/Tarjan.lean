/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DDM.Util.Fin
import Strata.DDM.Util.Vector

namespace Strata

structure OutGraph (nodeCount : Nat) where
  edges : Vector (Array (Fin nodeCount)) nodeCount
  deriving Inhabited, Repr

namespace OutGraph

abbrev Node n := Fin n

protected def empty (n : Nat) : OutGraph n where
  edges := .replicate n ∅

protected def addEdge (g : OutGraph n) (f t : Node n) : OutGraph n :=
  { edges := g.edges.modify ⟨t, by omega⟩ (·.push ⟨f, by omega⟩)
  }

protected def addEdge! (g : OutGraph n) (f t : Nat) : OutGraph n :=
  if fp : f ≥ n then
    @panic _ ⟨g⟩ s!"Invalid from edge {f}"
  else if tp : t ≥ n then
    @panic _ ⟨g⟩ s!"Invalid to edge {t}"
  else
    g.addEdge ⟨f, Nat.lt_of_not_le fp⟩ ⟨t, Nat.lt_of_not_le tp⟩

protected def ofEdges! (n : Nat) (edges : List (Nat × Nat)) : OutGraph n :=
  edges.foldl (fun g (f, t) => g.addEdge! f t) (.empty n)

def nodesOut (g : OutGraph n) (node : Node n) : Array (Node n) :=
    g.edges[node]

structure TarjanState (n : Nat) where
  index : Fin (n+1) := 0
  stk : Array (Fin n) := #[]
  indices : Vector (Fin (n + 1)) n := .replicate n (Fin.last n)
  lowlinks : Vector (Fin (n + 1)) n := .replicate n (Fin.last n)
  onStack : Vector Bool n := .replicate n false
  components : Array (Array (Fin n)) := #[]
deriving Inhabited

def TarjanState.mergeLowlink (s : TarjanState n) (v : Fin n) (w : Fin n): TarjanState n :=
  { s with lowlinks := s.lowlinks.modify v (min s.lowlinks[w]) }

def popTo (v : Fin n) (s : TarjanState n) (comp : Array (Fin n)) : TarjanState n :=
  if p : s.stk.size > 0 then
    let w := s.stk[s.stk.size - 1]
    let s := { s with stk := s.stk.pop, onStack := s.onStack.set w false  }
    let comp := comp.push w
    if w = v then
      { s with components := s.components.push comp.qsort }
    else
      popTo v s comp
  else
    panic "Unexpected empty stack"

partial def strongconnect (g : OutGraph n) (v : Node n) (s : TarjanState n) : TarjanState n :=
  -- Set the depth index for v to the smallest unused index
  let s := { s with
    index := s.index + 1,
    stk := s.stk.push v
    indices := s.indices.set v s.index,
    lowlinks := s.lowlinks.set v s.index
    onStack := s.onStack.set v true
  }
  let s := g.nodesOut v |>.foldl (init := s) fun (s : TarjanState n) w =>
    if s.indices[w] = .last n then
      let s := strongconnect g w s
      s.mergeLowlink v w
    else if s.onStack[w] then
      s.mergeLowlink v w
    else
      s
  if s.lowlinks[v] = s.indices[v] then
    popTo v s #[]
  else
    s

/--
This run Tarjan's algorithm to compute strongly connected components.

Results are ordered so that nodes in the group are in the same element
if they are in the same strongly connected component and a node only appears
in an array after all the nodes that have paths to it.
-/
def tarjan {n} (g : OutGraph n) : Array (Array (Node n)) :=
  let s : TarjanState n := {}
  let s : TarjanState n := n.fold (init := {}) fun v p s =>
    if s.indices[v] = .last n then
      strongconnect g ⟨v, p⟩ s
    else
      s
  s.components

/--
info: #[#[0, 1, 2, 4], #[3]]
-/
#guard_msgs in
#eval tarjan (.ofEdges! 5 [(0, 1), (1, 2), (2, 3), (2, 0), (2, 4), (4, 3), (4, 1)])
