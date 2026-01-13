module
public import Strata.DDM.Util.Graph.OutGraph
public import Std.Data.HashSet

import all Strata.DDM.Util.Array

public section
namespace Strata.OutGraph

private structure WorkSet (n : Nat) where
  set : Vector Bool n
  pending : Array (Fin n)
  inv : ∀idx, idx ∈ pending → set[idx.val] = true

namespace WorkSet

private def remainingCount {n} (s : WorkSet n) : Nat :=
  (s.set.toArray.filter (!·)).size + s.pending.size

private def empty {n} : WorkSet n :=
  { set := .replicate _ false
    pending := #[]
    inv := fun idx idxp => by simp only [Array.mem_empty_iff] at idxp
  }

private def addIdx {n} (s : WorkSet n) (idx : Fin n) : WorkSet n :=
  if p : s.set[idx] = true then
    s
  else
    let { set, pending, inv } := s
    { set := set.set idx true
      pending := pending.push idx
      inv := by grind
    }

private theorem remainingCount_addIdx {n} (s : WorkSet n) (idx : Fin n) :
  (s.addIdx idx).remainingCount = s.remainingCount := by
  simp only [WorkSet.addIdx]
  if h : s.set[idx] = true then
    simp [h]
  else
    have eq_false : s.set[idx.val] = false :=
      iff_of_eq (Bool.not_eq_true (s.set[idx.val])) |>.mp h
    simp [-Vector.size_toArray, -Array.size_set,
          remainingCount, Array.size_filter_set, eq_false]
    have false_in : false ∈ s.set :=  ⟨Array.mem_of_getElem eq_false⟩
    have size_pos : (Array.filter (fun x => !x) s.set.toArray).size > 0 := by
      simp [-Vector.size_toArray, Array.size_filter_pos_iff, false_in]
    omega


@[inline]
private def pop {n} (s : WorkSet n) (p : s.pending.size > 0) : WorkSet n :=
  let { set, pending, inv } := s
  { set
    pending := pending.pop
    inv := by
      intro idx mem
      apply inv
      simp [Array.mem_pop_ne p, mem]
   }

private theorem remaining_count_pop {m} (s : WorkSet m) (p : s.pending.size > 0) :
  (s.pop p).remainingCount + 1 = s.remainingCount := by
  simp_all [pop, remainingCount]
  grind

end WorkSet

private def preimage.aux {n} (g : OutGraph n) (s : WorkSet n) : Vector Bool n :=
  if p : s.pending.size > 0 then
    let idx := s.pending.back
    let s := s.pop p
    let ops := g.edges[idx]
    let s := ops.foldl (init := s) WorkSet.addIdx
    preimage.aux g s
  else
    s.set
termination_by s.remainingCount
decreasing_by
  rename_i u _
  have foldl_eq : ∀{n} (z : WorkSet n) (nodes : Array (Fin n)),
          (Array.foldl WorkSet.addIdx z nodes).remainingCount = z.remainingCount := by
    intro n z nodes
    apply Array.foldl_induction (motive := fun _ (s : WorkSet n) => s.remainingCount = z.remainingCount)
    case h0 =>
      simp
    case hf =>
      intro sz s sp
      simp [WorkSet.remainingCount_addIdx]
      exact sp
  simp [foldl_eq]
  have inv := WorkSet.remaining_count_pop u p
  omega

/--
`g.preimage_closure s` returns the nodes that have paths to some node in `s`.

Specifically, let `v = g.preimage_closure s`, then `v[i] = true` iff there is
a path from `i` to any node in `s` via the edges in `g`.
-/
def preimage_closure {n}
      (g : OutGraph n)
      (elts : Std.HashSet (Fin n))
      : Vector Bool n :=
  let s := .empty
  let s := elts.fold (init := s) fun s idx => s.addIdx idx
  preimage.aux g s

end Strata.OutGraph
end
