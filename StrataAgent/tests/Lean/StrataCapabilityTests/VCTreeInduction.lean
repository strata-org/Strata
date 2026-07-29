/-! # Verification conditions (Tier: binary-tree structural induction)

Inspired by the NTP4VC (github.com/xqyww123/NTP4VC) `tree_height_vcg`, `avl`, and
`bintree` VCs. The benchmark's `Why3.bintree` library models a polymorphic binary
tree with `size`/`height` measures over `ℤ`; here those are ported to core Lean 4
(no Mathlib) over `Nat`, with the VCs restated as self-contained obligations.

These need an induction on the TREE (two inductive hypotheses per node), a step up
from the list-induction tier. Proofs are left as `sorry`. -/

inductive Tree (α : Type) where
  | leaf : Tree α
  | node : Tree α → α → Tree α → Tree α

-- Why3.bintree.Size: number of internal nodes.
def Tree.size {α : Type} : Tree α → Nat
  | .leaf => 0
  | .node l _ r => 1 + l.size + r.size

-- Why3.bintree.Height: longest root-to-leaf path.
def Tree.height {α : Type} : Tree α → Nat
  | .leaf => 0
  | .node l _ r => 1 + max l.height r.height

-- left/right subtree swap (mirror), as in the avl balance VCs.
def Tree.mirror {α : Type} : Tree α → Tree α
  | .leaf => .leaf
  | .node l x r => .node r.mirror x l.mirror

-- tree_height_vcg-style: height is bounded by size.
theorem height_le_size_vc {α} (t : Tree α) : t.height ≤ t.size := by
  sorry

-- mirroring preserves the node count (a balance/rotation invariant).
theorem size_mirror_vc {α} (t : Tree α) : t.mirror.size = t.size := by
  sorry

-- mirroring preserves height.
theorem height_mirror_vc {α} (t : Tree α) : t.mirror.height = t.height := by
  sorry

-- mirror is an involution (double rotation returns the original tree).
theorem mirror_mirror_vc {α} (t : Tree α) : t.mirror.mirror = t := by
  sorry
