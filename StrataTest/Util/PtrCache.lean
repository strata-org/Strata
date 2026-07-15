/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

meta import Strata.Util.PtrCache

/-! # `PtrCache` smoke test

A minimal, self-contained exercise of the safe pointer-address cache
(`Strata.PtrCache`) on a toy AST: memoize a bottom-up node count keyed by
pointer identity, so a maximally-shared DAG is counted in time proportional to
the number of *distinct* nodes rather than its (exponential) tree unfolding.
-/

meta section

namespace Strata.PtrCache.Test

open Strata.PtrCache

/-- A toy binary-tree AST. -/
inductive Term where
  | leaf : Term
  | node : Term → Term → Term

/-- Reference node count: the size of `t` as a tree (each child counted in
    full, so this is exponential on a shared DAG). This is the pure function
    the cache memoizes. -/
def countNaive : Term → Nat
  | .leaf => 1
  | .node l r => 1 + countNaive l + countNaive r

/-- Pointer-address-memoized node count.
    Each physically distinct node is counted exactly once; the
    returned `Result countNaive t` carries a proof its value equals `countNaive t`. -/
def countPtrCache : (t : Term) → PtrCacheM countNaive t
  | .leaf => pure ⟨1, by simp [countNaive]⟩
  | .node l r => do
    let rl ← evalPtrCache l (countPtrCache l)
    let rr ← evalPtrCache r (countPtrCache r)
    pure ⟨1 + rl.output + rr.output, by simp [countNaive, rl.h, rr.h]⟩

/-- Run the memoized count from an empty cache. -/
def countCached (t : Term) : Nat := ((countPtrCache t).run' PtrCache.empty).output

/-- The memoized count equals the naive count for every term. -/
theorem countCached_eq (t : Term) : countCached t = countNaive t :=
  run'_output_eq (countPtrCache t) PtrCache.empty

/-- A maximally-shared tower: `tower n` has `2^(n+1) - 1` nodes as a tree, but
    only `n + 1` distinct nodes as a DAG. -/
def tower : Nat → Term
  | 0 => .leaf
  | n + 1 => let t := tower n; .node t t

-- Correctness on small inputs: the memoized count agrees with the naive one.
#guard countCached .leaf = 1
#guard countCached (tower 4) = countNaive (tower 4)
#guard countCached (tower 4) = 31   -- 2^5 - 1

-- `tower 50` has `2^51 - 1` nodes as a tree — a naive walk (`countNaive`) would
-- never finish, but `countCached` returns instantly.
#guard countCached (tower 50) = 2 ^ 51 - 1

end Strata.PtrCache.Test

end
