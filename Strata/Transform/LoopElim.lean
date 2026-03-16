/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.Stmt

namespace Core
open Imperative Lambda

public section

/-! ## Loop elimination

This transformation converts a loop into an acyclic passive statement suitable
for symbolic verification. A loop invariant `I` is required; without one the
transformation produces no useful verification conditions.

### Role of the invariant

Unlike the classical Hoare triple `{P} while G { S } {Q}` — which keeps the
loop pre-condition `P`, inductive invariant `I`, and post-condition `Q`
separate — this encoding folds all three into `I`. The user must choose `I`
strong enough so that:

- the pre-loop state satisfies `I` (checked at entry), and
- `I ∧ ¬G` implies some desired post-condition `Q` (checked after the loop).

### Passive encoding recipe

Let `M` be the set of variables modified by the loop body.

```
assert(I);              -- VC1: I holds at loop entry (unconditional)
assume(I);              -- make I available on the 0-iteration path
                        --   (assert-then-assume; intentional exception to the
                        --    usual assert/assume separation, needed so that
                        --    assert(Q) can use I when G is false at entry)
if (G) {
  havoc(M);             -- non-deterministically pick a mid-loop state
  assume(G);            -- guard holds at this state (live iteration)
  assume(I);            -- invariant holds at this state
  S;                    -- execute one iteration of the body
  assert(I);            -- VC2: I is maintained by S

  havoc(M);             -- non-deterministically pick an exit state
  assume(¬G);           -- guard is false at exit (loop has terminated)
  assume(I);            -- invariant holds at exit (by induction from VC1+VC2)
}
assert(Q);              -- checked with I ∧ ¬G available on both paths:
                        --   G=false path: M is pre-loop state, I from assume above
                        --   G=true  path: M is arbitrary exit state, I ∧ ¬G from then-branch
```

Note: the `if(G)` then-branch does double duty — VC2 check and exit-state model —
so the mid-loop path conditions (`G(M_iter)`, `I(M_iter)`) are present alongside the
exit-state facts when `Q` is checked. These linger as irrelevant assumptions,
indeed.

Note: `assume(I)` after VC1 is not strictly necessary. If VC1 passes, then it
means `I` is derivable for a backend solver and we could skip adding it to the
path conditions. However, we choose to keep this assumption for a higher-quality
encoding.
-/

mutual

def Stmt.removeLoopsM
  [HasNot P] [HasVarsImp P C] [HasHavoc P C] [HasPassiveCmds P C]
  (s : Stmt P C) : StateM Nat (Stmt P C) :=
  match s with
  | .loop guard _ invariants bss md => do
    let loop_num ← StateT.modifyGet (fun x => (x, x + 1))
    let neg_guard : P.Expr := HasNot.not guard
    let assigned_vars := Block.modifiedVars bss
    -- All of the replaced statements reuse the metadata md.
    let havocd : Stmt P C :=
      .block s!"loop_havoc_{loop_num}" (assigned_vars.map (λ n => Stmt.cmd (HasHavoc.havoc n md))) {}
    let entry_invariants := invariants.mapIdx fun i inv =>
      Stmt.cmd (HasPassiveCmds.assert s!"entry_invariant_{loop_num}_{i}" inv md)
    let entry_invariant_assumes := invariants.mapIdx fun i inv =>
      Stmt.cmd (HasPassiveCmds.assume s!"assume_entry_invariant_{loop_num}_{i}" inv md)
    let first_iter_facts :=
      .block s!"first_iter_asserts_{loop_num}" (entry_invariants ++ entry_invariant_assumes) {}
    let inv_assumes := invariants.mapIdx fun i inv =>
      Stmt.cmd (HasPassiveCmds.assume s!"assume_invariant_{loop_num}_{i}" inv md)
    let arbitrary_iter_assumes := .block s!"arbitrary_iter_assumes_{loop_num}"
      ([Stmt.cmd (HasPassiveCmds.assume s!"assume_guard_{loop_num}" guard md)] ++ inv_assumes)
      md
    let maintain_invariants := invariants.mapIdx fun i inv =>
      Stmt.cmd (HasPassiveCmds.assert s!"arbitrary_iter_maintain_invariant_{loop_num}_{i}" inv md)
    let body_statements ← Block.removeLoopsM bss
    let arbitrary_iter_facts := .block s!"arbitrary_iter_facts_{loop_num}"
      ([havocd, arbitrary_iter_assumes] ++ body_statements ++ maintain_invariants) {}
    let not_guard := Stmt.cmd (HasPassiveCmds.assume s!"not_guard_{loop_num}" neg_guard md)
    let invariant_assumes := invariants.mapIdx fun i inv =>
      Stmt.cmd (HasPassiveCmds.assume s!"invariant_{loop_num}_{i}" inv md)
    let exit_state_assumes := [havocd, not_guard] ++ invariant_assumes
    let loop_passive :=
      .ite guard (arbitrary_iter_facts :: exit_state_assumes) [] {}
    pure (.block s!"loop_{loop_num}" [first_iter_facts, loop_passive] {})
  | .ite c tss ess md => do
    let tss ← Block.removeLoopsM tss
    let ess ← Block.removeLoopsM ess
    pure (.ite c tss ess md)
  | .block label bss md => do
    let bss ← Block.removeLoopsM bss
    pure (.block label bss md)
  | .cmd _ => pure s
  | .exit _ _ => pure s
  | .funcDecl _ _ => pure s  -- Function declarations pass through unchanged
  | .typeDecl _ _ => pure s  -- Type declarations pass through unchanged

def Block.removeLoopsM
  [HasNot P] [HasVarsImp P C] [HasHavoc P C] [HasPassiveCmds P C]
  (ss : List (Stmt P C)) : StateM Nat (List (Stmt P C)) :=
  match ss with
  | [] => pure []
  | s :: ss => do
    let s ← Stmt.removeLoopsM s
    let ss ← Block.removeLoopsM ss
    pure (s :: ss)

end

def Stmt.removeLoops
  [HasNot P] [HasVarsImp P C] [HasHavoc P C] [HasPassiveCmds P C]
  (s : Stmt P C) : Stmt P C :=
  (StateT.run (removeLoopsM s) 0).fst

end
