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

The encoding produces two invariant VCs:

- **VC1** (`entry_invariant`): `assert(I)` at loop entry — `I` holds before
  the first iteration.
- **VC2** (`arbitrary_iter_maintain_invariant`): `assert(I)` after the body —
  `I` is preserved by one arbitrary iteration.

### Role of the measure (termination)

When a `decreases D` clause is provided, the encoding adds two termination VCs
inside the `if (G)` branch. Below, `m_old` is a fresh `init`-declared variable
(equivalent to a havoc) assumed equal to `D` before the body executes, so it
records the pre-body value of the measure.

- **VC3** (`measure_lb`): `assert(!(m_old < 0))` — the measure is non-negative,
  establishing a well-founded lower bound.
- **VC4** (`measure_decrease`): `assert(D < m_old)` — the measure strictly
  decreases from its pre-body value, ensuring the loop cannot run forever.

### Passive encoding recipe

Let `M` be the set of variables modified by the loop body.
When a `decreases D` clause is provided, let `m_old` be a fresh variable.

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
  [if decreases D:]
  init(m_old);          -- fresh unconstrained variable (≡ havoc)
  assume(m_old == D);   -- pin m_old to the pre-body value of the measure
  assert(!(m_old < 0)); -- VC3: measure is non-negative (well-foundedness)
  S;                    -- execute one iteration of the body
  assert(I);            -- VC2: I is maintained by S
  [if decreases D:]
  assert(D < m_old);    -- VC4: measure strictly decreases after body

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
  [HasNot P] [HasVarsImp P C] [HasHavoc P C] [HasInit P C] [HasPassiveCmds P C]
  [HasIdent P] [HasFvar P] [HasIntOrder P]
  (s : Stmt P C) : StateM Nat (Stmt P C) :=
  match s with
  | .loop guard measure invariants bss md => do
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
    -- Termination: when a measure expression is provided, emit
    --   VC3: assert(measure >= 0)  (well-foundedness lower bound)
    --   VC4: assert(measure < m_old)  (strict decrease after body)
    -- where m_old is a fresh variable pinned to the pre-body measure value.
    let termination_stmts ←
      match measure with
      | none => pure ([], [])
      | some m =>
        -- Variables with `$__` prefix are internal variables.
        let m_old_ident    := HasIdent.ident s!"$__loop_measure_{loop_num}"
        let m_old_expr     := HasFvar.mkFvar m_old_ident
        let init_m_old     := Stmt.cmd (HasInit.init m_old_ident HasIntOrder.intTy none md)
        let assume_m_old   := Stmt.cmd (HasPassiveCmds.assume
          s!"assume_measure_{loop_num}" (HasIntOrder.eq m_old_expr m) md)
        let assert_lb      := Stmt.cmd (HasPassiveCmds.assert
          s!"measure_lb_{loop_num}"
          (HasNot.not (HasIntOrder.lt m_old_expr HasIntOrder.zero)) md)
        let assert_decrease := Stmt.cmd (HasPassiveCmds.assert
          s!"measure_decrease_{loop_num}" (HasIntOrder.lt m m_old_expr) md)
        pure ([init_m_old, assume_m_old, assert_lb], [assert_decrease])
    let (pre_termination, post_termination) := termination_stmts
    let arbitrary_iter_facts := .block s!"arbitrary_iter_facts_{loop_num}"
      ([havocd, arbitrary_iter_assumes] ++ pre_termination ++
       body_statements ++ maintain_invariants ++ post_termination) {}
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
  [HasNot P] [HasVarsImp P C] [HasHavoc P C] [HasInit P C] [HasPassiveCmds P C]
  [HasIdent P] [HasFvar P] [HasIntOrder P]
  (ss : List (Stmt P C)) : StateM Nat (List (Stmt P C)) :=
  match ss with
  | [] => pure []
  | s :: ss => do
    let s ← Stmt.removeLoopsM s
    let ss ← Block.removeLoopsM ss
    pure (s :: ss)

end

def Stmt.removeLoops
  [HasNot P] [HasVarsImp P C] [HasHavoc P C] [HasInit P C] [HasPassiveCmds P C]
  [HasIdent P] [HasFvar P] [HasIntOrder P]
  (s : Stmt P C) : Stmt P C :=
  (StateT.run (removeLoopsM s) 0).fst

end -- public section

end Core
