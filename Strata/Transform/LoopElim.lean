/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.Stmt
public import Strata.Languages.Core.PipelinePhase
import Strata.Languages.Core.StatementSemantics

public section

namespace Imperative.LoopElim
open Lambda

/-- Label prefix for loop-elimination assumptions. -/
def loopElimAssumePrefix : String := "loopElimAssume_"
/-- Label prefix for loop-elimination asserts. -/
def loopElimAssertPrefix : String := "loopElimAssert_"
/-- Label prefix of blocks created by LoopElim. -/
def loopElimBlockPrefix : String := "loopElim_"

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
  (s : Stmt P C) : StateM StringGenState (Bool × Stmt P C) :=
  match s with
  | .loop guard measure invariants bss md => do
    let loop_num ← modifyGet (StringGenState.gen "loop")
    let assigned_vars := Block.modifiedVars bss
    let havocd : Stmt P C :=
      .block s!"{loopElimBlockPrefix}loop_havoc_{loop_num}" (assigned_vars.map (λ n => Stmt.cmd (HasHavoc.havoc n md))) {}
    let (_, body_statements) ← Block.removeLoopsM bss
    let entry_invariants := invariants.mapIdx fun i inv =>
      Stmt.cmd (HasPassiveCmds.assert s!"{loopElimAssertPrefix}{loop_num}_entry_invariant_{i}" inv md)
    let entry_invariant_assumes := invariants.mapIdx fun i inv =>
      Stmt.cmd (HasPassiveCmds.assume s!"{loopElimAssumePrefix}{loop_num}_entry_invariant_{i}" inv md)
    let first_iter_facts :=
      .block s!"{loopElimBlockPrefix}first_iter_asserts_{loop_num}" (entry_invariants ++ entry_invariant_assumes) {}
    let inv_assumes := invariants.mapIdx fun i inv =>
      Stmt.cmd (HasPassiveCmds.assume s!"{loopElimAssumePrefix}{loop_num}_invariant_{i}" inv md)
    let maintain_invariants := invariants.mapIdx fun i inv =>
      Stmt.cmd (HasPassiveCmds.assert s!"{loopElimAssertPrefix}{loop_num}_arbitrary_iter_maintain_invariant_{i}" inv md)
    -- Guard-specific parts: assume_guard, termination, not_guard
    let (guard_assumes, pre_termination, post_termination, exit_guard) ← match guard with
      | .det g => do
        let assume_guard := [Stmt.cmd (HasPassiveCmds.assume s!"{loopElimAssumePrefix}{loop_num}_guard" g md)]
        let termination_stmts ←
          match measure with
          | none => pure ([], [])
          | some m =>
            let m_old_ident    := HasIdent.ident s!"$__loop_measure_{loop_num}"
            let m_old_expr     := HasFvar.mkFvar m_old_ident
            let init_m_old     := Stmt.cmd (HasInit.init m_old_ident HasIntOrder.intTy .nondet md)
            let assume_m_old   := Stmt.cmd (HasPassiveCmds.assume
              s!"{loopElimAssumePrefix}{loop_num}_measure" (HasIntOrder.eq m_old_expr m) md)
            let assert_lb      := Stmt.cmd (HasPassiveCmds.assert
              s!"{loopElimAssertPrefix}{loop_num}_measure_lb"
              (HasNot.not (HasIntOrder.lt m_old_expr HasIntOrder.zero)) md)
            let assert_decrease := Stmt.cmd (HasPassiveCmds.assert
              s!"{loopElimAssertPrefix}{loop_num}_measure_decrease" (HasIntOrder.lt m m_old_expr) md)
            pure ([init_m_old, assume_m_old, assert_lb], [assert_decrease])
        let (pre, post) := termination_stmts
        let not_guard := [Stmt.cmd (HasPassiveCmds.assume s!"{loopElimAssumePrefix}{loop_num}_not_guard" (HasNot.not g) md)]
        pure (assume_guard, pre, post, not_guard)
      | .nondet =>
        -- Nondet loop: no guard assume, no termination, no not_guard
        pure ([], [], [], [])
    let arbitrary_iter_assumes := .block s!"{loopElimBlockPrefix}arbitrary_iter_assumes_{loop_num}"
      (guard_assumes ++ inv_assumes) md
    let arbitrary_iter_facts := .block s!"{loopElimBlockPrefix}arbitrary_iter_facts_{loop_num}"
      ([havocd, arbitrary_iter_assumes] ++ pre_termination ++
       body_statements ++ maintain_invariants ++ post_termination) {}
    let invariant_assumes := invariants.mapIdx fun i inv =>
      Stmt.cmd (HasPassiveCmds.assume s!"{loopElimAssumePrefix}{loop_num}_exit_invariant_{i}" inv md)
    let exit_state_assumes := [havocd] ++ exit_guard ++ invariant_assumes
    let loop_passive :=
      .ite guard (arbitrary_iter_facts :: exit_state_assumes) [] {}
    pure (true, .block s!"loop_{loop_num}" [first_iter_facts, loop_passive] {})
  | .ite c tss ess md => do
    let (c1, tss) ← Block.removeLoopsM tss
    let (c2, ess) ← Block.removeLoopsM ess
    pure (c1 || c2, .ite c tss ess md)
  | .block label bss md => do
    let (changed, bss) ← Block.removeLoopsM bss
    pure (changed, .block label bss md)
  | .cmd _ => pure (false, s)
  | .exit _ _ => pure (false, s)
  | .funcDecl _ _ => pure (false, s)
  | .typeDecl _ _ => pure (false, s)

def Block.removeLoopsM
  [HasNot P] [HasVarsImp P C] [HasHavoc P C] [HasInit P C] [HasPassiveCmds P C]
  [HasIdent P] [HasFvar P] [HasIntOrder P]
  (ss : List (Stmt P C)) : StateM StringGenState (Bool × List (Stmt P C)) :=
  match ss with
  | [] => pure (false, [])
  | s :: ss => do
    let (c1, s) ← Stmt.removeLoopsM s
    let (c2, ss) ← Block.removeLoopsM ss
    pure (c1 || c2, s :: ss)

end
end Imperative.LoopElim

namespace Core.LoopElim
open Imperative Lambda Imperative.LoopElim

/-!
# Specialization of removeLoopsM from Imperative.Stmt to Core
-/

private def removeLoopsDecls : List Core.Decl → StateM StringGenState (Bool × List Core.Decl)
  | [] => pure (false, [])
  | .proc proc md :: ds => do
    let (c1, body) ← Block.removeLoopsM proc.body
    let (c2, ds) ← removeLoopsDecls ds
    return (c1 || c2, .proc { proc with body := body } md :: ds)
  | d :: ds => do
    let (changed, ds) ← removeLoopsDecls ds
    return (changed, d :: ds)

/-- Eliminate loops in all procedures of a Core program by replacing each loop
    with assertions and assumptions about its invariants.
    Loop elimination as a `CoreTransformM` pass suitable for the pipeline.
    Returns `(changed, program, generated_assert_labels)`. -/
def loopElim (p : Core.Program) : Core.Transform.CoreTransformM (Bool × Core.Program) := do
  let σ ← get
  let ((changed, decls), cs') := StateT.run (removeLoopsDecls p.decls) σ.genState.cs
  set { σ with genState := { σ.genState with cs := cs' } }
  return (changed, { decls := decls })

end LoopElim

/-- Loop-elimination pipeline phase: replaces each loop with an
    invariant-based acyclic encoding. If the obligation's path includes
    labels from loop elimination, the loop was replaced by an
    over-approximation, so SAT models are demoted to unknown. -/
def loopElimPipelinePhase : Core.PipelinePhase where
  transform := Core.LoopElim.loopElim
  phase.name := "LoopElim"
  phase.getValidation obligation :=
    if Core.obligationHasLabelPrefix obligation Imperative.LoopElim.loopElimAssumePrefix
       || Core.obligationHasLabelPrefix obligation Imperative.LoopElim.loopElimAssertPrefix then
      .modelToValidate (fun _ => /- TODO -/ false)
    else .modelPreserving

end Core

end -- public section
