/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.PipelinePhase
import Strata.Languages.Core.StatementSemantics
import Strata.Transform.CoreTransform
import Strata.Transform.LoopElim

namespace Core
open Imperative Lambda

public section

/-- Prefix for variables freshly introduced. -/
def insertLoopInvAssertReservedPrefix : String := "$__loop"
/-- Label prefix for invariant/measure asserts inserted by
    `InsertLoopInvariantAsserts`. -/
def insertLoopInvAssertPrefix : String := "insertLoopInvAssert_"
/-- Label prefix for invariant/measure assumptions inserted by
    `InsertLoopInvariantAsserts`. -/
def insertLoopInvAssumePrefix : String := "insertLoopInvAssume_"

/-! ## Inserting loop invariant / measure assertions

This pass materializes the verification conditions that a loop's invariant
`I` and optional measure `D` impose, as explicit `assert`/`assume` statements
around and inside the loop, without removing the loop.

### Resulting shape

For `loop (G) decreases D invariant I { S }` this pass produces:

```
assert(I); assume(I);           -- before the loop (VC1 + zero-iteration assume)
loop (G) {                      -- invariants/measure stripped: now a "bare" loop
  assume(I);                    -- invariant at the arbitrary mid-loop state
  init(m_old); assume(m_old==D); assert(!(m_old<0));   -- measure setup + VC3
  S;                            -- original body
  assert(I);                    -- VC2
  assert(D < m_old);            -- VC4
}
assume(I /\ !G);                -- after the loop (exit invariant and negated guard)
```

Only deterministic loops (`while (G)`) may carry a `decreases` measure — a
nondeterministic loop (`while *`) iterates an arbitrary number of times and
cannot be shown to terminate by a measure, so this pass rejects a
nondeterministic loop that carries a measure with a diagnostic (`throw`).

### Role of the invariant

The invariant `I` is checked at entry and after an arbitrary iteration, and
assumed at the arbitrary mid-loop state and at loop exit:

- **VC1** (`entry_invariant`): `assert(I)` before the loop — `I` holds before
  the first iteration.
- **VC2** (`arbitrary_iter_maintain_invariant`): `assert(I)` at the bottom of
  the body — `I` is preserved by one arbitrary iteration.

Two assumptions accompany them: `assume(I)` before the loop (so `I` is
available on the zero-iteration path) and `assume(I)` at the top of the body
(the invariant holds at the arbitrary mid-loop state), plus `assume(I /\ !G)`
after the loop.

### Role of the measure (termination)

When a `decreases D` clause is present, a fresh `init`-declared variable
`m_old` records the pre-body value of `D`, and two termination VCs are added
inside the body:

- **VC3** (`measure_lb`): `assert(!(m_old < 0))` — the measure is non-negative.
- **VC4** (`measure_decrease`): `assert(D < m_old)` — the measure strictly
  decreases across the body.
-/

namespace InsertLoopInvariantAsserts

/-- Statistics keys tracked by the loop elimination transformation. -/
inductive Stats where
  | insertedAssertAssumes

#derive_prefixed_toString Stats "InsertLoopInvariantAsserts"

end InsertLoopInvariantAsserts

/-- Materialize a single loop's invariant/measure VCs as explicit
    `assert`/`assume` statements around and inside the loop, and clear the
    loop's `invariants`/`measure` metadata.

    Returns `some` (a list: entry asserts/assumes, the bare loop, exit assumes)
    for a loop that still carries invariants or a measure, and `none` otherwise.
    Throws if a nondeterministic loop (`while *`) carries a `decreases` measure,
    since such a loop cannot be shown to terminate by a measure. -/
def insertInvariantAsserts (s : Statement)
    : Transform.CoreTransformM (Option (List Statement)) := do
  match s with
  | .loop guard measure invariants bss md => do
    -- Nothing to materialize for a bare loop; let traversal descend into it.
    if invariants.isEmpty && measure.isNone then
      return none
    -- The guard expression for a deterministic loop; `none` for a
    -- nondeterministic (`while *`) loop.
    let guardExpr? : Option Expression.Expr := match guard with
      | .det g => some g
      | .nondet => none
    -- A `decreases` measure only makes sense for a deterministic guard: a
    -- nondeterministic loop iterates an arbitrary number of times, so it cannot
    -- be shown to terminate by a measure. Reject such an ill-formed loop with a
    -- diagnostic rather than silently dropping its invariants downstream.
    if measure.isSome && guardExpr?.isNone then
      throw (Strata.DiagnosticModel.fromFormat
        f!"nondeterministic loop (`while *`) cannot carry a `decreases` measure: \
it iterates an arbitrary number of times and so cannot be shown to terminate")
    let loop_num ← genLoopNum
    -- The per-invariant source label is carried through as part of the suffix
    -- (alongside the index `i`, which guarantees uniqueness when source labels
    -- coincide or are empty) so each generated assert/assume preserves a stable
    -- reference to the source invariant.
    let invSuffix : Nat → String → String := fun i lbl =>
      if lbl.isEmpty then toString i else s!"{i}_{lbl}"
    -- Per-invariant source provenance, threaded through the loop metadata by the
    -- Laurel→Core translation (in invariant order). When present, each
    -- invariant's generated assert/assume is attributed to that invariant's own
    -- source location instead of the whole loop; otherwise we fall back to the
    -- loop metadata `md`. A size mismatch degrades gracefully via the index
    -- lookup below rather than mis-attributing ranges.
    let invProvs := MetaData.getInvariantProvenances md
    let invMd : Nat → MetaData Expression := fun i =>
      match invProvs[i]? with
      | some (p@(.loc ..)) => MetaData.ofProvenance p
      | _ => md
    -- Before the loop: assert(I) (VC1) and assume(I) (zero-iteration path).
    let entry_asserts := invariants.mapIdx fun i (lbl, inv) =>
      Stmt.cmd (HasPassiveCmds.assert s!"{insertLoopInvAssertPrefix}entry_invariant_{loop_num}_{invSuffix i lbl}" inv (invMd i))
    let entry_assumes := invariants.mapIdx fun i (lbl, inv) =>
      Stmt.cmd (HasPassiveCmds.assume s!"{insertLoopInvAssumePrefix}entry_invariant_{loop_num}_{invSuffix i lbl}" inv (invMd i))
    -- Top of the body: assume(I) (invariant at the arbitrary mid-loop state).
    let mid_assumes := invariants.mapIdx fun i (lbl, inv) =>
      Stmt.cmd (HasPassiveCmds.assume s!"{insertLoopInvAssumePrefix}invariant_{loop_num}_{invSuffix i lbl}" inv (invMd i))
    -- Bottom of the body: assert(I) (VC2, invariant maintained).
    let maintain_asserts := invariants.mapIdx fun i (lbl, inv) =>
      Stmt.cmd (HasPassiveCmds.assert s!"{insertLoopInvAssertPrefix}arbitrary_iter_maintain_invariant_{loop_num}_{invSuffix i lbl}" inv (invMd i))
    -- After the loop: assume(I ∧ ¬g) — the invariant, and the negated guard, at
    -- the exit state. The `¬g` conjunct is only added for a deterministic
    -- guard; a nondeterministic loop has no guard to negate.
    let exit_not_guard := match guardExpr? with
      | some g => [Stmt.cmd (HasPassiveCmds.assume
          s!"{insertLoopInvAssumePrefix}exit_not_guard_{loop_num}" (HasBoolOps.not g) md)]
      | none => []
    let exit_assumes := (invariants.mapIdx fun i (lbl, inv) =>
      Stmt.cmd (HasPassiveCmds.assume s!"{insertLoopInvAssumePrefix}exit_invariant_{loop_num}_{invSuffix i lbl}" inv (invMd i)))
      ++ exit_not_guard
    -- Measure: init m_old := nondet; assume(m_old == D); assert(!(m_old<0)) at
    -- the top of the body, and assert(D < m_old) at the bottom.
    let (measure_pre, measure_post) := match measure with
      | none => ([], [])
      | some m =>
        let m_old_ident    := HasIdent.ident s!"{insertLoopInvAssertReservedPrefix}_measure_{loop_num}"
        let m_old_expr     := HasFvar.mkFvar m_old_ident
        let init_m_old     := Stmt.cmd (HasInit.init m_old_ident HasInt.intTy .nondet md)
        let assume_m_old   := Stmt.cmd (HasPassiveCmds.assume
          s!"{insertLoopInvAssumePrefix}measure_{loop_num}" (HasIntOps.eq m_old_expr m) md)
        let assert_lb      := Stmt.cmd (HasPassiveCmds.assert
          s!"{insertLoopInvAssertPrefix}measure_lb_{loop_num}"
          (HasBoolOps.not (HasIntOps.lt m_old_expr HasInt.zero)) md)
        let assert_decrease := Stmt.cmd (HasPassiveCmds.assert
          s!"{insertLoopInvAssertPrefix}measure_decrease_{loop_num}" (HasIntOps.lt m m_old_expr) md)
        ([init_m_old, assume_m_old, assert_lb], [assert_decrease])
    -- Decorated body and bare loop (invariants/measure cleared).
    let new_body := mid_assumes ++ measure_pre ++ bss ++ maintain_asserts ++ measure_post
    let bare_loop : Statement := .loop guard none [] new_body md
    -- Count assert/assume statements inserted (init is not an assert/assume;
    -- the measure contributes assume_m_old + assert_lb + assert_decrease = 3).
    let numAssertAssumes := entry_asserts.length + entry_assumes.length +
      mid_assumes.length + maintain_asserts.length + exit_assumes.length +
      (if measure.isSome then 3 else 0)
    Transform.incrementStat s!"{InsertLoopInvariantAsserts.Stats.insertedAssertAssumes}" numAssertAssumes
    return some (entry_asserts ++ entry_assumes ++ [bare_loop] ++ exit_assumes)
  | _ => return none

/-- Insert loop invariant/measure assertions across all procedures of a Core
    program, iterating to a fixed point so that loops nested inside loop bodies
    are also decorated. Returns whether anything changed and the transformed
    program. -/
def insertLoopInvariantAsserts (p : Program) : Transform.CoreTransformM (Bool × Program) :=
  Transform.runProgramUntil insertInvariantAsserts p

/-- Pipeline phase that materializes loop invariant/measure verification
    conditions. -/
def insertLoopInvariantAssertsPipelinePhase : PipelinePhase where
  transform := insertLoopInvariantAsserts
  phase.name := "InsertLoopInvariantAsserts"
  phase.getValidation obligation :=
    if obligationHasLabelPrefix obligation insertLoopInvAssumePrefix then
      .modelToValidate (fun _ => /- TODO -/ false)
    else .modelPreserving

end -- public section

end Core
