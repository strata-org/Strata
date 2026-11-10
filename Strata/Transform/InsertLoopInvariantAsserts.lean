/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import Strata.Pipeline.Messages

public import Strata.Languages.Core.PipelinePhase
import Strata.Languages.Core.StatementSemantics
import Strata.Transform.CoreTransform
import Strata.Transform.LoopElim

namespace Core
open Imperative

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
  init(m_old := D); assert(!(m_old<0));   -- measure snapshot + VC3
  S;                            -- original body
  assert(I);                    -- VC2
  assert(D < m_old);            -- VC4
}
assume(I /\ !G);                -- after the loop (exit invariant and negated guard)
```

A nondeterministic loop (`while *`) may carry a `decreases` measure. A measure
that decreases across the body and stays non-negative bounds the number of
iterations however the guard decides to continue, and a nondeterministic guard
can only stop the loop sooner; a `while *` whose body breaks out is how a
bounded loop with a non-guard exit condition gets written. The mechanics agree:
none of the four VCs below mentions the guard, and the one statement that does,
the exit `assume(!G)`, is already omitted for a nondeterministic guard.

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
`m_old` records the pre-body value of `D` — a deterministic `init m_old := D`,
which leaves `m_old` the single value an unconstrained `init` pinned by an
`assume(m_old == D)` would leave it, and draws no nondeterministic value. Two
termination VCs are added inside the body:

- **VC3** (`measure_lb`): `assert(!(m_old < 0))` — the measure is non-negative.
- **VC4** (`measure_decrease`): `assert(D < m_old)` — the measure strictly
  decreases across the body.

Neither mentions the guard, so a measure says as much about a `while *` loop as
about a `while G` one: a measure that decreases across the body and stays
non-negative bounds the number of iterations, and a nondeterministic guard can
only stop the loop sooner than that bound.
-/

namespace InsertLoopInvariantAsserts

/-- Statistics keys tracked by the loop elimination transformation. -/
inductive Stats where
  | insertedAssertAssumes

#derive_prefixed_toString Stats "InsertLoopInvariantAsserts"

end InsertLoopInvariantAsserts

end -- public section

end Core

/-! ### The statements inserted for one loop

The checked form of one loop (`Stmt.invChecked`), as the module note above describes it.  The
label of each check carries the index `i` of its invariant, which keeps labels unique when source
labels coincide or are empty, and the invariant's source label, so that each check refers back to
its invariant; it carries the invariant's own source location (`MetaData.invariantMd`), falling
back to the loop's.  The definitions are generic over the expression language, so that the
correctness proof of the pass reasons about them over Imperative statements. -/

namespace Imperative

public section

variable {P : PureExpr} {C : Type}

namespace InsertLoopInvAsserts

/-- The label suffix of the invariant at index `i` with source label `lbl`. -/
def invSuffix (i : Nat) (lbl : String) : String :=
  if lbl.isEmpty then toString i else s!"{i}_{lbl}"

/-- The label of the assertion, before loop `n`, of the invariant at index `i` with source
    label `lbl`. -/
def entryAssertLabel (n : String) (i : Nat) (lbl : String) : String :=
  s!"{Core.insertLoopInvAssertPrefix}entry_invariant_{n}_{invSuffix i lbl}"

/-- The label of the assumption, before loop `n`, of the invariant at index `i` with source
    label `lbl`. -/
def entryAssumeLabel (n : String) (i : Nat) (lbl : String) : String :=
  s!"{Core.insertLoopInvAssumePrefix}entry_invariant_{n}_{invSuffix i lbl}"

/-- The label of the assumption, at the start of an iteration of loop `n`, of the invariant at
    index `i` with source label `lbl`. -/
def midAssumeLabel (n : String) (i : Nat) (lbl : String) : String :=
  s!"{Core.insertLoopInvAssumePrefix}invariant_{n}_{invSuffix i lbl}"

/-- The label of the assertion, at the end of an iteration of loop `n`, of the invariant at index
    `i` with source label `lbl`. -/
def maintainAssertLabel (n : String) (i : Nat) (lbl : String) : String :=
  s!"{Core.insertLoopInvAssertPrefix}arbitrary_iter_maintain_invariant_{n}_{invSuffix i lbl}"

/-- The label of the assumption, after loop `n`, of the invariant at index `i` with source label
    `lbl`. -/
def exitAssumeLabel (n : String) (i : Nat) (lbl : String) : String :=
  s!"{Core.insertLoopInvAssumePrefix}exit_invariant_{n}_{invSuffix i lbl}"

/-- The prefix of the names of the variables recording loop measures. -/
@[expose] def measurePrefix : String := s!"{Core.insertLoopInvAssertReservedPrefix}_measure_"

/-- The variable recording the measure of loop `n` before an iteration. -/
def measureIdent [HasIdent P] (n : String) : P.Ident :=
  HasIdent.ident (measurePrefix ++ n)

/-- The prefixes of the measure snapshot variables, which the source must not use: the only
    names the checks introduce are snapshot variables (`measureIdent`), which start with
    `measurePrefix`. -/
@[expose] def prefixesReserved : List String := [measurePrefix]

/-- The variables the checks of loop `n` with measure `measure` define: the measure snapshot
    when there is a measure. -/
def measureVars [HasIdent P] (n : String) : Option P.Expr → List P.Ident
  | some _ => [measureIdent n]
  | none => []

/-- The assertions of the invariants `inv` of loop `n` before the loop. -/
def entryAsserts [HasPassiveCmds P C] (n : String) (inv : List (String × P.Expr))
    (md : MetaData P) : List (Stmt P C) :=
  inv.mapIdx fun i (lbl, e) =>
    Stmt.cmd (HasPassiveCmds.assert (entryAssertLabel n i lbl) e (md.invariantMd i))

/-- The assumptions of the invariants `inv` of loop `n` before the loop. -/
def entryAssumes [HasPassiveCmds P C] (n : String) (inv : List (String × P.Expr))
    (md : MetaData P) : List (Stmt P C) :=
  inv.mapIdx fun i (lbl, e) =>
    Stmt.cmd (HasPassiveCmds.assume (entryAssumeLabel n i lbl) e (md.invariantMd i))

/-- The assumptions of the invariants `inv` of loop `n` at the start of an iteration. -/
def midAssumes [HasPassiveCmds P C] (n : String) (inv : List (String × P.Expr))
    (md : MetaData P) : List (Stmt P C) :=
  inv.mapIdx fun i (lbl, e) =>
    Stmt.cmd (HasPassiveCmds.assume (midAssumeLabel n i lbl) e (md.invariantMd i))

/-- The assertions of the invariants `inv` of loop `n` at the end of an iteration. -/
def maintainAsserts [HasPassiveCmds P C] (n : String) (inv : List (String × P.Expr))
    (md : MetaData P) : List (Stmt P C) :=
  inv.mapIdx fun i (lbl, e) =>
    Stmt.cmd (HasPassiveCmds.assert (maintainAssertLabel n i lbl) e (md.invariantMd i))

/-- The assumptions of the invariants `inv` and, for a deterministic guard, of the negation of
    the guard of loop `n` after the loop. -/
def exitAssumes [HasPassiveCmds P C] [HasBoolOps P] (n : String) (guard : ExprOrNondet P)
    (inv : List (String × P.Expr)) (md : MetaData P) : List (Stmt P C) :=
  (inv.mapIdx fun i (lbl, e) =>
    Stmt.cmd (HasPassiveCmds.assume (exitAssumeLabel n i lbl) e (md.invariantMd i))) ++
  match guard with
  | .det g => [Stmt.cmd (HasPassiveCmds.assume
      s!"{Core.insertLoopInvAssumePrefix}exit_not_guard_{n}" (HasBoolOps.not g) md)]
  | .nondet => []

/-- At the start of an iteration of loop `n` with measure `m`: the snapshot of the measure and
    the assertion that it is not negative. -/
def measurePre [HasIdent P] [HasFvar P] [HasFvars P] [HasBoolOps P] [HasInt P]
    [HasIntOps P] [HasInit P C] [HasPassiveCmds P C] (n : String) (measure : Option P.Expr)
    (md : MetaData P) : List (Stmt P C) :=
  match measure with
  | none => []
  | some m =>
    [Stmt.cmd (HasInit.init (measureIdent n) HasInt.intTy (.det m) md),
     Stmt.cmd (HasPassiveCmds.assert s!"{Core.insertLoopInvAssertPrefix}measure_lb_{n}"
      (HasBoolOps.not (HasIntOps.lt (HasFvar.mkTypedFvar (measureIdent n) HasInt.intTy)
        HasInt.zero)) md)]

/-- At the end of an iteration of loop `n` with measure `m`: the assertion that the measure
    decreased. -/
def measurePost [HasIdent P] [HasFvar P] [HasFvars P] [HasBoolOps P] [HasInt P]
    [HasIntOps P] [HasPassiveCmds P C] (n : String) (measure : Option P.Expr)
    (md : MetaData P) : List (Stmt P C) :=
  match measure with
  | none => []
  | some m =>
    [Stmt.cmd (HasPassiveCmds.assert s!"{Core.insertLoopInvAssertPrefix}measure_decrease_{n}"
      (HasIntOps.lt m (HasFvar.mkTypedFvar (measureIdent n) HasInt.intTy)) md)]

/-- The body of the checked loop `n`: the body `body` between the checks of the invariants
    `inv` and of the measure `measure`. -/
def loopBody [HasIdent P] [HasFvar P] [HasFvars P] [HasBoolOps P] [HasInt P]
    [HasIntOps P] [HasInit P C] [HasPassiveCmds P C] (n : String) (measure : Option P.Expr)
    (inv : List (String × P.Expr)) (body : List (Stmt P C)) (md : MetaData P) :
    List (Stmt P C) :=
  midAssumes n inv md ++ measurePre n measure md ++ body ++ maintainAsserts n inv md ++
    measurePost n measure md

end InsertLoopInvAsserts

open InsertLoopInvAsserts in
/-- The statements checking the invariants `inv` and the measure `measure` of loop `n` with
    guard `guard`, body `body` and metadata `md`: the loop without invariants and measure
    between the checks before, during and after it (see the module note above). -/
def Stmt.invChecked [HasIdent P] [HasFvar P] [HasFvars P] [HasBoolOps P] [HasInt P]
    [HasIntOps P] [HasInit P C] [HasPassiveCmds P C] (n : String) (guard : ExprOrNondet P)
    (measure : Option P.Expr) (inv : List (String × P.Expr)) (body : List (Stmt P C))
    (md : MetaData P) : List (Stmt P C) :=
  entryAsserts n inv md ++ entryAssumes n inv md ++
    [.loop guard none [] (loopBody n measure inv body md) md] ++ exitAssumes n guard inv md

end -- public section

end Imperative

namespace Core
open Imperative

public section

/-- Materialize a single loop's invariant/measure VCs as explicit
    `assert`/`assume` statements around and inside the loop, and clear the
    loop's `invariants`/`measure` metadata.

    Returns `some` (a list: entry asserts/assumes, the bare loop, exit assumes;
    `Stmt.invChecked`) for a loop that still carries invariants or a measure, and
    `none` otherwise.
    A `decreases` measure works for a nondeterministic guard as well as a
    deterministic one: the measure VCs never mention the guard, and a measure
    that decreases across the body and stays non-negative bounds the number of
    iterations however the guard decides to continue. -/
def insertInvariantAsserts (s : Statement)
    : Transform.CoreTransformM (Option (List Statement)) := do
  match s with
  | .loop guard measure invariants bss md => do
    -- Nothing to materialize for a bare loop; let traversal descend into it.
    if invariants.isEmpty && measure.isNone then
      return none
    let loop_num ← genLoopNum
    -- Count assert/assume statements inserted (init is not an assert/assume;
    -- the measure contributes assert_lb + assert_decrease = 2).
    let numAssertAssumes :=
      (InsertLoopInvAsserts.entryAsserts (C := Command) loop_num invariants md).length +
      (InsertLoopInvAsserts.entryAssumes (C := Command) loop_num invariants md).length +
      (InsertLoopInvAsserts.midAssumes (C := Command) loop_num invariants md).length +
      (InsertLoopInvAsserts.maintainAsserts (C := Command) loop_num invariants md).length +
      (InsertLoopInvAsserts.exitAssumes (C := Command) loop_num guard invariants md).length +
      (if measure.isSome then 2 else 0)
    Transform.incrementStat s!"{InsertLoopInvariantAsserts.Stats.insertedAssertAssumes}" numAssertAssumes
    return some (Stmt.invChecked loop_num guard measure invariants bss md)
  | _ => return none

/-- Insert loop invariant/measure assertions across all procedures of a Core
    program, iterating so that loops nested inside loop bodies are also
    decorated. Each iteration decorates the outermost loops not decorated yet, so
    the iterations are bounded by `numLoops p + 1`: at least the loop nesting
    depth, and at least one, so a CFG procedure body is rejected even when `p`
    has no loops. Returns whether anything changed and the transformed
    program. -/
def insertLoopInvariantAsserts (p : Program) : Transform.CoreTransformM (Bool × Program) :=
  Transform.runProgramUntil insertInvariantAsserts p (maxIters := some (numLoops p + 1))

/-- Pipeline phase that materializes loop invariant/measure verification
    conditions. -/
def insertLoopInvariantAssertsPipelinePhase : PipelinePhase where
  transform := insertLoopInvariantAsserts
  phase.name := "insertLoopInvariantAsserts"
  phase.getValidation obligation :=
    if obligationHasLabelPrefix obligation insertLoopInvAssumePrefix then
      .modelToValidate (fun _ => /- TODO -/ false)
    else .modelPreserving
  -- The measure snapshot is an `init`, which declares rather than reassigns, so
  -- `staticSingleAssignment` survives; the invariants, measure and guard are
  -- relocated unchanged, so no redex appears.
  requires := factSet![.noCFGBodies]
  establishes := factSet![.noLoopInvariants, .noLoopMeasures]
  preserves := factSet![.noCFGBodies, .noCalls, .noLoops, .staticSingleAssignment,
                      .noBetaRedexes, .noPrecondsFromFuncs, .noNondetGuards, .noProcedureContracts,
                         .noPolymorphicProcedures,
                         .noPolymorphicFunctions, .typeAnnotated]

end -- public section

end Core
