/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.PipelinePhase
public import Strata.DL.Util.StringGen
import Strata.Languages.Core.StatementSemantics
import Strata.Transform.CoreTransform

namespace Core
open Imperative Lambda

public section

/-- Label prefix for loop-elimination assumptions. -/
def loopElimAssumePrefix : String := "loopElimAssume_"
/-- Label prefix of blocks created by LoopElim. -/
def loopElimBlockPrefix : String := "loopElim_"

namespace LoopElim

/-- Statistics keys tracked by the loop elimination transformation. -/
inductive Stats where
  | erasedLoops

#derive_prefixed_toString Stats "LoopElim"

end LoopElim

/-- Generate a fresh, globally-unique loop number by drawing from the shared
    `CoreGenState` counter in `CoreTransformState`. Because the counter is
    shared across the whole transform pipeline (and persists across repeated
    runs of loop elimination), loop numbers are unique but need not start at
    zero — different loops always get different numbers. -/
def genLoopNum : Transform.CoreTransformM String := do
  let genLoopIdent : CoreGenM CoreIdent := CoreGenState.gen ("loop" : CoreIdent)
  let id ← genLoopIdent
  return id.name

/-- The block labels that loop elimination mints for a given `loop_num`.
    Used to detect collisions with labels already present in a loop body. -/
def loopElimGeneratedBlockLabels (loop_num : String) : List String :=
  [ s!"{loopElimBlockPrefix}havoc_{loop_num}",
    s!"{loopElimBlockPrefix}arbitrary_iter_facts_{loop_num}" ]

/-- Whether any exit target in `bss` collides with a block label that loop
    elimination would mint for `loop_num`.  Such a collision would silently
    redirect an in-body `exit` to one of the freshly created blocks. -/
def hasLabelConflict {P : PureExpr} {C : Type} (loop_num : String) (bss : List (Stmt P C)) : Bool :=
  let bodyLabels := Block.labels bss
  (loopElimGeneratedBlockLabels loop_num).any bodyLabels.contains

/-! ## Loop elimination

This pass converts a loop into an acyclic passive statement suitable for
symbolic verification. It introduces `havoc`s over the loop-carried variables
and guard assumptions.

### Passive encoding recipe

Let `M` be the set of variables modified by the loop body. A loop

```
loop (G) { B }
```

is replaced by

```
if (G) {
  havoc(M);     -- non-deterministically pick a mid-loop state
  assume(G);    -- guard holds at this state (live iteration)
  B;            -- one arbitrary iteration (already decorated by pass 1)
  havoc(M);     -- non-deterministically pick an exit state
  assume(¬G);   -- guard is false at exit (loop has terminated)
}
```

For a `.nondet` guard, the guard assumptions are omitted.

Any invariant `assert`/`assume` statements that pass 1 inserted before/after
the loop remain outside this `if`, and those it inserted into the body ride
along inside `B`. The mid-loop and exit states are modeled with two independent
`havoc`s, so the exit state is unconstrained apart from `¬G` (and whatever
invariant assumptions pass 1 left after the loop).
-/

/-- Convert a single loop into its passive acyclic form (see the module note).
    Returns `some` for a `.loop` — replaced by an `if` with havocs and guard
    assumptions — and `none` for every other statement. Throws if the loop still
    carries invariants or a measure, i.e. `InsertLoopInvariantAsserts` has not
    run first. -/
def removeLoop (s : Statement)
    : Transform.CoreTransformM (Option (List Statement)) := do
  match s with
  | .loop guard measure invariants bss md => do
    if !invariants.isEmpty || measure.isSome then
      throw (Strata.DiagnosticModel.fromFormat
        f!"LoopElim invoked on a loop that still carries invariants/measure; \
run InsertLoopInvariantAsserts first (or use the built-in verify pipeline)")
    let loop_num ← genLoopNum
    -- Reject loop bodies whose block/exit labels collide with the blocks we are
    -- about to mint, which would otherwise silently redirect control flow.
    if hasLabelConflict loop_num bss then
      throw (Strata.DiagnosticModel.fromFormat
        f!"Generated loop block label conflicts with exit target in loop body (loop {loop_num})")
    -- Havoc only loop-carried variables. Variables declared inside the loop
    -- body are block-local and should not be treated as pre-existing state by
    -- the passive loop encoding.
    let local_defs := Block.definedVars bss false
    let assigned_vars :=
      (Block.modifiedVars bss).filter (fun v => v ∉ local_defs)
    -- All of the replaced statements reuse the metadata md.
    let havocd : Statement :=
      .block s!"{loopElimBlockPrefix}havoc_{loop_num}"
        (assigned_vars.map (fun n => Stmt.cmd (HasHavoc.havoc n md))) {}
    -- Guard assumptions re-establish the guard after each havoc (a havoc breaks
    -- the connection between the modified variables and the guard). For a nondet
    -- guard there is nothing to assume.
    let (assume_guard, exit_guard) := match guard with
      | .det g =>
        ([Stmt.cmd (HasPassiveCmds.assume s!"{loopElimAssumePrefix}guard_{loop_num}" g md)],
         [Stmt.cmd (HasPassiveCmds.assume s!"{loopElimAssumePrefix}not_guard_{loop_num}" (HasBoolOps.not g) md)])
      | .nondet => ([], [])
    let arbitrary_iter_facts :=
      .block s!"{loopElimBlockPrefix}arbitrary_iter_facts_{loop_num}"
        ([havocd] ++ assume_guard ++ bss) {}
    let loop_passive :=
      .ite guard (arbitrary_iter_facts :: ([havocd] ++ exit_guard)) [] {}
    Transform.incrementStat s!"{LoopElim.Stats.erasedLoops}"
    return some [loop_passive]
  | _ => return none

/-- Loop-elimination pass suitable for the pipeline: replace every loop in the
    program with its acyclic passive encoding, iterating to a fixed point so
    that loops nested inside loop bodies are also eliminated. Returns whether
    any loop was eliminated and the transformed program. Throws if a loop body
    contains a label that collides with a block minted by loop elimination. -/
def loopElim (p : Program) : Transform.CoreTransformM (Bool × Program) :=
  Transform.runProgramUntil removeLoop p

/-- Loop-elimination pipeline phase: replaces each loop with an acyclic
    encoding. -/
def loopElimPipelinePhase : PipelinePhase where
  transform := loopElim
  phase.name := "LoopElim"
  phase.getValidation obligation :=
    if obligationHasLabelPrefix obligation loopElimAssumePrefix then
      .modelToValidate (fun _ => /- TODO -/ false)
    else .modelPreserving

end -- public section

end Core
