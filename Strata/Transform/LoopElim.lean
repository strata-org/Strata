/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import Strata.Pipeline.Messages

public import Strata.Languages.Core.PipelinePhase
public import Strata.DL.Util.StringGen
import Strata.Languages.Core.StatementSemantics
import Strata.Transform.CoreTransform

namespace Core
open Imperative

public section

/-- Prefix reserved for the labels loop elimination generates. The pass rejects a loop body
    with an `exit` whose target starts with this prefix, which a generated block would
    otherwise capture. -/
def loopElimPrefix : String := "$__loopElim"
/-- Label prefix for loop-elimination assumptions. -/
def loopElimAssumePrefix : String := "$__loopElimAssume_"
/-- Label prefix of blocks created by LoopElim. -/
def loopElimBlockPrefix : String := "$__loopElim_"

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
      throw (Strata.Message.fromFormat
        f!"LoopElim invoked on a loop that still carries invariants/measure; \
run InsertLoopInvariantAsserts first (or use the built-in verify pipeline)")
    let loop_num ← genLoopNum
    -- Reject loop bodies with an exit to a label of the reserved prefix, which the blocks we
    -- are about to mint would otherwise capture, silently redirecting control flow.
    if (Block.labels bss).any (·.startsWith loopElimPrefix) then
      throw (Strata.Message.fromFormat
        f!"Exit target in loop body uses the reserved label prefix {loopElimPrefix} \
          (loop {loop_num})")
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

/-- The number of loops in the structured procedure bodies of `p`; it bounds the loop
    nesting depth. -/
def numLoops (p : Program) : Nat :=
  p.decls.foldl (fun n d => match d with
    | .proc proc _ => match proc.body with
      | .structured ss => n + Block.numLoops ss
      | .cfg _ => n
    | _ => n) 0

/-- Loop-elimination pass suitable for the pipeline: replace every loop in the
    program with its acyclic passive encoding, iterating to a fixed point so
    that loops nested inside loop bodies are also eliminated. The iterations are
    bounded by `numLoops p + 1`: at least the loop nesting depth, and at least one,
    so a CFG procedure body is rejected even when `p` has no loops. Returns whether
    any loop was eliminated and the transformed program. Throws if an `exit` in a loop body
    targets a label starting with `loopElimPrefix`, which generated blocks use. -/
def loopElim (p : Program) : Transform.CoreTransformM (Bool × Program) :=
  Transform.runProgramUntil removeLoop p (maxIters := some (numLoops p + 1))

/-- Loop-elimination pipeline phase: replaces each loop with an acyclic
    encoding. -/
def loopElimPipelinePhase : PipelinePhase where
  transform := loopElim
  phase.name := "loopElim"
  phase.getValidation obligation :=
    if obligationHasLabelPrefix obligation loopElimAssumePrefix then
      .modelToValidate (fun _ => /- TODO -/ false)
    else .modelPreserving
  -- Iterating to a fixed point dissolves nested loops as well, so a successful
  -- run leaves none; what replaces them havocs, which is why
  -- `staticSingleAssignment` is not claimed.
  requires := factSet![.noCFGBodies, .noLoopInvariants, .noLoopMeasures]
  establishes := factSet![.noLoops]
  preserves := factSet![.noCFGBodies, .noCalls, .noLoopInvariants,
                      .noLoopMeasures, .noBetaRedexes, .noPrecondsFromFuncs, .noNondetGuards,
                      .noProcedureContracts,
                         .noPolymorphicProcedures,
                         .noPolymorphicFunctions, .typeAnnotated]

end -- public section

end Core
