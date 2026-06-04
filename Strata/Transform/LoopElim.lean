/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.Stmt
public import Strata.DL.Util.LabelGen
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
/-- The identifier prefix that loop-elimination claims for its fresh names
    (e.g. measure-snapshot variables `$__loop_measure_<n>`). Any caller of
    `loopElim_overapproximatesAggressive` must include this in `reserved`. -/
def loopElimReservedPrefix : String := "$__loop"

/-- Statistics keys tracked by the loop elimination transformation. -/
inductive Stats where
  | erasedLoops
  | insertedAssertAssumes

#derive_prefixed_toString Stats "LoopElim"

/-- State threaded through loop elimination.
    `gen` is a `StringGenState` used to mint unique loop numbers and block
    labels; `statistics` accumulates per-pass counters. -/
structure LoopElimState where
  gen : StringGenState := .emp
  statistics : Statistics := {}

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

/-- Generate a fresh loop number, drawing from the embedded `StringGenState`. -/
def genLoopNum : StateM LoopElimState String := fun s =>
  let (nm, gen') := StringGenState.gen "loop" s.gen
  (nm, { s with gen := gen' })

/-- Increment a statistic key by `n` (default 1). -/
def bumpStat (key : String) (n : Nat := 1) : StateM LoopElimState Unit :=
  modify fun s => { s with statistics := s.statistics.increment key n }

/-! ## Auxiliary builders for the loop-elimination encoding.

These pure (non-monadic) functions construct the various pieces of the passive
loop encoding. Splitting them out lets us prove focused lemmas like
"`Block.modifiedVars (havocBlock ...) = filtered_vars`" without having to dig
through a giant monadic term. -/

/-- The per-invariant label suffix: `"i"` if the source label is empty, else
    `"i_lbl"` (where `i` is the index). Used by all invariant-related builders. -/
@[expose, reducible] def invSuffix (i : Nat) (lbl : String) : String :=
  if lbl.isEmpty then toString i else s!"{i}_{lbl}"

/-- Termination stmts when guard is `.det g` and measure is `some m`:
    `init m_old` and `assert(¬(m_old < 0))` go into the prefix; `assert(m < m_old)`
    goes into the suffix. -/
@[expose] def buildTerminationStmtsSome
    [HasPassiveCmds P C] [HasInit P C] [HasIdent P] [HasFvar P]
    [HasBool P] [HasFvars P] [HasInt P] [HasIntOps P] [HasBoolOps P]
    (loop_num : String) (m : P.Expr) (md : MetaData P) :
    List (Stmt P C) × List (Stmt P C) :=
  let m_old_ident := HasIdent.ident s!"{loopElimReservedPrefix}_measure_{loop_num}"
  let m_old_expr := HasFvar.mkFvar m_old_ident
  let init_m_old := Stmt.cmd (HasInit.init m_old_ident HasInt.intTy (.det m) md)
  let assert_lb := Stmt.cmd (HasPassiveCmds.assert
    s!"{loopElimAssertPrefix}{loop_num}_measure_lb"
    (HasBoolOps.not (HasIntOps.lt m_old_expr HasInt.zero)) md)
  let assert_decrease := Stmt.cmd (HasPassiveCmds.assert
    s!"{loopElimAssertPrefix}{loop_num}_measure_decrease" (HasIntOps.lt m m_old_expr) md)
  ([init_m_old, assert_lb], [assert_decrease])

/-- The fresh measure-snapshot identifier for a given loop number.
    Returns `Some` when measure is `Some _` and freshness check passes. -/
@[expose, reducible] def measureOldIdent [HasIdent P] (loop_num : String) : P.Ident :=
  HasIdent.ident s!"{loopElimReservedPrefix}_measure_{loop_num}"

/-- The full output of the loop-elimination encoding for one loop:
    `block loop_label [first_iter_facts, loop_passive] {}`, where
    `first_iter_facts` collects entry-invariant asserts/assumes and
    `loop_passive` is the `if (G)` arbitrary-iteration encoding. -/
@[expose, reducible] def buildLoopOutput
    [HasVarsImp P C] [HasHavoc P C] [HasPassiveCmds P C] [DecidableEq P.Ident]
    (loop_num : String) (guard : ExprOrNondet P) (bss : List (Stmt P C))
    (assumeGuard preTermination postTermination exitGuard : List (Stmt P C))
    (invariants : List (String × P.Expr))
    (md : MetaData P) : Stmt P C :=
  let local_defs := Block.definedVars bss false
  let assigned_vars := (Block.modifiedVars bss).filter (fun v => v ∉ local_defs)
  let havocd : Stmt P C := .block s!"{loopElimBlockPrefix}loop_havoc_{loop_num}"
    (assigned_vars.map (fun n => Stmt.cmd (HasHavoc.havoc n md))) {}
  let entry_invariants := invariants.mapIdx fun i lp =>
    Stmt.cmd (HasPassiveCmds.assert
      s!"{loopElimAssertPrefix}{loop_num}_entry_invariant_{invSuffix i lp.1}" lp.2 md)
  let entry_invariant_assumes := invariants.mapIdx fun i lp =>
    Stmt.cmd (HasPassiveCmds.assume
      s!"{loopElimAssumePrefix}{loop_num}_entry_invariant_{invSuffix i lp.1}" lp.2 md)
  let first_iter_facts : Stmt P C :=
    .block s!"{loopElimBlockPrefix}first_iter_asserts_{loop_num}"
      (entry_invariants ++ entry_invariant_assumes) {}
  let inv_assumes := invariants.mapIdx fun i lp =>
    Stmt.cmd (HasPassiveCmds.assume
      s!"{loopElimAssumePrefix}{loop_num}_invariant_{invSuffix i lp.1}" lp.2 md)
  let maintain_invariants := invariants.mapIdx fun i lp =>
    Stmt.cmd (HasPassiveCmds.assert
      s!"{loopElimAssertPrefix}{loop_num}_arbitrary_iter_maintain_invariant_{invSuffix i lp.1}" lp.2 md)
  let exit_invariant_assumes := invariants.mapIdx fun i lp =>
    Stmt.cmd (HasPassiveCmds.assume
      s!"{loopElimAssumePrefix}{loop_num}_exit_invariant_{invSuffix i lp.1}" lp.2 md)
  let arb_assumes : Stmt P C :=
    .block s!"{loopElimBlockPrefix}arbitrary_iter_assumes_{loop_num}"
      (assumeGuard ++ inv_assumes) md
  let arb_facts : Stmt P C :=
    .block s!"{loopElimBlockPrefix}arbitrary_iter_facts_{loop_num}"
      ([havocd, arb_assumes] ++ preTermination ++ bss ++
       maintain_invariants ++ postTermination) {}
  let exit_state : List (Stmt P C) := [havocd] ++ exitGuard ++ exit_invariant_assumes
  let loop_passive : Stmt P C := .ite guard (arb_facts :: exit_state) [] {}
  .block s!"{loopElimBlockPrefix}loop_{loop_num}"
    [first_iter_facts, loop_passive] {}

/-- The label-conflict freshness check. Returns `false` if no conflict (= ok),
    `true` if there's a conflict. -/
@[expose, reducible] def hasLabelConflict (loop_num : String) (bss : List (Stmt P C)) : Bool :=
  let arb_iter_facts_label := s!"{loopElimBlockPrefix}arbitrary_iter_facts_{loop_num}"
  let loop_label := s!"{loopElimBlockPrefix}loop_{loop_num}"
  let body_exit_labels := Block.labels bss
  arb_iter_facts_label ∈ body_exit_labels || loop_label ∈ body_exit_labels

/-- The loop case of `Stmt.removeLoopsM`, factored out so the proofs can pattern
    on `removeLoopsLoopCase` rather than the giant in-place `do`-block.
    The match on `guard` and `measure` is inlined directly so that proofs can
    `dsimp` past these branches and see each concrete guard-parts tuple. -/
@[reducible] def removeLoopsLoopCase
    [HasBoolOps P] [HasVarsImp P C] [HasFvars P] [HasVarsPure P C]
    [HasHavoc P C] [HasInit P C] [HasPassiveCmds P C]
    [DecidableEq P.Ident]
    [HasIdent P] [HasFvar P] [HasInt P] [HasIntOps P]
    (guard : ExprOrNondet P) (measure : Option (String × P.Expr))
    (invariants : List (String × P.Expr)) (bss : List (Stmt P C))
    (md : MetaData P) :
    ExceptT String (StateM LoopElimState) (Bool × Stmt P C) := do
  let loop_num ← genLoopNum
  if hasLabelConflict loop_num bss then
    throw s!"Generated loop block label conflicts with exit target in loop body (loop {loop_num})"
  -- Note: loop bodies must not contain procedure calls; this is checked once at
  -- the procedure level by `Core.LoopElim.removeLoopsDecls` (the havoc-based
  -- encoding of loop elimination does not preserve call semantics).
  -- The guard × measure match is inlined here (rather than going through a
  -- helper) so that proofs can `dsimp` past these branches and see each
  -- concrete guard-parts tuple directly.
  let (assumeGuard, preTermination, postTermination, exitGuard) ← match guard with
    | .det g =>
      let assumeGuard := [Stmt.cmd (HasPassiveCmds.assume
        s!"{loopElimAssumePrefix}{loop_num}_guard" g md)]
      let notGuard := [Stmt.cmd (HasPassiveCmds.assume
        s!"{loopElimAssumePrefix}{loop_num}_not_guard" (HasBoolOps.not g) md)]
      match measure with
      | none =>
        pure (assumeGuard, ([] : List (Stmt P C)), ([] : List (Stmt P C)), notGuard)
      | some (_, m) =>
        let m_old_ident : P.Ident := measureOldIdent loop_num
        if m_old_ident ∈ Block.touchedVars bss then
          throw s!"Loop measure variable conflicts with body variable"
        else
          let (pre, post) := buildTerminationStmtsSome loop_num m md
          pure (assumeGuard, pre, post, notGuard)
    | .nondet =>
      pure (([] : List (Stmt P C)), ([] : List (Stmt P C)),
            ([] : List (Stmt P C)), ([] : List (Stmt P C)))
  let result := buildLoopOutput loop_num guard bss
    assumeGuard preTermination postTermination exitGuard invariants md
  bumpStat s!"{LoopElim.Stats.erasedLoops}"
  -- Total assert/assume statements emitted for this loop: 4·#invariants
  -- (entry asserts + entry assumes + mid-iter assumes + maintain asserts +
  -- exit assumes) + |assumeGuard| + |exitGuard| + 2 if measure is some
  -- (measure_lb assert + measure_decrease assert).
  let measureExtra := if measure.isSome then 2 else 0
  let numAssertAssumes :=
    invariants.length + invariants.length + assumeGuard.length +
      invariants.length + invariants.length + exitGuard.length +
      invariants.length + measureExtra
  bumpStat s!"{LoopElim.Stats.insertedAssertAssumes}" numAssertAssumes
  pure (true, result)

mutual

def Stmt.removeLoopsM
  [HasBoolOps P] [HasVarsImp P C] [HasFvars P] [HasVarsPure P C]
  [HasHavoc P C] [HasInit P C] [HasPassiveCmds P C]
  [DecidableEq P.Ident]
  [HasIdent P] [HasFvar P] [HasInt P] [HasIntOps P]
  (s : Stmt P C) : ExceptT String (StateM LoopElimState) (Bool × Stmt P C) :=
  match s with
  | .loop guard measure invariants bss md =>
    removeLoopsLoopCase guard measure invariants bss md
  | .ite c tss ess md => do
    let (c1, tss) ← Block.removeLoopsM tss
    let (c2, ess) ← Block.removeLoopsM ess
    pure (c1 || c2, .ite c tss ess md)
  | .block label bss md => do
    let (changed, bss) ← Block.removeLoopsM bss
    pure (changed, .block label bss md)
  | .cmd _ => pure (false, s)
  | .exit _ _ => pure (false, s)
  | .funcDecl _ _ => pure (false, s)  -- Function declarations pass through unchanged
  | .typeDecl _ _ => pure (false, s)  -- Type declarations pass through unchanged

def Block.removeLoopsM
  [HasBoolOps P] [HasVarsImp P C] [HasFvars P] [HasVarsPure P C]
  [HasHavoc P C] [HasInit P C] [HasPassiveCmds P C]
  [DecidableEq P.Ident]
  [HasIdent P] [HasFvar P] [HasInt P] [HasIntOps P]
  (ss : List (Stmt P C)) : ExceptT String (StateM LoopElimState) (Bool × List (Stmt P C)) :=
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

/-- Repeatedly apply `Block.removeLoopsM` until no more loops remain (fixpoint).
    Uses a fuel parameter to guarantee termination (each pass eliminates at least
    one loop, so the depth of loop nesting is a bound). -/
private def removeLoopsBlock (fuel : Nat) (body : List (Stmt Expression Command)) :
    ExceptT String (StateM LoopElimState) (Bool × List (Stmt Expression Command)) := do
  match fuel with
  | 0 => return (false, body)
  | fuel + 1 =>
    let (changed, result) ← Block.removeLoopsM body
    if changed then
      let (_, result') ← removeLoopsBlock fuel result
      return (true, result')
    else
      return (false, body)

private def removeLoopsDecls :
    List Core.Decl → ExceptT String (StateM LoopElimState) (Bool × List Core.Decl)
  | [] => pure (false, [])
  | .proc proc md :: ds => do
    -- Loop bodies must not contain procedure calls: the havoc-based encoding
    -- of loop elimination does not preserve call semantics.  Loop elim
    -- runs after CallElim in the Core pipeline, so this check is defensive.
    if !Core.Statements.noCall proc.body then
      throw s!"Procedure body contains a procedure call (loop elim does not support calls)"
    let (c1, body) ← removeLoopsBlock 100 proc.body
    let (c2, ds) ← removeLoopsDecls ds
    return (c1 || c2, .proc { proc with body := body } md :: ds)
  | d :: ds => do
    let (changed, ds) ← removeLoopsDecls ds
    return (changed, d :: ds)

/-- Eliminate loops in all procedures of a Core program by replacing each
    loop with assertions and assumptions about its invariants.  Loop
    elimination as a `CoreTransformM` pass suitable for the pipeline.
    Returns `(changed, program)` and merges the generated label state back
    into the transform's `genState.cs`. -/
def loopElim (p : Core.Program) :
    Core.Transform.CoreTransformM (Bool × Core.Program) := do
  let σ ← get
  let initState : LoopElimState := { gen := σ.genState.cs }
  let (result, finalState) := StateT.run (ExceptT.run (removeLoopsDecls p.decls)) initState
  set { σ with
    genState := { σ.genState with cs := finalState.gen },
    statistics := σ.statistics.merge finalState.statistics }
  match result with
  | .ok (changed, decls) => return (changed, { decls := decls })
  | .error e => throw (Strata.DiagnosticModel.fromMessage e)

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
