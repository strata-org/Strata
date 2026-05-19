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

/-- The havoc block: a single `.block` containing havocs of the loop-carried
    (modified-but-not-locally-defined) variables. -/
@[expose] def buildHavocBlock [HasVarsImp P C] [HasHavoc P C] [DecidableEq P.Ident]
    (loop_num : String) (bss : List (Stmt P C)) (md : MetaData P) : Stmt P C :=
  let local_defs := Block.definedVars bss false
  let assigned_vars := (Block.modifiedVars bss).filter (fun v => v ∉ local_defs)
  .block s!"{loopElimBlockPrefix}loop_havoc_{loop_num}"
    (assigned_vars.map (fun n => Stmt.cmd (HasHavoc.havoc n md))) {}

/-- The list of entry-invariant assertions: `assert(I_i)` for each invariant.
    Used at loop entry to establish VC1. -/
@[expose] def buildEntryInvariants [HasPassiveCmds P C]
    (loop_num : String) (invariants : List (String × P.Expr)) (md : MetaData P) :
    List (Stmt P C) :=
  invariants.mapIdx fun i lp =>
    Stmt.cmd (HasPassiveCmds.assert
      s!"{loopElimAssertPrefix}{loop_num}_entry_invariant_{invSuffix i lp.1}" lp.2 md)

/-- The list of entry-invariant assumptions: `assume(I_i)` for each invariant.
    Used after the entry asserts to make the invariant available on the
    0-iteration path. -/
@[expose] def buildEntryInvariantAssumes [HasPassiveCmds P C]
    (loop_num : String) (invariants : List (String × P.Expr)) (md : MetaData P) :
    List (Stmt P C) :=
  invariants.mapIdx fun i lp =>
    Stmt.cmd (HasPassiveCmds.assume
      s!"{loopElimAssumePrefix}{loop_num}_entry_invariant_{invSuffix i lp.1}" lp.2 md)

/-- The first-iteration facts block: entry asserts followed by entry assumes. -/
@[expose] def buildFirstIterFacts [HasPassiveCmds P C]
    (loop_num : String) (invariants : List (String × P.Expr)) (md : MetaData P) :
    Stmt P C :=
  .block s!"{loopElimBlockPrefix}first_iter_asserts_{loop_num}"
    (buildEntryInvariants loop_num invariants md ++
     buildEntryInvariantAssumes loop_num invariants md) {}

/-- The list of mid-iteration invariant assumptions: `assume(I_i)` after havoc.
    These are used to make the invariant available during one arbitrary
    iteration. -/
@[expose] def buildInvAssumes [HasPassiveCmds P C]
    (loop_num : String) (invariants : List (String × P.Expr)) (md : MetaData P) :
    List (Stmt P C) :=
  invariants.mapIdx fun i lp =>
    Stmt.cmd (HasPassiveCmds.assume
      s!"{loopElimAssumePrefix}{loop_num}_invariant_{invSuffix i lp.1}" lp.2 md)

/-- The list of post-body invariant assertions: `assert(I_i)` after the body.
    These are VC2: the invariant must be maintained by an arbitrary iteration. -/
@[expose] def buildMaintainInvariants [HasPassiveCmds P C]
    (loop_num : String) (invariants : List (String × P.Expr)) (md : MetaData P) :
    List (Stmt P C) :=
  invariants.mapIdx fun i lp =>
    Stmt.cmd (HasPassiveCmds.assert
      s!"{loopElimAssertPrefix}{loop_num}_arbitrary_iter_maintain_invariant_{invSuffix i lp.1}" lp.2 md)

/-- The list of exit-state invariant assumptions: `assume(I_i)` at exit.
    Used after the exit havoc to assume the invariant holds in the exit state
    (justified by induction from VC1+VC2). -/
@[expose] def buildExitInvariantAssumes [HasPassiveCmds P C]
    (loop_num : String) (invariants : List (String × P.Expr)) (md : MetaData P) :
    List (Stmt P C) :=
  invariants.mapIdx fun i lp =>
    Stmt.cmd (HasPassiveCmds.assume
      s!"{loopElimAssumePrefix}{loop_num}_exit_invariant_{invSuffix i lp.1}" lp.2 md)

/-- Termination stmts when guard is `.det g` and measure is `some m`:
    `init m_old` and `assert(¬(m_old < 0))` go into the prefix; `assert(m < m_old)`
    goes into the suffix. -/
@[expose] def buildTerminationStmtsSome
    [HasPassiveCmds P C] [HasInit P C] [HasIdent P] [HasFvar P]
    [HasIntOrder P] [HasNot P]
    (loop_num : String) (m : P.Expr) (md : MetaData P) :
    List (Stmt P C) × List (Stmt P C) :=
  let m_old_ident := HasIdent.ident s!"$__loop_measure_{loop_num}"
  let m_old_expr := HasFvar.mkFvar m_old_ident
  let init_m_old := Stmt.cmd (HasInit.init m_old_ident HasIntOrder.intTy (.det m) md)
  let assert_lb := Stmt.cmd (HasPassiveCmds.assert
    s!"{loopElimAssertPrefix}{loop_num}_measure_lb"
    (HasNot.not (HasIntOrder.lt m_old_expr HasIntOrder.zero)) md)
  let assert_decrease := Stmt.cmd (HasPassiveCmds.assert
    s!"{loopElimAssertPrefix}{loop_num}_measure_decrease" (HasIntOrder.lt m m_old_expr) md)
  ([init_m_old, assert_lb], [assert_decrease])

/-- The fresh measure-snapshot identifier for a given loop number.
    Returns `Some` when measure is `Some _` and freshness check passes. -/
@[expose, reducible] def measureOldIdent [HasIdent P] (loop_num : String) : P.Ident :=
  HasIdent.ident s!"$__loop_measure_{loop_num}"

/-- A guard-specific bundle as a tuple: (assumeGuard, preTermination,
    postTermination, exitGuard). Returned by `buildGuardParts`. The four pieces
    are inserted at different positions in the final encoding. We use a tuple
    rather than a structure to avoid hiding the components behind record
    projections, which can block tactics like `cases` on `gp.exitGuard`. -/
@[expose, reducible] def GuardParts (P : PureExpr) (C : Type) :=
  List (Stmt P C) × List (Stmt P C) × List (Stmt P C) × List (Stmt P C)

/-- Build the guard-specific parts (assumes, termination, exit_guard).
    Throws on the freshness check failure for the measure variable. -/
@[expose, reducible] def buildGuardParts
    [HasNot P] [HasVarsImp P C] [HasVarsPure P P.Expr] [HasVarsPure P C]
    [HasHavoc P C] [HasInit P C] [HasPassiveCmds P C]
    [DecidableEq P.Ident]
    [HasIdent P] [HasFvar P] [HasIntOrder P]
    (loop_num : String) (guard : ExprOrNondet P) (measure : Option P.Expr)
    (bss : List (Stmt P C)) (md : MetaData P) :
    Except String (GuardParts P C) :=
  match guard with
  | .det g =>
    let assumeGuard := [Stmt.cmd (HasPassiveCmds.assume
      s!"{loopElimAssumePrefix}{loop_num}_guard" g md)]
    let notGuard := [Stmt.cmd (HasPassiveCmds.assume
      s!"{loopElimAssumePrefix}{loop_num}_not_guard" (HasNot.not g) md)]
    match measure with
    | none =>
      Except.ok (assumeGuard, [], [], notGuard)
    | some m =>
      let m_old_ident : P.Ident := measureOldIdent loop_num
      if m_old_ident ∈ Block.touchedVars bss then
        Except.error s!"Loop measure variable conflicts with body variable"
      else
        let (pre, post) := buildTerminationStmtsSome loop_num m md
        Except.ok (assumeGuard, pre, post, notGuard)
  | .nondet =>
    Except.ok ([], [], [], [])

/-- Total count of assert/assume statements emitted for one loop. Used for the
    `insertedAssertAssumes` statistic. -/
@[expose, reducible] def numAssertAssumesForLoop
    (invariants : List (String × P.Expr))
    (assumeGuard exitGuard : List (Stmt P C))
    (measureSome : Bool) : Nat :=
  let measureExtra := if measureSome then 2 else 0
  invariants.length + invariants.length +  -- entry_invariants + entry_invariant_assumes
    assumeGuard.length +
    invariants.length +                     -- inv_assumes
    invariants.length +                     -- maintain_invariants
    exitGuard.length +
    invariants.length +                     -- invariant_assumes (exit)
    measureExtra

/-- The `arbitrary_iter_assumes` block: guard_assumes ++ inv_assumes. -/
@[expose, reducible] def buildArbitraryIterAssumes [HasPassiveCmds P C]
    (loop_num : String) (assumeGuard : List (Stmt P C))
    (invariants : List (String × P.Expr)) (md : MetaData P) : Stmt P C :=
  .block s!"{loopElimBlockPrefix}arbitrary_iter_assumes_{loop_num}"
    (assumeGuard ++ buildInvAssumes loop_num invariants md) md

/-- The `arbitrary_iter_facts` block: havoc + arb_assumes + pre_term + body
    + maintain_inv + post_term. -/
@[expose, reducible] def buildArbitraryIterFacts
    [HasVarsImp P C] [HasHavoc P C] [HasPassiveCmds P C] [DecidableEq P.Ident]
    (loop_num : String) (bss : List (Stmt P C))
    (assumeGuard preTermination postTermination : List (Stmt P C))
    (invariants : List (String × P.Expr)) (md : MetaData P) : Stmt P C :=
  let havocd := buildHavocBlock loop_num bss md
  let arb_assumes := buildArbitraryIterAssumes loop_num assumeGuard invariants md
  .block s!"{loopElimBlockPrefix}arbitrary_iter_facts_{loop_num}"
    ([havocd, arb_assumes] ++ preTermination ++ bss ++
     buildMaintainInvariants loop_num invariants md ++ postTermination) {}

/-- The exit-state assumes: `[havocd] ++ exit_guard ++ invariant_assumes`.
    Wrapped into a list (not a block) since it's spliced at the top level. -/
@[expose, reducible] def buildExitStateAssumes
    [HasVarsImp P C] [HasHavoc P C] [HasPassiveCmds P C] [DecidableEq P.Ident]
    (loop_num : String) (bss : List (Stmt P C)) (exitGuard : List (Stmt P C))
    (invariants : List (String × P.Expr)) (md : MetaData P) : List (Stmt P C) :=
  let havocd := buildHavocBlock loop_num bss md
  [havocd] ++ exitGuard ++ buildExitInvariantAssumes loop_num invariants md

/-- The full passive-loop output for a given guard parts. Combines
    `arbitrary_iter_facts`, `exit_state_assumes`, and the outer `if (G)` ite. -/
@[expose, reducible] def buildLoopPassive
    [HasVarsImp P C] [HasHavoc P C] [HasPassiveCmds P C] [DecidableEq P.Ident]
    (loop_num : String) (guard : ExprOrNondet P) (bss : List (Stmt P C))
    (assumeGuard preTermination postTermination exitGuard : List (Stmt P C))
    (invariants : List (String × P.Expr))
    (md : MetaData P) : Stmt P C :=
  let arb_facts := buildArbitraryIterFacts loop_num bss assumeGuard preTermination postTermination invariants md
  let exit_state := buildExitStateAssumes loop_num bss exitGuard invariants md
  .ite guard (arb_facts :: exit_state) [] {}

/-- The full output of the loop-elimination encoding for one loop:
    `block loop_label [first_iter_facts, loop_passive] {}`. -/
@[expose, reducible] def buildLoopOutput
    [HasVarsImp P C] [HasHavoc P C] [HasPassiveCmds P C] [DecidableEq P.Ident]
    (loop_num : String) (guard : ExprOrNondet P) (bss : List (Stmt P C))
    (assumeGuard preTermination postTermination exitGuard : List (Stmt P C))
    (invariants : List (String × P.Expr))
    (md : MetaData P) : Stmt P C :=
  let first_iter_facts := buildFirstIterFacts loop_num invariants md
  let loop_passive := buildLoopPassive loop_num guard bss assumeGuard preTermination postTermination exitGuard invariants md
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
    The match on `guard` and `measure` is inlined here (rather than going via
    `buildGuardParts`) so that proofs can `dsimp` past these branches and see
    each concrete guard-parts tuple directly. -/
@[reducible] def removeLoopsLoopCase
    [HasNot P] [HasVarsImp P C] [HasVarsPure P P.Expr] [HasVarsPure P C]
    [HasHavoc P C] [HasInit P C] [HasPassiveCmds P C]
    [DecidableEq P.Ident]
    [HasIdent P] [HasFvar P] [HasIntOrder P]
    (guard : ExprOrNondet P) (measure : Option P.Expr)
    (invariants : List (String × P.Expr)) (bss : List (Stmt P C))
    (md : MetaData P) :
    ExceptT String (StateM LoopElimState) (Bool × Stmt P C) := do
  let loop_num ← genLoopNum
  if hasLabelConflict loop_num bss then
    throw s!"Generated loop block label conflicts with exit target in loop body (loop {loop_num})"
  -- Inline the guard × measure branch to avoid `match buildGuardParts ... with`
  -- creating an opaque `gp` tuple that `dsimp` cannot reduce.
  let (assumeGuard, preTermination, postTermination, exitGuard) ← match guard with
    | .det g =>
      let assumeGuard := [Stmt.cmd (HasPassiveCmds.assume
        s!"{loopElimAssumePrefix}{loop_num}_guard" g md)]
      let notGuard := [Stmt.cmd (HasPassiveCmds.assume
        s!"{loopElimAssumePrefix}{loop_num}_not_guard" (HasNot.not g) md)]
      match measure with
      | none =>
        pure (assumeGuard, ([] : List (Stmt P C)), ([] : List (Stmt P C)), notGuard)
      | some m =>
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
  bumpStat s!"{LoopElim.Stats.insertedAssertAssumes}"
    (numAssertAssumesForLoop invariants assumeGuard exitGuard measure.isSome)
  pure (true, result)

mutual

def Stmt.removeLoopsM
  [HasNot P] [HasVarsImp P C] [HasVarsPure P P.Expr] [HasVarsPure P C]
  [HasHavoc P C] [HasInit P C] [HasPassiveCmds P C]
  [DecidableEq P.Ident]
  [HasIdent P] [HasFvar P] [HasIntOrder P]
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
  [HasNot P] [HasVarsImp P C] [HasVarsPure P P.Expr] [HasVarsPure P C]
  [HasHavoc P C] [HasInit P C] [HasPassiveCmds P C]
  [DecidableEq P.Ident]
  [HasIdent P] [HasFvar P] [HasIntOrder P]
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
