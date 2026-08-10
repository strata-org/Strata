/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.LaurelAST
public import Strata.Languages.Laurel.LaurelPass
import Strata.Languages.Laurel.MapStmtExpr
import Strata.Util.Tactics

/-!
# Loop Invariant Well-Formedness

A loop invariant is *assumed* and re-asserted at the loop head, over the
loop-carried variables as they stand on an arbitrary iteration. Its
well-formedness (WF) must therefore be established at *that* state.

Checking it in the loop's pre-state instead is checking the wrong state: the
pre-state knows strictly more, so a WF obligation can be vacuously discharged
there and never checked where the invariant is actually used. For a loop where
`d` starts at `1` and decreases toward `0`, an invariant `pureDiv(10, d) >= 0`
has its `d != 0` obligation evaluated where `d == 1` — trivially true — while
the loop head admits `d == 0`.

This pass emits, immediately before each loop carrying invariants:

```
if * {
  havoc(M);        -- M = loop-carried write-set: the loop-head state
  assume I_0;      -- lowering I_0 here emits its WF obligations
  assume I_1;      -- chained: I_1's WF may rely on I_0
  ...
  assume false;    -- sever: contributes nothing downstream
}
```

`havoc(M)` reaches the loop-head state, so the obligations are checked where the
invariant is actually used. `assume false` severs the branch, so the havoc cannot
leak into the pre-state and the block cannot make downstream obligations vacuous.

The invariants are `assume`d, not `assert`ed. The obligations we want come from
lowering each invariant's *contents* — a call inside it becomes
`assert callee$pre_i(args)`, a partial operation becomes a definedness assert —
and that happens in either position. Asserting the invariant itself would be
wrong: the havoc'd state is arbitrary, so the invariant generally does not hold
there, and every well-written loop would report a spurious failure. Assuming each
invariant in turn also supplies the chaining, so a later invariant's
well-formedness may rely on the earlier ones.

## Why this is a Laurel pass and not a Core one

The natural place for this is `PrecondElim`, which already harvests WF
obligations from expressions. But by the time a loop reaches Core its invariants
are Core *expressions*, and a Core expression cannot carry an `assert`/`assume`.
Any invariant whose WF check needs a statement — most importantly a call to a
procedure with a precondition, whose check is `assert callee$pre_i(args)` — has
nowhere to put it there, so a Core-level pass cannot generate the obligation at
all.

Emitting the block here, while invariants are still Laurel `StmtExpr`s, means
the ordinary WF machinery (contract lowering, precondition asserts, definedness
checks) sees the invariant in statement position and handles it the same way it
handles any other assert. This pass generates no obligations itself; it only
places the invariants at the right program point.

## Placement in the pipeline

Must run before `contractPass`, which lowers calls to their precondition
asserts — the emitted invariant copies have to be in place for it to see them.
Runs after `eliminateDoWhile`, so every `While` is pre-test and each loop is
visited once.
-/

namespace Strata.Laurel

/-- Monotonic counter feeding fresh names, mirroring `EliminateDoWhile`. -/
private structure WFState where
  freshCounter : Nat := 0

private abbrev WFM := StateM WFState

private def freshIndex : WFM Nat :=
  modifyGet fun s => (s.freshCounter, { s with freshCounter := s.freshCounter + 1 })

/-- The local variables a statement assigns to, in first-assignment order.

    Only `.Local` targets are collected: a `.Field` write mutates the heap rather
    than rebinding a local, and the heap is already modelled by the loop
    encoding's own frame handling. A `.Declare` target introduces a *new*
    body-local variable, which is not part of the loop-head state, so it is
    excluded — matching the write-set `LoopElim` havocs (`modifiedVars` minus
    `definedVars`).

    The full `Identifier` is carried (not just its text) so the havoc we emit
    reuses the target's own identity, including the `uniqueId` assigned by
    resolution. -/
private def assignedLocals (node : StmtExprMd) : List Identifier :=
  collectStmtExprList (fun n =>
    match n.val with
    | .Assign targets _ => targets.filterMap fun t =>
        match t.val with
        | .Local name => some name
        | _ => none
    | _ => []) node
  |>.foldl (fun acc n => if acc.any (·.text == n.text) then acc else acc ++ [n]) []

/-- Names declared by `var x : T` inside a statement; these are body-local and
    must not be havoc'd even if they are also assigned. -/
private def declaredLocals (node : StmtExprMd) : List String :=
  collectStmtExprList (fun n =>
    match n.val with
    | .Var (.Declare p) => [p.name.text]
    | .Assign targets _ => targets.filterMap fun t =>
        match t.val with
        | .Declare p => some p.name.text
        | _ => none
    | _ => []) node

/-- Havoc a local by assigning it a nondeterministic hole. -/
private def havocLocal (name : Identifier) (source : FileRange) : StmtExprMd :=
  ⟨.Assign [⟨.Local name, source⟩] ⟨.Hole (deterministic := false) none, source⟩, source⟩

/-- Build the severed WF proof block for one loop, or `none` when the loop
    carries no invariants (nothing to check, so no block is emitted). -/
private def mkWFBlock (invariants : List StmtExprMd) (body : StmtExprMd)
    (source : FileRange) : WFM (Option StmtExprMd) := do
  if invariants.isEmpty then
    return none
  let idx ← freshIndex
  -- Loop-carried write-set: assigned locals minus those declared in the body.
  let declared := declaredLocals body
  let targets := (assignedLocals body).filter (fun n => !declared.contains n.text)
  let havocs := targets.map (havocLocal · source)
  -- One `assume` per invariant, in order. `assume` (not `assert`): the goal is
  -- to make the WF machinery evaluate each invariant at this state, not to prove
  -- the invariant *holds* here — the havoc'd state is arbitrary, so the
  -- invariant generally does not hold and asserting it would be unsound-in-the-
  -- other-direction (a spurious failure on every well-written loop).
  --
  -- The obligations we want come from lowering the invariant's *contents*: a
  -- call inside it becomes `assert callee$pre_i(args)` (contract pass), a
  -- division becomes a definedness assert (PrecondElim). Those are emitted at
  -- this program point regardless of whether the enclosing condition is
  -- asserted or assumed.
  --
  -- Assuming each invariant after its own checks also gives the chaining: a
  -- later invariant's WF may rely on the earlier ones.
  let chained := invariants.map fun inv =>
    (⟨.Assume inv, inv.source⟩ : StmtExprMd)
  let sever : StmtExprMd := ⟨.Assume ⟨.LiteralBool false, source⟩, source⟩
  let blockBody : StmtExprMd :=
    ⟨.Block (havocs ++ chained ++ [sever]) (some s!"$loop_invariant_wf_{idx}"), source⟩
  -- A nondeterministic `if` with no else: the then-branch is severed, so this
  -- adds a proof context without adding a feasible path.
  return some ⟨.IfThenElse ⟨.Hole (deterministic := false) none, source⟩ blockBody none, source⟩

/-- Emit the WF block before each loop that carries invariants. Applied
    bottom-up by `mapStmtExprFlattenM`, so a loop nested in another loop's body
    gets its own block, emitted inside that body. -/
private def wfNode (_resultUsed : Bool) (node : StmtExprMd) : WFM (List StmtExprMd) := do
  match node.val with
  | .While _ invariants _ body _ =>
    match ← mkWFBlock invariants body node.source with
    | some blk => return [blk, node]
    | none => return [node]
  | _ => return [node]

/-- Insert a loop-head invariant well-formedness block before every loop in the
    program that carries invariants. -/
private def loopInvariantWellFormedness (program : Program) : Program :=
  let rewriteBody : StmtExprMd → WFM StmtExprMd := fun body =>
    mapStmtExprFlattenM (fun _ _ => pure none) wfNode false body
  let rewrite : Procedure → WFM Procedure := mapProcedureM rewriteBody
  (mapProgramProceduresM rewrite program |>.run {}).fst

public section

/-- Pipeline pass: check loop invariant well-formedness at the loop head. -/
public def loopInvariantWellFormednessPass : LoweringPass where
  name := "LoopInvariantWellFormedness"
  needsResolves := true
  documentation := "Emits `if * { havoc(loop targets); assume each invariant in order; assume false }` before each loop carrying invariants, so invariant well-formedness is checked at the loop head (where the invariant is assumed) rather than in the loop's pre-state (where more is known and the obligation can be vacuously discharged). Assuming each invariant in turn lets a later invariant's well-formedness rely on the earlier ones. Must run before the contract pass, which lowers the calls inside those invariants to precondition asserts."
  run := fun _ p _m => (loopInvariantWellFormedness p, [], {})

end -- public section

end Strata.Laurel
