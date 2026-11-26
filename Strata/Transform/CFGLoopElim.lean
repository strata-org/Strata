/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module
public import Strata.Pipeline.Messages

public import Strata.Languages.Core.PipelinePhase
public import Strata.Languages.Core.MarkerLabels
public import Strata.Transform.CoreTransform
public import Strata.DL.Imperative.CFGDominators
import Strata.Transform.CFGLoopElimReplay
import Strata.Transform.CallElim

/-! # Loop elimination for unstructured (CFG) procedure bodies

Cuts every loop of a `cfg` body so that the body becomes acyclic, in the style
of Barnett and Leino's loop cutting, using the loop invariants written on the
loop-header blocks.

## Loops

A *back edge* is an edge `b → h` from a reachable block `b` to a block `h` that
dominates `b`; `h` is then a *loop header*. The loop of `h` is its natural loop:
`h` together with every reachable block that reaches a back-edge source of `h`
without passing through `h`. Nested loops are loops whose headers lie in an
outer loop; each is cut independently.

A cycle that has no dominating header (irreducible control flow) cannot be cut,
and is rejected.

## Invariants

The invariants of a header `h` are the expressions of its `loopInvariant` block
metadata entries, `@[loopInvariant = (e)]`; a header may carry several. A header
with none has the invariant `true`, for which no invariant is asserted. The CFG type
checker, which runs first (the phase requires `typeAnnotated`), rejects a `loopInvariant`
on a reachable block that is not a loop header, and one that is not boolean.

## The cut

Let `I` be the invariants of `h` and `M` the variables the loop modifies (the
variables its blocks assign or havoc). A loop's blocks may not declare locals:
a declaration would run again on every iteration, which `init` cannot, and the
CFG type checker rejects it too. Then:

* every edge into `h` that is not a back edge goes to a fresh *pre-header* block
  `loopElim_pre_h`:

  ```
  assert I;       // the invariant holds on entry
  assume true;    // labelled `$__cfgLoopElimAssume_havoc_h`: marks the cut
  havoc M;        // an arbitrary iteration ...
  assume I;       // ... in which the invariant holds
  goto h;
  ```

  The labelled `assume true` puts a `$__cfgLoopElimAssume_` label on every path
  through the cut. It comes before the havoc, so it also precedes the checks a
  later phase adds for the havoc and the assumed invariants: a result resting
  on the arbitrary iteration is validated rather than reported as definite.
  Precondition elimination runs after the cut (it refuses a block that still carries a
  `loopInvariant`), and checks the preconditions of the cut's `assert`s and `assume`s
  like those of any other command. Every edge into `h` that is not a back edge is
  redirected to the pre-header (if `h` is the entry, the pre-header becomes the
  entry);

* every back edge `b → h` is redirected to a fresh block `loopElim_back_b_h`:

  ```
  assert I;     // the iteration maintains the invariant
  assume false; // and the path ends here
  return;
  ```

  No execution returns through this block, so a postcondition checked after it
  holds trivially.

The pre-header has the same strict dominators as `h` had, so everything in
scope at the start of `h` is in scope in it, and every back-edge block is
dominated by its source. Every edge into a header leaves a pre-header or
ends in a back-edge block, so a reducible body becomes acyclic.

Invariants are moved from the header's metadata into `assert`/`assume`
commands, so a later type check checks them as boolean conditions. The annotations
of unreachable blocks are dropped too, so on a body the type checker accepts, the output
carries no `loopInvariant` on any block.

A call's writes are its output arguments (`Command.modifiedVars`), so a loop
containing calls is cut like any other. Structured bodies are left unchanged.

## Proof debt

The phase's soundness is unproved: if a run of the input body fails a check, then a run of
the output body fails a check (the same one, or an invariant check the cut added), so the
output can fail whenever the input can. Every obligation that does not rest on the cut is
claimed model-preserving on that basis. The proof also needs the direction of
`computeDominators` that is itself unproved (`CFGDominators.lean`). What is proved is that the
output is acyclic (`CFGLoopElimProps.cutLoops_acyclic`).
Target: rung 4 (Lean proof), with structured loop elimination's (`LoopElimCorrect`) as the
model. Budget: one follow-up CR. Fallback: the loop tests in `CFGLoopElimTest`, run under
both merge modes. -/

namespace Core
namespace CFGLoopElim

open Imperative

public section


/-- Label prefix of the invariant `assert`s this pass creates. -/
def cfgLoopElimAssertPrefix : String := "cfgLoopElimAssert_"

/-- The location of the expressions this pass builds. -/
abbrev cfgLoopElimLoc : ExprSourceLoc := ExprSourceLoc.synthesized "cfgLoopElim"

/-- Label prefix of the blocks this pass creates. -/
def cfgLoopElimBlockPrefix : String := "loopElim_"

/-- A deterministic block of a Core CFG body. -/
abbrev CBlock := Imperative.DetBlock String Command Expression

/-- The loop invariants of a header block, in metadata order. A
    `loopInvariant` entry whose value is not an expression is an error. -/
def loopInvariants (procName lbl : String) (blk : CBlock) :
    Except String (List Expression.Expr) :=
  blk.md.loopInvariantValues.mapM fun v =>
    match v with
    | .expr x => pure x
    | _ => throw s!"procedure '{procName}': the `{MetaData.loopInvariantKey}` metadata of \
                   block '{lbl}' must be an expression, `@[{MetaData.loopInvariantKey} = (e)]`"

/-- The natural loop of header `h` with back-edge sources `srcs`: `h` and every
    reachable block that reaches a source without passing through `h`, by a
    backward search over the predecessors `preds`. Each block is pushed at most
    once, so the search ends within `fuel` (the number of blocks plus one). -/
private def naturalLoop (preds : Std.HashMap String (List String))
    (reachable : Std.HashSet String) (fuel : Nat) (h : String) (srcs : List String) :
    Std.HashSet String := Id.run do
  let mut body : Std.HashSet String := Std.HashSet.ofList [h]
  let mut work : List String := []
  for s in srcs do
    if !body.contains s && reachable.contains s then
      body := body.insert s
      work := s :: work
  for _ in [0:fuel] do
    match work with
    | [] => break
    | n :: rest =>
      work := rest
      for m in preds.getD n [] do
        if !body.contains m && reachable.contains m then
          body := body.insert m
          work := m :: work
  return body

private def retarget (f : String → String) :
    DetTransferCmd String Expression → DetTransferCmd String Expression
  | .condGoto c lt lf md => .condGoto c (f lt) (f lf) md
  | .finish md => .finish md

/-- Reject a CFG that still has a cycle reachable from its entry. Run after
    cutting, such a cycle had no dominating header (irreducible control flow). -/
def rejectCycles (procName : String) (cfg : DetCFG) : Except String Unit := do
  let cyclic := Imperative.CFG.cycleLabelsWith cfg.succMap [cfg.entry]
  if !cyclic.isEmpty then
    let ls := cfg.labels.filter cyclic.contains
    throw s!"procedure '{procName}': irreducible control flow: the cycle through \
             {ls} has no loop header that dominates it, so its loops cannot be cut"

/-- The labelled `assume true` a pre-header has before its havoc (see "The cut"
    in the module header). -/
private def havocMark (h : String) (md : MetaData Expression) : Command :=
  .cmd (.assume s!"{cfgLoopElimAssumePrefix}havoc_{h}"
    (Lambda.LExpr.boolConst cfgLoopElimLoc true) md)

/-- The location of the entry check of invariant `inv`: the invariant's own source range
    when it was parsed from a file, else `fallback`. -/
private def invariantMd (fallback : MetaData Expression) (inv : Expression.Expr) :
    MetaData Expression :=
  let loc := inv.metadata
  match loc.uri with
  | some u => if loc.isSynthesized then fallback else MetaData.ofSourceRange u loc.range
  | none => fallback

/-- The variable the translator declares for a nondeterministic `goto a, b` (an
    `init $__nondet_N : bool := *` in the block that branches on it; `nondetChoicePrefix`). -/
def isNondetChoice (x : Expression.Ident) : Bool := x.name.startsWith nondetChoicePrefix

/-- Declare each nondeterministic choice (`isNondetChoice`) of a reachable block once,
    at the entry (`Transform.declareAtEntry`), and havoc it where it was declared. The
    choice is unconstrained either way, but a declaration inside a loop would run
    again on every iteration, which `init` cannot; a havoc is just another write of
    the loop.

    Why this keeps every run (argued, not proved): the in-block `init $__nondet_N := *`
    becomes `$__nondet_N := *` at the same place, so each execution of the block, in
    every iteration, still chooses a fresh value. The only other change is that the
    variable exists from the entry on, with an arbitrary value, and nothing observes that
    value: the choice is read only by its own block's `goto`, after the assignment. -/
def hoistNondetChoices (cfg : DetCFG) : DetCFG := Id.run do
  let reachable := cfg.reachableLabels
  let mut decls : Array Command := #[]
  let mut blocks : Array (String × CBlock) := #[]
  for (lbl, blk) in cfg.blocks do
    if !reachable.contains lbl then
      blocks := blocks.push (lbl, blk)
      continue
    let cmds := blk.cmds.map fun c => match c with
      | .cmd (.init x _ .nondet md) => if isNondetChoice x then .cmd (.set x .nondet md) else c
      | c => c
    for c in blk.cmds do
      if let .cmd (.init x _ .nondet _) := c then
        if isNondetChoice x then decls := decls.push c
    blocks := blocks.push (lbl, { blk with cmds := cmds })
  return Transform.declareAtEntry { cfg with blocks := blocks.toList } decls.toList
    s!"{cfgLoopElimBlockPrefix}entry"

/-- `cfg` without the `loopInvariant` annotations of the blocks not in `reachable`, and
    whether any were dropped. -/
private def dropUnreachableInvariants (reachable : Std.HashSet String) (cfg : DetCFG) :
    Bool × DetCFG :=
  let isDead : String × CBlock → Bool := fun lb =>
    !reachable.contains lb.1 && !lb.2.md.loopInvariantValues.isEmpty
  if cfg.blocks.any isDead then
    let erase : String × CBlock → String × CBlock := fun lb =>
      if isDead lb then
        (lb.1, { lb.2 with md := lb.2.md.eraseAllElems (.label MetaData.loopInvariantKey) })
      else lb
    (true, { cfg with blocks := cfg.blocks.map erase })
  else (false, cfg)

/-- The work of `cutLoops`, without its final check that no cycle is left. -/
def cutLoopsCore (procName : String) (cfg : DetCFG) : Except String (Bool × DetCFG) := do
  let reachable := cfg.reachableLabels
  let (droppedDead, cfg) := dropUnreachableInvariants reachable cfg
  -- Without a cycle there is no back edge and no header: skip the dominators.
  let acyclic := (CFG.cycleLabelsWith cfg.succMap [cfg.entry]).isEmpty
  let dom := if acyclic then {} else cfg.computeDominators
  let preds := cfg.predMap
  let blockOf : Std.HashMap String CBlock := Std.HashMap.ofList cfg.blocks
  let blockArr := cfg.blocks.toArray
  let blockIdx : Std.HashMap String Nat :=
    (cfg.blocks.zipIdx.foldl (fun m ((l, _), i) => m.insertIfNew l i) {})
  let edges := CFG.backEdges dom reachable cfg
  let headers := edges.map (·.1)
  let headerSet : Std.HashSet String := .ofList headers.toList
  let backSrcs : Std.HashMap String (Array String) := .ofList edges.toList
  -- No header: the body is acyclic, or its cycles are irreducible, which the check in
  -- `cutLoops` rejects.
  if headers.isEmpty then
    return (droppedDead, cfg)
  let fuel := cfg.blocks.length + 1
  let mut taken : Std.HashSet String := Std.HashSet.ofList cfg.labels
  -- The keys `<header>_<source>` of the back-edge labels, made distinct.
  let mut usedKeys : Std.HashSet String := {}
  -- Per header: its pre-header label and block.
  let mut preLabel : Std.HashMap String String := {}
  let mut preBlock : Std.HashMap String CBlock := {}
  -- Per (source, header) back edge: its block label and block, in order.
  let mut backLabel : Std.HashMap (String × String) String := {}
  let mut backBlocks : Array (String × CBlock) := #[]
  for h in headers do
    let hblk := blockOf.getD h { cmds := [], transfer := .finish .empty }
    let md := hblk.transfer.md
    let invs ← loopInvariants procName h hblk
    let srcs := (backSrcs.getD h #[]).toList
    let body := naturalLoop preds reachable fuel h srcs
    -- The loop's blocks in block order, found through their indices: scanning
    -- every block per header would be quadratic in the number of headers.
    let bodyBlocks := ((body.toList.filterMap blockIdx.get?).toArray.qsort (· < ·)).toList.filterMap
      fun i => blockArr[i]?
    -- A declaration in a loop would run again on every iteration, which `init`
    -- cannot (it needs the variable unset); the CFG type checker rejects it too.
    for (l, b) in bodyBlocks do
      if let some x := (b.cmds.flatMap Command.definedVars).head? then
        -- Call elimination names its temporaries `tmp_…` and `old_…`
        -- (`Transform.tmpVarPrefix`, `Transform.oldVarPrefix`).
        let hint :=
          if x.name.startsWith (Transform.tmpVarPrefix "") ||
              x.name.startsWith (Transform.oldVarPrefix "") then
            "; if it is a call elimination temporary, run call elimination after cfgLoopElim"
          else ""
        throw s!"procedure '{procName}': block '{l}' declares '{x.name}' inside the loop \
                 at '{h}'; a local must be declared before the loop{hint}"
    let bodyCmds := bodyBlocks.flatMap (·.2.cmds)
    -- The modified variables, in first-write order, each once.
    let (_, modified) := (bodyCmds.flatMap Command.modifiedVars).foldl
      (fun (seen, acc) (v : Expression.Ident) =>
        if seen.contains v.name then (seen, acc)
        else (seen.insert v.name, acc.push v))
      ((({} : Std.HashSet String)), (#[] : Array Expression.Ident))
    let modified := modified.toList
    -- Invariant `i`'s check is labelled `<tag>_<i>`. An entry check points at the
    -- invariant; a maintenance check at the back edge's source (`atMd`).
    let asserts (tag : String) (atMd : Expression.Expr → MetaData Expression) :
        List Command :=
      invs.mapIdx fun i inv =>
        .cmd (.assert s!"{cfgLoopElimAssertPrefix}{tag}_{i}" inv (atMd inv))
    let pre := Strata.Name.freshName taken s!"{cfgLoopElimBlockPrefix}pre_{h}"
    taken := taken.insert pre
    preLabel := preLabel.insert h pre
    preBlock := preBlock.insert h
      { cmds := asserts s!"entry_{h}" (invariantMd md) ++ [havocMark h md] ++
                  Transform.createHavocCmds modified md ++
                  invs.mapIdx fun i inv =>
                    .cmd (.assume s!"{cfgLoopElimAssumePrefix}invariant_{h}_{i}" inv md)
        transfer := .goto h md }
    for b in srcs do
      let bl := Strata.Name.freshName taken s!"{cfgLoopElimBlockPrefix}back_{b}_{h}"
      taken := taken.insert bl
      backLabel := backLabel.insert (b, h) bl
      -- `h_b` does not determine `(h, b)`: `a` with `b_c`, and `a_b` with `c`.
      let key := Strata.Name.freshName usedKeys s!"{h}_{b}"
      usedKeys := usedKeys.insert key
      backBlocks := backBlocks.push (bl,
        { cmds := asserts s!"maintain_{key}"
                      (fun _ => ((blockOf.get? b).map (·.transfer.md)).getD md) ++
                    [.cmd (.assume s!"{cfgLoopElimAssumePrefix}cut_{key}"
                      (Lambda.LExpr.boolConst cfgLoopElimLoc false) md)]
          transfer := .finish md })
  -- Rebuild: every edge into a header goes to its back-edge block (back edges) or its
  -- pre-header (others). The pre-headers and back-edge blocks are listed after the
  -- input's blocks: they read and havoc variables declared there, and in the concrete
  -- syntax a declaration is in scope only in the blocks listed after it.
  let mut blocks : Array (String × CBlock) := #[]
  let mut preBlocks : Array (String × CBlock) := #[]
  for (l, blk) in cfg.blocks do
    if let some pl := preLabel.get? l then
      preBlocks := preBlocks.push
        (pl, preBlock.getD l { cmds := [], transfer := .finish .empty })
    let f := fun (t : String) =>
      match backLabel.get? (l, t) with
      | some bl => bl
      | none => (preLabel.get? t).getD t
    -- A cut header's invariants live in the commands above; dropping them
    -- from its metadata leaves no `loopInvariant` on a block that heads no loop
    -- in the output.
    let md := if headerSet.contains l then blk.md.eraseAllElems (.label MetaData.loopInvariantKey)
      else blk.md
    blocks := blocks.push (l, { blk with transfer := retarget f blk.transfer, md := md })
  let cut : DetCFG :=
    { entry := (preLabel.get? cfg.entry).getD cfg.entry
      blocks := (blocks ++ preBlocks ++ backBlocks).toList }
  return (true, cut)

/-- Cut every loop of the CFG body of procedure `procName`. Returns whether the body
    changed, and the acyclic body. Fails on an irreducible cycle, on a header's
    `loopInvariant` entry that is not an expression, and on a declaration inside a loop.
    A `loopInvariant` on a reachable block that is not a loop header is the CFG type
    checker's to reject; on a body it accepts, the result has no `loopInvariant` on any
    block. The result is checked for cycles last (`rejectCycles`), so a body it returns
    has none reachable from its entry (`cutLoops_acyclic`): what `noCFGCycles` asks of
    each CFG body. -/
def cutLoops (procName : String) (cfg : DetCFG) : Except String (Bool × DetCFG) := do
  let (changed, cut) ← cutLoopsCore procName cfg
  rejectCycles procName cut
  return (changed, cut)

/-- `hoistNondetChoices` on every CFG body with a cycle reachable from its entry. The
    type checker rejects a declaration in a block on a cycle, so a nondeterministic
    `goto` inside a loop, whose choice the translator declares in its block, type-checks
    only after this. -/
def hoistNondetChoicesInLoops (p : Program) : Transform.CoreTransformM (Bool × Program) :=
  Transform.runProgram (fun _ => pure none) p
    (cfgBody := some fun _ g =>
      if (CFG.cycleLabelsWith g.succMap [g.entry]).isEmpty then pure (false, g)
      else pure (true, hoistNondetChoices g))

/-- Cut the loops of every CFG procedure body; structured bodies are unchanged. -/
def cfgLoopElim (p : Program) : Transform.CoreTransformM (Bool × Program) :=
  Transform.runProgram (fun _ => pure none) p
    (cfgBody := some fun proc g =>
      match cutLoops proc.header.name.1 g with
      | .ok r => pure r
      | .error msg => throw (Strata.Message.fromString msg))

end -- public section

end CFGLoopElim

public section

/-- The phase that declares the nondeterministic choices of CFG loops at the entry of
    their bodies (`CFGLoopElim.hoistNondetChoicesInLoops`), so that type checking, which
    rejects a declaration on a cycle, accepts them. A choice is unconstrained wherever it
    is declared, so the phase keeps every run, and every fact. -/
def hoistNondetChoicesPipelinePhase : PipelinePhase :=
  modelPreservingPipelinePhase "hoistNondetChoices"
    (preserves := factSet![.wellFormedCalls, .noCFGBodies, .noCalls, .noLoops,
                          .noLoopInvariants, .noLoopMeasures, .uniqueInits,
                          .loopBodyNoInits, .noPrecondsFromFuncs, .noNondetGuards,
                          .noProcedureContracts, .noPolymorphicProcedures,
                          .noPolymorphicFunctions, .typeAnnotated, .exitsCovered,
                          .noCFGCycles])
    CFGLoopElim.hoistNondetChoicesInLoops

/-- CFG loop-elimination pipeline phase: cuts the loops of CFG bodies using the
    invariants on their loop headers. The `assume`s it adds over-approximate the
    loop (an arbitrary iteration satisfying the invariant), so a model of an
    obligation that depends on them must be validated: given the program the phase
    was given, a model is valid when replaying it through that program reaches the
    obligation's check with the value the model gives it
    (`CFGLoopElim.replayValidates`); otherwise no model is, and such an obligation's
    failure is reported as unknown. -/
def cfgLoopElimPipelinePhase : PipelinePhase where
  transform p := do
    rejectMarkerLabels "CFG loop elimination" CFGLoopElim.cfgLoopElimAssumePrefix p
    CFGLoopElim.cfgLoopElim p
  phase.name := "cfgLoopElim"
  phase.validationPrefixes := [CFGLoopElim.cfgLoopElimAssumePrefix]
  phase.getValidation obligation :=
    if obligationHasLabelPrefix obligation CFGLoopElim.cfgLoopElimAssumePrefix then
      .modelToValidate (fun _ _ => none)
    else .modelPreserving
  phase.getValidationOn := some fun input obligation =>
    if obligationHasLabelPrefix obligation CFGLoopElim.cfgLoopElimAssumePrefix then
      -- A run through a callee's contract (call elimination's assumptions) is not one
      -- of the program.
      .modelToValidate (CFGLoopElim.replayValidates
        (·.startsWith CallElim.callElimAssumePrefix) input obligation)
    else .modelPreserving
  -- The invariant's index is the label's last `_`-separated part (`<tag>_<i>`).
  phase.getAssertDescription label :=
    let idx := (label.splitOn "_").getLast?.getD ""
    if label.startsWith s!"{CFGLoopElim.cfgLoopElimAssertPrefix}entry_" then
      some s!"loop invariant {idx} on entry"
    else if label.startsWith s!"{CFGLoopElim.cfgLoopElimAssertPrefix}maintain_" then
      some s!"loop invariant {idx} maintained"
    else none
  -- It makes every CFG body acyclic (`noCFGCycles`): it cuts each loop at its
  -- header and rejects an irreducible cycle.
  -- It adds no calls, structured loops, inits or guards, and changes no function
  -- declaration (so `noPrecondsFromFuncs`, which is about declarations, holds).
  -- Precondition elimination, which runs after it, checks the preconditions of its new
  -- commands. It does not claim
  -- `staticSingleAssignment`, because it havocs. It keeps every expression annotated
  -- (`typeAnnotated`): its new expressions are Boolean literals and the header's
  -- invariants, which type checking annotated in the block's metadata, and its new
  -- declarations carry their types. It changes only CFG bodies, so it keeps
  -- `exitsCovered`, which is about the `exit`s of structured bodies. `noBetaRedexes` is left
  -- unclaimed.
  -- It requires `typeAnnotated`: the type checker has checked the invariants (boolean, on a
  -- loop header, in scope) and annotated them.
  requires := factSet![.typeAnnotated]
  establishes := factSet![.noCFGCycles]
  preserves := factSet![.wellFormedCalls, .noCFGBodies, .noCalls, .noLoops,
                        .noLoopInvariants, .noLoopMeasures, .uniqueInits,
                        .loopBodyNoInits, .noPrecondsFromFuncs, .noNondetGuards,
                        .noProcedureContracts, .noPolymorphicProcedures,
                        .noPolymorphicFunctions, .typeAnnotated, .exitsCovered]

end -- public section

end Core
