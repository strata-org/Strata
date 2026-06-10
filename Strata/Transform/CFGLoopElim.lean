/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.BasicBlock
public import Strata.Languages.Core.PipelinePhase
public import Strata.Transform.LoopElim
import Strata.Languages.Core.StatementSemantics

/-! # CFG-native loop elimination

`evalCFGBlocks` (`Strata/Languages/Core/ProcedureEval.lean`) is a fuel-only
worklist with no back-edge awareness: on a `.cfg` body with a loop back-edge it
unrolls the loop until fuel runs out, growing the heap one `Env` per
pseudo-iteration (the #29 OOM). The structured path never OOMs because
`LoopElim` runs an acyclic havoc-and-cut on `.loop` Stmts; the CFG path has no
equivalent (`LoopElim.lean` passes `.cfg` bodies through unchanged).

This pass is the CFG-native analogue. For each natural loop in a `DetCFG`, it
recovers the loop contract (`specLoopInvariant` / `specDecreases`, attached to
the header `condGoto` transfer by `stmtsToCFG`, defaulting to the trivial
invariant `true` for contract-less SMACK loops) and replaces the loop region
with the **full** structured recipe (`LoopElim.lean:73-104`):

```
header h:    <existing invCmds>; assert(I); assume(I); condGoto G  h_then  h_exit
h_then:      havoc(M); assume(G); assume(I);                       goto bodyEntry
... body blocks, back-edge `goto h` rerouted to h_post ...
h_post:      assert(I)  -- VC2 (maintenance) — the load-bearing one
             havoc(M); assume(¬G); assume(I);                      goto kNext
h_exit:      <0-trip path> havoc(M); assume(¬G); assume(I);        goto kNext
```

The back-edge is removed, so the rewritten region is a DAG and `evalCFGBlocks`
terminates in bounded steps. VC1 (entry) is already emitted as `invCmds` by
`stmtsToCFG`; this pass adds VC2 (maintenance) on the post-body path, which is
the verification-critical obligation the naive cut would drop.

**Scope boundary:** this is a verification-path-only `Program → Program`
pre-pass. The CBMC/GOTO entry does not call `corePipelinePhases`, so the GOTO
path keeps the real cyclic CFG for unwinding.
-/

namespace Core
open Imperative Lambda

public section

namespace CFGLoopElim

abbrev Blk := DetBlock String Command Expression
abbrev Lbl := String

/-- Successor labels of a transfer command (deduplicated for `goto = condGoto tt l l`). -/
def transferTargets : DetTransferCmd String Expression → List Lbl
  | .condGoto _ lt lf _ => if lt == lf then [lt] else [lt, lf]
  | .finish _ => []

/-- Successors of a block in the CFG. -/
def blockSuccs (blk : Blk) : List Lbl := transferTargets blk.transfer

/-! ## Dominator analysis -/

/-- Predecessor map: for each label, the labels that jump to it. -/
def predMap (cfg : DetCFG) : Std.HashMap Lbl (List Lbl) := Id.run do
  let mut m : Std.HashMap Lbl (List Lbl) := {}
  for (l, _) in cfg.blocks do
    if !m.contains l then m := m.insert l []
  for (l, blk) in cfg.blocks do
    for s in blockSuccs blk do
      let cur := m.getD s []
      m := m.insert s (l :: cur)
  return m

/-- Iterative dominator dataflow to fixpoint.
    `dom(entry) = {entry}`; `dom(n) = {n} ∪ ⋂_{p ∈ preds(n)} dom(p)`.
    Returns a map label ↦ set of dominators (as a label list). -/
def computeDominators (cfg : DetCFG) : Std.HashMap Lbl (List Lbl) := Id.run do
  let allLabels := cfg.blocks.map (·.1)
  let preds := predMap cfg
  -- initialize: entry ↦ {entry}, every other node ↦ all labels (⊤)
  let mut dom : Std.HashMap Lbl (List Lbl) := {}
  for l in allLabels do
    if l == cfg.entry then
      dom := dom.insert l [cfg.entry]
    else
      dom := dom.insert l allLabels
  -- iterate to fixpoint (bounded by |blocks|+1 passes; a DAG-ish CFG converges fast)
  let fuel := allLabels.length + 1
  let mut changed := true
  let mut steps := 0
  while changed && steps < fuel do
    changed := false
    steps := steps + 1
    for l in allLabels do
      if l != cfg.entry then
        let ps := preds.getD l []
        -- intersection of preds' dominator sets
        let inter : List Lbl :=
          match ps with
          | [] => []
          | p :: rest =>
            rest.foldl (fun acc q =>
              let qd := dom.getD q []
              acc.filter (fun x => qd.contains x)) (dom.getD p [])
        let newDom := l :: inter.filter (· != l)
        let oldDom := dom.getD l []
        -- compare as sets (length + membership) cheaply
        if newDom.length != oldDom.length || newDom.any (fun x => !oldDom.contains x) then
          dom := dom.insert l newDom
          changed := true
  return dom

/-- Does `a` dominate `b`? -/
def dominates (dom : Std.HashMap Lbl (List Lbl)) (a b : Lbl) : Bool :=
  (dom.getD b []).contains a

/-! ## Natural-loop region -/

/-- A detected natural loop. -/
structure LoopRegion where
  header   : Lbl
  /-- the back-edge source (the latch block whose `goto header` is the back-edge) -/
  latch    : Lbl
  /-- all blocks in the loop body region (includes header and latch) -/
  body     : List Lbl
  /-- exit continuation: the header's successor that is NOT in the loop body -/
  kNext    : Lbl

/-- Back-edges: edges `u → v` with `v` dominating `u`. Returns `(u, v)` pairs. -/
def backEdges (cfg : DetCFG) (dom : Std.HashMap Lbl (List Lbl)) : List (Lbl × Lbl) := Id.run do
  let mut es : List (Lbl × Lbl) := []
  for (u, blk) in cfg.blocks do
    for v in blockSuccs blk do
      if dominates dom v u then
        es := (u, v) :: es
  return es

/-- Natural-loop body for back-edge `latch → header`: header plus every node that
    can reach `latch` without passing through `header`. Standard reverse reachability. -/
def naturalLoopBody (cfg : DetCFG) (header latch : Lbl) : List Lbl := Id.run do
  let preds := predMap cfg
  let mut body : List Lbl := [header]
  let mut work : List Lbl := if latch == header then [] else [latch]
  if latch != header then body := latch :: body
  while !work.isEmpty do
    match work with
    | [] => pure ()
    | n :: rest =>
      work := rest
      for p in preds.getD n [] do
        if p != header && !body.contains p then
          body := p :: body
          work := p :: work
  return body

/-- Build the loop region for a back-edge, if the header carries a det `condGoto`
    (the loop guard). Returns `none` for headers we can't analyze (e.g. `finish`). -/
def mkLoopRegion (cfg : DetCFG) (latch header : Lbl) : Option LoopRegion := do
  let hdrBlk ← cfg.blocks.lookup header
  match hdrBlk.transfer with
  | .condGoto _ lt lf _ =>
    let body := naturalLoopBody cfg header latch
    -- exit continuation = the header successor outside the body
    let kNext :=
      if body.contains lt then lf
      else lt
    some { header := header, latch := latch, body := body, kNext := kNext }
  | .finish _ => none

/-! ## Recipe synthesis -/

/-- Extract loop invariants from a header transfer's metadata.
    Returns the list of invariant expressions; defaults to `[true]` when none. -/
def invariantsFromMd (md : MetaData Expression) : List Expression.Expr :=
  let invField : MetaDataElem.Field Expression := MetaData.specLoopInvariant
  let invs := md.foldl (fun acc elem =>
    if elem.fld == invField then
      match elem.value with
      | .expr e => acc ++ [e]
      | _ => acc
    else acc) []
  if invs.isEmpty then [HasBool.tt] else invs

/-- Extract the optional measure expression from a header transfer's metadata. -/
def measureFromMd (md : MetaData Expression) : Option Expression.Expr :=
  let decField : MetaDataElem.Field Expression := MetaData.specDecreases
  md.foldl (fun acc elem =>
    if elem.fld == decField then
      match elem.value with
      | .expr e => some e
      | _ => acc
    else acc) none

/-- Modified set of the loop body: union of variables assigned by body blocks'
    commands, minus body-local `init`s (mirrors `LoopElim.lean:131-133`). -/
def loopModifiedSet (cfg : DetCFG) (region : LoopRegion) : List Expression.Ident := Id.run do
  let mut modified : List Expression.Ident := []
  let mut defined : List Expression.Ident := []
  for lbl in region.body do
    match cfg.blocks.lookup lbl with
    | some blk =>
      for c in blk.cmds do
        modified := modified ++ (HasVarsImp.modifiedVars (P := Expression) c)
        defined := defined ++ (HasVarsImp.definedVars (P := Expression) c)
    | none => pure ()
  -- dedup modified, drop body-local defs
  return modified.eraseDups.filter (fun v => !defined.contains v)

/-! ## Rewrite a single loop region into the acyclic recipe -/

/-- Build havoc commands for the modified set `M`. -/
def havocCmds (m : List Expression.Ident) : List Command :=
  m.map (fun x => HasHavoc.havoc x .empty)

/-- Build `assume(inv)` commands, one per invariant, with stable labels. -/
def assumeInvCmds (pfx : String) (loopNum : Nat) (invs : List Expression.Expr) : List Command :=
  invs.mapIdx (fun i inv => HasPassiveCmds.assume s!"{pfx}_{loopNum}_{i}" inv .empty)

/-- Build `assert(inv)` commands (the VC2 maintenance obligations). -/
def assertInvCmds (loopNum : Nat) (invs : List Expression.Expr) : List Command :=
  invs.mapIdx (fun i inv =>
    HasPassiveCmds.assert s!"arbitrary_iter_maintain_invariant_{loopNum}_{i}" inv .empty)

/-- Rewrite the CFG to eliminate one natural loop, producing an acyclic region.

    Generates four fresh auxiliary labels (suffixed with `loopNum`) and:
    - rewrites the header `h` to: keep existing cmds (VC1 invariant asserts that
      `stmtsToCFG` already emitted), append `assume(I)`, transfer
      `condGoto G  h_then  h_exit`;
    - `h_then`: `havoc(M); assume(G); assume(I)` → goto the loop's body entry
      (the header's in-body successor);
    - reroutes the latch's back-edge (`goto h`) to `h_post`;
    - `h_post`: `assert(I)` (VC2) ; `havoc(M); assume(¬G); assume(I)` → goto kNext;
    - `h_exit` (the 0-trip path): `havoc(M); assume(¬G); assume(I)` → goto kNext. -/
def rewriteLoop (cfg : DetCFG) (region : LoopRegion) (loopNum : Nat) : DetCFG :=
  match cfg.blocks.lookup region.header with
  | none => cfg
  | some hdrBlk =>
    match hdrBlk.transfer with
    | .finish _ => cfg
    | .condGoto g lt lf md =>
      let invs := invariantsFromMd md
      let modSet := loopModifiedSet cfg region
      -- body entry = the header's in-body successor; exit target = kNext
      let bodyEntry := if region.body.contains lt then lt else lf
      let hThen := s!"cfgloop_then_{loopNum}"
      let hPost := s!"cfgloop_post_{loopNum}"
      let hExit := s!"cfgloop_exit_{loopNum}"
      let notG := HasNot.not g
      -- NOTE on measure (`decreases`) loops: `stmtsToCFG` already lowers the
      -- measure into the header cmds (`init m_old; assume m_old == D;
      -- assert(m_old >= 0)` = VC3) plus a separate decrease block on the
      -- back-edge (`assert(D < m_old)` = VC4). This pass deliberately does NOT
      -- re-emit those VCs — doing so double-counts VC3 and leaves the original
      -- decrease block's VC4 evaluated against havoc'd state. Closing the
      -- measure case correctly requires recognizing and rewriting the
      -- decrease block too (recover `m_old`/`D` and splice VC4 onto h_post),
      -- which the 3-of-313 measure-bearing procs in the corpus would need.
      -- For now the contract-less / invariant-only loops (the #29 case and the
      -- 310 SMACK loops) are fully handled; measure loops still terminate
      -- bounded but may carry a stray `unknown` on the orphaned decrease block.
      -- Rewritten header: existing cmds (VC1) ++ assume(I); condGoto g hThen hExit.
      let newHdr : Blk :=
        { cmds := hdrBlk.cmds ++ assumeInvCmds "assume_invariant" loopNum invs,
          transfer := .condGoto g hThen hExit md }
      -- h_then: havoc(M); assume(G); assume(I) → bodyEntry
      let thenBlk : Blk :=
        { cmds := havocCmds modSet
                  ++ [HasPassiveCmds.assume s!"assume_guard_{loopNum}" g .empty]
                  ++ assumeInvCmds "assume_loop_invariant" loopNum invs,
          transfer := .goto bodyEntry }
      -- h_post: assert(I) [VC2]; havoc(M); assume(¬G); assume(I) → kNext
      let postBlk : Blk :=
        { cmds := assertInvCmds loopNum invs
                  ++ havocCmds modSet
                  ++ [HasPassiveCmds.assume s!"not_guard_{loopNum}" notG .empty]
                  ++ assumeInvCmds "exit_invariant" loopNum invs,
          transfer := .goto region.kNext }
      -- h_exit (0-trip): havoc(M); assume(¬G); assume(I) → kNext
      let exitBlk : Blk :=
        { cmds := havocCmds modSet
                  ++ [HasPassiveCmds.assume s!"not_guard_exit_{loopNum}" notG .empty]
                  ++ assumeInvCmds "exit0_invariant" loopNum invs,
          transfer := .goto region.kNext }
      -- Reroute the latch back-edge (goto header) → hPost, and replace the header block.
      let rewireTransfer (t : DetTransferCmd String Expression) : DetTransferCmd String Expression :=
        match t with
        | .condGoto p a b m =>
          .condGoto p (if a == region.header then hPost else a)
                      (if b == region.header then hPost else b) m
        | .finish m => .finish m
      let newBlocks := cfg.blocks.map (fun (l, blk) =>
        if l == region.header then (l, newHdr)
        else if l == region.latch then (l, { blk with transfer := rewireTransfer blk.transfer })
        else (l, blk))
      { cfg with blocks := newBlocks ++ [(hThen, thenBlk), (hPost, postBlk), (hExit, exitBlk)] }

/-- Does this CFG have any back-edge (cheap gate to skip non-loop CFGs)? -/
def hasBackEdge (cfg : DetCFG) : Bool :=
  let dom := computeDominators cfg
  !(backEdges cfg dom).isEmpty

/-- Eliminate all natural loops in a single `DetCFG`. Processes one back-edge at
    a time, recomputing dominators after each rewrite (the block set changes).
    Bounded by an explicit fuel = original back-edge count, so it always terminates. -/
partial def elimLoops (cfg : DetCFG) : DetCFG := Id.run do
  let mut cur := cfg
  let mut loopNum := 0
  let mut fuel := (backEdges cfg (computeDominators cfg)).length + 1
  while fuel > 0 do
    fuel := fuel - 1
    let dom := computeDominators cur
    let bes := backEdges cur dom
    match bes with
    | [] => break
    | (latch, header) :: _ =>
      match mkLoopRegion cur latch header with
      | some region =>
        cur := rewriteLoop cur region loopNum
        loopNum := loopNum + 1
      | none => break
  return cur

end CFGLoopElim

/-- Eliminate loops in all `.cfg`-bodied procedures of a Core program, replacing
    each natural loop with the acyclic invariant-based encoding. `.structured`
    bodies pass through unchanged (they are handled by `loopElim`); this is the
    inverse passthrough of `LoopElim.lean`. -/
def cfgLoopElim (p : Program) : Program :=
  { decls := p.decls.map fun
      | .proc proc md =>
        match proc.body with
        | .cfg cfgBody =>
          if CFGLoopElim.hasBackEdge cfgBody then
            .proc { proc with body := .cfg (CFGLoopElim.elimLoops cfgBody) } md
          else .proc proc md
        | .structured _ => .proc proc md
      | other => other }

/-- CFG loop elimination as a `CoreTransformM` pass. -/
def cfgLoopElim' (p : Program) : Transform.CoreTransformM (Bool × Program) := do
  return (true, cfgLoopElim p)

/-- CFG-native loop-elimination pipeline phase. Mirrors `loopElimPipelinePhase`
    but operates on `.cfg` bodies. Obligations whose path includes the
    invariant/guard assumptions introduced here are over-approximations, so SAT
    models are demoted to unknown (same treatment as structured loop elim). -/
def cfgLoopElimPipelinePhase : PipelinePhase where
  transform := cfgLoopElim'
  phase.name := "CFGLoopElim"
  phase.getValidation obligation :=
    if obligationHasLabelPrefix obligation loopElimInvariantPrefix
       || obligationHasLabelPrefix obligation loopElimGuardPrefix
       || obligationHasLabelPrefix obligation "assume_invariant"
       || obligationHasLabelPrefix obligation "assume_guard" then
      .modelToValidate (fun _ => false)
    else .modelPreserving

end -- public section

end Core
