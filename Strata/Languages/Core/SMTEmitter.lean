/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.SMTEncoder
public import Strata.DL.SMT.Solver
public import Strata.DL.SMT.Encoder

/-! # Env-scoped SMT-LIB emission

The batch backend writes one `.smt2` file per obligation. Consecutive
obligations share most of their assumption entries. This module renders each
entry's SMT-LIB text once per verification environment and assembles each
obligation's file from the captured blocks.

Entry terms are rendered through `Encoder.encodeTerm` against an in-memory
writer. On-the-fly `declare-fun`s and sanitize/uniquify renaming therefore
happen against one env-scoped `EncoderState`. Each entry's captured text is
exactly what per-obligation encoding would produce from that state; the
assembled file orders it per frame rather than in `encodeCore`'s bulk kind
order, which is semantically inert. Each file's tail is encoded against a
fork of that state, which is then discarded, so obligation-local names
cannot leak.

`EmitterState.frames` holds one `CapturedFrame` per frame of the SMT
encoding fold (`SMTEncodeState` in `Core.SMTEncoder`). After the fold
advances to an obligation, `EmitterState.sync` realigns the two frame
lists. Matched frames are kept. Divergent frames are dropped, restoring the
`EncoderState` snapshot taken at frame open. New entries are captured.
`sync` never modifies the fold's frames.

For example, `PathConditionsFold`'s `Demo` procedure yields four obligations
whose assumptions share prefixes (`c` is the branch condition):
```
A1: [ [h0] ]
A2: [ [h0, h1] ]
A3: [ [h0, h1], [c]  ]
A4: [ [h0, h1], [¬c] ]
```
Emission processes them as:
* A1 — capture frame ⟨h0⟩: a `declare-fun` for each free variable `h0`
  mentions into `declText`, its `(assert …)` into `assertText`.
* A2 — extend to ⟨h0, h1⟩, rendering only `h1`.
* A3 — capture a second frame ⟨c⟩.
* A4 — drop ⟨c⟩, restoring the `EncoderState` from ⟨c⟩'s open — names ⟨c⟩
  declared are forgotten, so ⟨¬c⟩'s rendering may reuse them; capture ⟨¬c⟩.

Across the run, `h0` and `h1` are rendered once instead of four and three
times. Had A3 pruned some entries, it would fall back to `encodeCore`
(captured text asserts every entry) while its frames still sync, keeping A4
on the fast path.

Each obligation's file is assembled from the captured blocks; A3's:
```
headerPreText            -- set-logic, solver prelude
prologue                 -- A3's sorts and datatypes, rendered fresh
headerPostText           -- base declarations and axioms
⟨h0, h1⟩ ⟨c⟩ declTexts
⟨h0, h1⟩ ⟨c⟩ assertTexts
tail                     -- A3's remaining declarations and axioms, goal,
                         -- check-sat; rendered against a discarded fork
```

Fallback to `encodeCore` happens in `verifySingleEnv`. Pruning and
`usableFor` (context sorts that could collide with a captured name) affect
only the one obligation. A managed-name collision instead sets `disabled`
for the rest of the environment: pre-seeding a `varDecl`'s name is correct
only when no entry references the variable before the frame declaring it,
and a collision means that property failed.

TODO: if value and type names are proven distinct after sanitization and
monomorphization, `usableFor` becomes dead code.

TODO: if the decl-before-use property is proven for
`ObligationExtraction.extractObligations`, the managed-name check becomes
dead code.
-/

namespace Core.SMT

open Strata.SMT

public section

/-! ## Shared SMT-LIB emission

Shared pieces of an obligation's `.smt2` file. Every emitter of such files
(`Strata.SMT.Encoder.encodeCore`, the env-scoped capture below) must use
these definitions, so the emitters agree by construction. In particular, all
emitters must use the same managed-name `UF` key (`Encoder.seedManagedName`);
otherwise one would miss another's registration. -/

/-- Emit a context's uninterpreted-function declarations and interpreted
    function definitions, skipping managed names (their declarations come from
    the caller's variable declarations/definitions instead) but registering them
    so references resolve to the raw name. -/
def writeContextDeclarations (ctx : SMT.Context)
    (managedNames : Std.HashSet String) : EncoderM Unit := do
  let (managedUfs, ufsToDecl) :=
    ctx.ufs.toArray.partition fun uf => managedNames.contains uf.id
  let _ ← ufsToDecl.mapM Encoder.encodeUF
  modify fun estate => managedUfs.foldl (init := estate) Encoder.seedManagedName
  let _ ← ctx.ifs.toArray.mapM Encoder.encodeFunctionDef

/-- Emit a verification condition's closing block: the `get-value` ids, the
    `check-sat`(-assuming) commands for whichever checks are requested, and the
    final-message info string. Assumes `obligationId` is the encoded goal and
    that every symbol it mentions is already declared. -/
def writeCheckSatBlock (obligationId obligationTerm : Term)
    (md : Imperative.MetaData Expression)
    (satisfiabilityCheck validityCheck : Bool)
    (label : String) (managedNames : Std.HashSet String) :
    EncoderM (List String) := do
  let estate ← get
  let ids := estate.functions.toList.filterMap fun (uf, id) =>
    if uf.args.isEmpty && !managedNames.contains uf.id then some id else none

  let bothChecks := satisfiabilityCheck && validityCheck

  if bothChecks then
    Solver.comment "Satisfiability"
    Imperative.SMT.addLocationInfo (P := Expression) (md := md)
      (message := ("sat-message", "Property can be satisfied"))
    let obligationStr ← Solver.termToSMTString obligationId
    let _ ← Solver.checkSatAssuming [obligationStr] ids

    Solver.comment "Validity"
    Imperative.SMT.addLocationInfo (P := Expression) (md := md)
      (message := ("unsat-message", "Property is always true"))
    let negObligationStr := s!"(not {obligationStr})"
    let _ ← Solver.checkSatAssuming [negObligationStr] ids
  else
    if satisfiabilityCheck then
      Solver.comment "Satisfiability"
      Imperative.SMT.addLocationInfo (P := Expression) (md := md)
        (message := ("sat-message", "Property can be satisfied"))
      Solver.assert obligationId
      let _ ← Solver.checkSat ids
    else if validityCheck then
      Solver.comment "Validity"
      Imperative.SMT.addLocationInfo (P := Expression) (md := md)
        (message := ("unsat-message", "Property is always true"))
      Solver.assert (← Encoder.encodeTerm (Strata.SMT.Factory.not obligationTerm))
      let _ ← Solver.checkSat ids

  let rawMsg := md.getPropertySummary.getD label
  Solver.setInfoString "final-message" rawMsg
  pure ids

end -- public section

end Core.SMT

namespace Core.SMT.Emitter

open Std (ToFormat Format format)
open Lambda Strata Strata.SMT Imperative Imperative.PathConditions

public section

/-! ## Emission state -/

/-- The encoding fold's frame type, at Core's instantiation. -/
abbrev FoldFrame :=
  Imperative.PathConditions.PathConditionFrame
    SMTCheckpoint SMTEncodedPathCondition Core.Expression

/-- The captured contribution of one path-condition frame. -/
structure CapturedFrame where
  /-- The corresponding fold frame's entries, oldest first (the alignment
      key). -/
  entries : Array (PathConditionEntry Core.Expression)
  /-- Declarations this frame's entries caused, in entry order:
      on-the-fly `declare-fun`s, `varDecl` handles, drained definitions. -/
  declText : String
  /-- The frame's `(assert …)` lines, rendered from the same encoder state. -/
  assertText : String
  /-- Encoder state at frame open; restored when the frame is dropped, so
      names declared by dropped entries are forgotten. -/
  estateBefore : EncoderState
  /-- Env-scoped drain context at frame open; restored with `estateBefore`. -/
  dctxBefore : SMT.Context
  /-- Checkpoint context declared as of frame open; restored likewise. -/
  ctxCapturedBefore : SMT.Context

/-- Environment-scoped emission state, threaded through `verifySingleEnv`
    alongside the encoding fold's `SMTEncodeState`. -/
structure EmitterState where
  /-- The env-scoped encoder state: names declared by captured entries.
      Grows only through capture. -/
  estate : EncoderState
  /-- Solver-side term/type string caches, shared across the environment. -/
  sstate : SolverState
  /-- File header before the sort/datatype prologue: logic and solver
      prelude. Environment-constant, captured once by `init`. -/
  headerPreText : String
  /-- File header after the prologue: the base context's declarations,
      definitions, and axioms (all may reference sorts/datatypes, hence
      after them). Environment-constant. -/
  headerPostText : String
  /-- Env-scoped context for capture-time drains (`processPendingFnDefs`),
      so each definition is emitted once per environment. -/
  dctx : SMT.Context
  /-- Checkpoint context whose UF registrations capture has declared.
      Advances as frames are captured, rewinds with them. -/
  ctxCaptured : SMT.Context
  /-- One `CapturedFrame` per fold frame, newest first (like
      `SMTEncodeState.frames`). -/
  frames : List CapturedFrame
  /-- Every managed (program-variable) name captured so far. Never shrinks. -/
  managedNames : Std.HashSet String
  /-- Every name capture declared other than managed seeds. Never shrinks. -/
  discoveredNames : Std.HashSet String
  /-- The base context's pre-declared (sort/datatype) names
      (see `EmitterState.usableFor`). -/
  basePreDeclared : Std.HashSet String
  /-- Number of base-context axioms, all asserted in the header. Contexts
      extend the base append-only, so the axioms past this count are the ones
      an obligation's own tail must assert. -/
  baseAxmCount : Nat
  /-- Set when captured text can no longer be trusted for this environment
      (managed-name conflict or capture failure). -/
  disabled : Bool := false


/-- The final SMT-LIB names registered in an encoder state, for the
    managed-name safety check. -/
private def registeredNames (estate : EncoderState) : Std.HashSet String :=
  estate.functions.toList.foldl (fun acc (p : UF × String) => acc.insert p.2)
    (∅ : Std.HashSet String)

/-- Fresh emission state. Captures the environment-constant file header once:
    logic, solver prelude, and the base context's declarations, definitions,
    and axioms, mirroring `encodeCore`'s header phases in order.

    Sorts and datatypes are not captured: a context only sees them during
    encoding, so the base context has seen almost none. `emitObligation`
    renders them per obligation instead, between the two header halves. -/
def EmitterState.init (baseCtx : SMT.Context) (prelude : SolverM Unit) :
    IO EmitterState := do
  let pre := baseCtx.preDeclaredNames
  let preludeAct : EncoderM Unit := do
    Solver.setLogic "ALL"
    prelude
  let ((_, estate), headerPreText, sstate) ←
    Solver.recordToString (preludeAct.run (EncoderState.initWithNames pre))
  let baseDeclAct : EncoderM Unit := do
    -- The base context has no managed names: program variables come from
    -- `varDecl` entries.
    writeContextDeclarations baseCtx {}
    Encoder.encodeAxioms baseCtx.axms.toArray
  let ((_, estate), headerPostText, sstate) ←
    Solver.recordToString (baseDeclAct.run estate) sstate
  return {
    estate := estate
    sstate := sstate
    headerPreText := headerPreText
    headerPostText := headerPostText
    dctx := baseCtx
    ctxCaptured := baseCtx
    frames := []
    managedNames := {}
    discoveredNames := registeredNames estate
    basePreDeclared := pre
    baseAxmCount := baseCtx.axms.toArray.size }

/-! ## Frame alignment

Decides how much of `EmitterState.frames` is still valid for the current
obligation: `alignMirror` finds the longest prefix matching the fold's
frames, and whether the next frame can be extended in place. Entries are
compared with `fastEq` (pointer-accelerated), so matches settle by pointer
identity almost always. -/

/-- `a[i:]` agrees element-wise with `b[i:]` under `fastEq`, for as far as
    `a` runs. -/
private def entriesAgreeFrom (a b : Array (PathConditionEntry Core.Expression))
    (i : Nat) : Bool :=
  if h : i < a.size then
    if hb : i < b.size then
      (a[i].fastEq b[i]) && entriesAgreeFrom a b (i + 1)
    else false
  else true
  termination_by a.size - i
  decreasing_by omega

/-- Element-wise `fastEq` on entry arrays. -/
def entriesEq (a b : Array (PathConditionEntry Core.Expression)) : Bool :=
  a.size == b.size && entriesAgreeFrom a b 0

/-- `a` is a proper prefix of `b` (so `b` extends `a` by ≥ 1 entry). -/
def entriesProperPrefix (a b : Array (PathConditionEntry Core.Expression)) : Bool :=
  a.size < b.size && entriesAgreeFrom a b 0

/-- Returns the length of the longest common prefix of `mirror` and
    `target`, and whether the first frame after that prefix can be extended
    in place. -/
def alignMirror (mirror : List CapturedFrame) (target : List FoldFrame)
    (k : Nat) : Nat × Bool :=
  match mirror, target with
  | b :: brest, a :: arest =>
    if entriesEq b.entries a.entries then alignMirror brest arest (k + 1)
    else (k, entriesProperPrefix b.entries a.entries)
  | _, _ => (k, false)

/-! ## Capture

Capture runs per frame delta, in two buffered passes mirroring `encodeCore`'s
kind order: a declarations pass (`declText`) and an assertions pass
(`assertText`). Definition axioms are *not* asserted here: they live in each
obligation's drained context, and its tail asserts them.

Entries whose fold-level encoding failed (deferred errors) are skipped. Any
obligation keeping such an entry fails at `snapshotObligation`, before
emission is consulted. -/

/-- The per-kind items of one frame delta, oldest first, as encoded by the
    encoding fold. -/
structure DeltaItems where
  varDecls : List VarDeclaration := []
  varDefs : List (VarDefinition × SMT.PendingFnQueue) := []
  distincts : List (String × Term × SMT.PendingFnQueue) := []
  assumptions : List (String × Term × SMT.PendingFnQueue) := []

/-- Select `deltaEntries`' items from a frame's fold output `out`. -/
def deltaItems (out : SMTEncodedPathCondition)
    (deltaEntries : Array (PathConditionEntry Core.Expression)) : DeltaItems :=
  let counts := deltaEntries.foldl (init := (0, 0, 0, 0)) fun (a, d, vdef, vdecl) e =>
    match e with
    | .assumption .. => (a + 1, d, vdef, vdecl)
    | .distinct .. => (a, d + 1, vdef, vdecl)
    | .varDecl _ _ (.det _) => (a, d, vdef + 1, vdecl)
    | .varDecl _ _ .nondet => (a, d, vdef, vdecl + 1)
  let (nA, nD, nVdef, nVdecl) := counts
  { varDecls := (out.varDeclsRev.take nVdecl).reverse
    varDefs := (out.varDefsRev.take nVdef).reverse
    distincts := ((out.distinctsRev.take nD).reverse).filterMap fun e =>
      match e.result with
      | .ok (t, pending) => some (e.label, t, pending)
      | .error _ => none
    assumptions := ((out.assumptionsRev.take nA).reverse).filterMap fun e =>
      match e.result with
      | .ok (t, pending) => some (e.label, t, pending)
      | .error _ => none }

/-- Result of capturing one frame delta. -/
structure CaptureResult where
  estate : EncoderState
  sstate : SolverState
  dctx : SMT.Context
  declText : String
  assertText : String
  /-- Names newly registered in the encoder state, minus the managed seeds. -/
  discovered : List String
  managed : List String

/-- Drain pending factory-function definitions, lifting the pure error into
    `EncoderM`. -/
private def drainPending (factory : @Lambda.Factory CoreLParams)
    (dctx : SMT.Context) (pending : SMT.PendingFnQueue) : EncoderM SMT.Context :=
  match processPendingFnDefs factory dctx pending with
  | .ok dctx' => pure dctx'
  | .error e => throw (IO.userError s!"SMT.Emitter.captureDelta: {e}")

/-- Emit the definitions `processPendingFnDefs` newly committed to `dctx'`
    relative to `dctx` (its ordered sets grow append-only, so the delta is a
    suffix). -/
private def emitDrainedDefs (dctx dctx' : SMT.Context) :
    EncoderM Unit := do
  let oldUfs := (dctx.ufs.toArray).size
  let oldIfs := (dctx.ifs.toArray).size
  for uf in (dctx'.ufs.toArray).toList.drop oldUfs do
    let _ ← Encoder.encodeUF uf
  for f in (dctx'.ifs.toArray).toList.drop oldIfs do
    let _ ← Encoder.encodeFunctionDef f

/-- The declarations pass of one frame delta: the UF registrations between
    the fold checkpoints `ctxBefore`/`ctxAfter`, the `varDecl`/`varDef`
    handles (raw, pre-seeded names), and the newly drained factory-function
    definitions. Returns the advanced drain context and the managed names
    declared. -/
private def declarationsPass (factory : @Lambda.Factory CoreLParams)
    (dctx : SMT.Context) (ctxBefore ctxAfter : SMT.Context)
    (items : DeltaItems) : EncoderM (SMT.Context × List String) := do
  -- Managed names of *this* delta: their declarations come from the varDecl
  -- entries below, not from the context-UF pass.
  let deltaManaged : Std.HashSet String :=
    (items.varDecls.map (·.name) ++ items.varDefs.map (·.1.name)).foldl
      (·.insert ·) (∅ : Std.HashSet String)
  let mut dctx := dctx
  let mut managed : List String := []
  -- UF registrations this delta introduced.
  for uf in (ctxAfter.ufs.toArray).toList.drop (ctxBefore.ufs.toArray).size do
    if !deltaManaged.contains uf.id then
      let _ ← Encoder.encodeUF uf
  -- Variable declarations: declare-fun, raw name, pre-seeded.
  for d in items.varDecls do
    Solver.declareFun d.name [] d.ty
    modify (Encoder.seedManagedName · { id := d.name, args := [], out := d.ty })
    managed := d.name :: managed
  -- Variable definitions: drain body deps, define-fun, raw name, pre-seeded.
  for (d, pending) in items.varDefs do
    let dctx' ← drainPending factory dctx pending
    emitDrainedDefs dctx dctx'
    dctx := dctx'
    let bodyEnc ← Encoder.encodeTerm d.body
    Solver.defineFunTerm d.name [] d.ty bodyEnc
    modify (Encoder.seedManagedName · { id := d.name, args := [], out := d.ty })
    managed := d.name :: managed
  -- Assumption/distinct definition deps.
  for (_, _, pending) in items.distincts ++ items.assumptions do
    let dctx' ← drainPending factory dctx pending
    emitDrainedDefs dctx dctx'
    dctx := dctx'
  return (dctx, managed)

/-- The assertions pass of one frame delta: assert each distinct and
    assumption term. -/
private def assertionsPass (items : DeltaItems) : EncoderM Unit := do
  for (_, t, _) in items.distincts ++ items.assumptions do
    let tEnc ← Encoder.encodeTerm t
    Solver.assert tEnc

/-- Capture one frame delta: `declarationsPass`, then `assertionsPass`,
    against separate buffers, threading encoder/solver state through both. -/
def captureDelta (factory : @Lambda.Factory CoreLParams)
    (estate : EncoderState) (sstate : SolverState)
    (dctx : SMT.Context) (ctxBefore ctxAfter : SMT.Context)
    (items : DeltaItems) : IO CaptureResult := do
  let oldFunctions := estate.functions
  let (((dctx, managed), estate), declText, sstate) ←
    Solver.recordToString
      ((declarationsPass factory dctx ctxBefore ctxAfter items).run estate) sstate
  let ((_, estate), assertText, sstate) ←
    Solver.recordToString ((assertionsPass items).run estate) sstate
  -- Everything newly registered that we did not seed ourselves was declared
  -- on the fly (or is a drained definition); record for the safety check.
  let managedSet := managed.foldl (·.insert ·) (∅ : Std.HashSet String)
  let discovered := estate.functions.toList.filterMap fun (uf, id) =>
    if oldFunctions.contains uf || managedSet.contains id then none else some id
  return {
    estate := estate
    sstate := sstate
    dctx := dctx
    declText := declText
    assertText := assertText
    discovered := discovered
    managed := managed }

/-! ## Sync

Realigns `EmitterState.frames` with the fold's frames after each `advance`:
keep the common prefix (`alignMirror`), drop divergent frames (restoring
their open-time snapshots), then capture what is new (`captureDelta`) and
record it (`EmitterState.record`). The managed-name check lives in
`record`. -/

/-- Record a capture result into the state, appending to an existing frame
    (`extend`) or opening a new one. The name sets only grow, even for
    dropped frames, so the managed-name check can only cause unnecessary
    fallbacks, never unsound reuse. -/
private def EmitterState.record (es : EmitterState) (r : CaptureResult)
    (entries : Array (PathConditionEntry Core.Expression))
    (extend : Bool) (ctxCaptured : SMT.Context) : EmitterState :=
  let conflict :=
    r.discovered.any (fun n => es.managedNames.contains n) ||
    r.managed.any (fun n => es.discoveredNames.contains n) ||
    (r.managed.any fun n => r.discovered.contains n)
  let fresh : CapturedFrame :=
    { entries := entries
      declText := r.declText
      assertText := r.assertText
      estateBefore := es.estate
      dctxBefore := es.dctx
      ctxCapturedBefore := es.ctxCaptured }
  let newFrames : List CapturedFrame :=
    match extend, es.frames with
    | true, top :: rest =>
      let grown : CapturedFrame :=
        { top with
          entries := entries
          declText := top.declText ++ r.declText
          assertText := top.assertText ++ r.assertText }
      grown :: rest
    | _, frames => fresh :: frames
  { es with
    estate := r.estate
    sstate := r.sstate
    dctx := r.dctx
    frames := newFrames
    ctxCaptured := ctxCaptured
    managedNames := r.managed.foldl (·.insert ·) es.managedNames
    discoveredNames := r.discovered.foldl (·.insert ·) es.discoveredNames
    disabled := es.disabled || conflict }

/-- Keep the oldest `keep` captured frames, restoring the encoder state,
    drain context, and checkpoint context saved when the oldest dropped
    frame opened. `mirror` is `es.frames` oldest first. -/
private def EmitterState.rewindTo (es : EmitterState)
    (mirror : List CapturedFrame) (keep : Nat) : EmitterState :=
  match mirror.drop keep with
  | [] => es
  | oldestDropped :: _ =>
    { es with
      estate := oldestDropped.estateBefore
      dctx := oldestDropped.dctxBefore
      ctxCaptured := oldestDropped.ctxCapturedBefore
      frames := (mirror.take keep).reverse }

/-- The checkpoint context after a frame: the next frame's base checkpoint,
    or `currentCtx` for the newest frame. -/
private def ctxAfter (rest : List FoldFrame) (currentCtx : SMT.Context) :
    SMT.Context :=
  match rest with
  | next :: _ => next.baseCheckpoint.ctx
  | [] => currentCtx

/-- Capture the frames, oldest first: the first from index `already`, the
    rest in full. `extendFirst` appends the first capture to the kept top
    frame instead of opening a new one. -/
private def EmitterState.captureFrames (es : EmitterState)
    (factory : @Lambda.Factory CoreLParams) (currentCtx : SMT.Context)
    (fs : List FoldFrame) (already : Nat) (extendFirst : Bool) :
    IO EmitterState := do
  match fs with
  | [] => return es
  | a :: rest =>
    let ctxA := ctxAfter rest currentCtx
    let delta := if already == 0 then a.entries
      else a.entries.extract already a.entries.size
    let r ← captureDelta factory es.estate es.sstate es.dctx
      es.ctxCaptured ctxA (deltaItems a.output delta)
    (es.record r a.entries (extend := extendFirst) ctxA).captureFrames
      factory currentCtx rest 0 false

/-- Realign `es.frames` with the fold's frames.
    No-op when `disabled`; any capture failure sets `disabled`. -/
def EmitterState.sync (factory : @Lambda.Factory CoreLParams) (es : EmitterState)
    (foldFrames : List FoldFrame) (currentCtx : SMT.Context) :
    IO EmitterState := do
  if es.disabled then return es
  try
    -- Both oldest first, matching the fold's frame order under `reverse`.
    let target := foldFrames.reverse
    let mirror := es.frames.reverse
    let (keep, extend) := alignMirror mirror target 0
    let es := es.rewindTo mirror (keep + if extend then 1 else 0)
    -- When the kept top frame is extendable, its first `already` entries
    -- are already captured.
    let already := if extend then (mirror[keep]?.map (·.entries.size)).getD 0 else 0
    es.captureFrames factory currentCtx (target.drop keep) already extend
  catch _ =>
    return { es with disabled := true }

/-! ## Per-obligation tail and file assembly -/

/-- The captured per-frame declaration blocks, oldest frame first. Valid
    only immediately after `sync`, for an unpruned obligation that passes
    `usableFor`. -/
def EmitterState.declPieces (es : EmitterState) : List String :=
  es.frames.foldl (fun acc f => f.declText :: acc) []

/-- The captured per-frame assertion blocks, oldest frame first. See
    `EmitterState.declPieces`. -/
def EmitterState.assertPieces (es : EmitterState) : List String :=
  es.frames.foldl (fun acc f => f.assertText :: acc) []

/-- Whether the captured blocks may be emitted for an obligation with drained
    context `ctx`. Beyond `disabled`, rejects obligations whose context
    declares sorts/datatypes the base context did not: capture uniquified
    against the base context's pre-declared names only, so a later-registered
    sort could collide with a captured name. -/
def EmitterState.usableFor (es : EmitterState) (ctx : SMT.Context) : Bool :=
  if es.disabled then false
  else
    let pre := ctx.preDeclaredNames
    pre.toList.all fun n => es.basePreDeclared.contains n || !es.discoveredNames.contains n

/-- A complete, assembled `.smt2` file for one obligation, plus the encoder
    state it was rendered from. -/
structure CapturedFile where
  /-- The file contents as blocks, in order: header halves, per-obligation
      prologue, per-frame declaration and assertion text, tail. -/
  pieces : List String
  /-- The `get-value` ids for the check-sat commands in `pieces`. -/
  ids : List String
  /-- The encoder state after rendering `pieces`. -/
  estate : EncoderState

/-- Write already-assembled SMT-LIB blocks verbatim, in order. Deliberately
    scoped to this module, whose captured text is the only text known to be
    rendered against an `EncoderState` it owns. -/
def emitPrerendered (pieces : List String) : SolverM Unit := do
  let stream := (← read).smtLibInput
  for p in pieces do
    stream.putStr p

/-- Assemble one obligation's `.smt2` file. Callers must check `usableFor`
    first. A captured assertion can only mention symbols declared in the
    header or during capture, so the tail's declarations coming last is
    sound. No `factory` is needed: `ctx` arrives already drained. -/
def EmitterState.emitObligation
    (es : EmitterState) (ctx : SMT.Context) (goalTerm : Term)
    (md : Imperative.MetaData Core.Expression) (label : String)
    (managedNames : Std.HashSet String)
    (satisfiabilityCheck validityCheck : Bool) : IO CapturedFile := do
  let declPieces := es.declPieces
  let assertPieces := es.assertPieces
  -- Prologue: this obligation's sorts and datatypes. They are name-neutral,
  -- so rendering outside the captured lineage is sound.
  let prologueAct : SolverM Unit := writeSortsAndDatatypes ctx
  let (_, prologueText, _) ← Solver.recordToString prologueAct es.sstate
  let tailAct : EncoderM (List String) := do
    writeContextDeclarations ctx managedNames
    -- This obligation's own definition axioms.
    let axms := ctx.axms.toArray
    Encoder.encodeAxioms (axms.extract es.baseAxmCount axms.size)
    -- The goal, then the shared check-sat block.
    let goalEnc ← Encoder.encodeTerm goalTerm
    writeCheckSatBlock goalEnc goalTerm md
      satisfiabilityCheck validityCheck label managedNames
  -- The fork: never written back to `es`.
  let ((ids, forkEstate), tailText, _) ←
    Solver.recordToString (tailAct.run es.estate) es.sstate
  let pieces :=
    (es.headerPreText :: prologueText :: es.headerPostText :: declPieces)
      ++ assertPieces ++ [tailText]
  return { pieces, ids, estate := forkEstate }

/-- `sync` with the fold's advanced frames, then `emitObligation` if the
    obligation is not `pruned` and `usableFor` holds. Returns `none`
    otherwise; the caller then encodes the obligation itself. `sync` runs
    either way, so `es.frames` stays in step for later obligations. -/
def EmitterState.syncAndEmit (es : EmitterState)
    (factory : @Lambda.Factory CoreLParams)
    (foldFrames : List FoldFrame)
    (currentCtx : SMT.Context) (pruned : Bool)
    (ctx : SMT.Context) (goalTerm : Term)
    (md : Imperative.MetaData Core.Expression) (label : String)
    (managedNames : Std.HashSet String)
    (satisfiabilityCheck validityCheck : Bool) :
    IO (EmitterState × Option CapturedFile) := do
  let es ← es.sync factory foldFrames currentCtx
  if !pruned && es.usableFor ctx then
    let cf ← es.emitObligation ctx goalTerm md label managedNames
      satisfiabilityCheck validityCheck
    return (es, some cf)
  return (es, none)

end -- public section

end Core.SMT.Emitter
