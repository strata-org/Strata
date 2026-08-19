/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.Resolution
public import Strata.Languages.Laurel.MapStmtExpr
public import Strata.Languages.Laurel.LaurelPass
import Strata.Languages.Laurel.HeapParameterization
import Strata.Languages.Laurel.HeapParameterizationConstants
import Strata.Languages.Laurel.LiftInstanceProcedures
import Strata.Util.Tactics

public section

namespace Strata.Laurel

/-! ## Yield elimination pass

This pass lowers coroutine `old`-semantics on **both** the body path and the
caller path — the two are complementary halves of one step and share the
`Snapshot` / labeled-`Old` vocabulary, so they live together:

* **Body path** (verify-only, `verifyCoroutine := true`): each coroutine's
  `$body` copy becomes a regular procedure whose every `yield` is an inline
  rely/guarantee step (below). See `runYieldElimBody`.
* **Caller path** (always on): the lifted `resume` procedure and its callers
  get their `oldRelies`/`oldGuarantees` lowered and a per-instance `$h1_co`
  last-suspension heap threaded through. See `## Coroutine rely-heap threading`
  below and `coroutineRelyHeap`. This runs even without `verifyCoroutine`,
  because the non-verify elaboration path also emits `OldRelies`/`OldGuarantee`
  markers on its `resume` procedures and this is the only pass that lowers them.

### Body path

For each coroutine declaration

```laurel
coroutine c(args)
  requires P_init
  ensures  Q_final
  relies   R_1, …, R_n
  guarantees G_1, …, G_n
  modifies M
{ body }                              // body may contain `yield`
```

we emit a regular procedure with the same name, parameters, and types.
The user-written `relies` / `guarantees` fire only at yield sites (not as
the procedure's own pre/postconditions — see `yieldElimProc`); the body
is rewritten to replace each `yield` with an inline step:

```laurel
procedure c(args)
  requires P_init
  ensures  Q_final
  modifies M
{ body[yield ↦ <inline-step>] }
```

where each `yield` is replaced by the inline-step block:

```laurel
{
  assert ⋀ guarantees          // oldGuarantee reads $old_heap (start-of-step)
  snapshot $old_heap           // = $heap, pre-havoc  (for the rely's old)
  havocHeap()                  // env havocs the heap
  assume ⋀ relies              // oldRelies reads $old_heap; rest reads live $heap
  snapshot $old_heap           // = $heap, post-havoc (start of the next step)
}
```

### The single snapshot

Both clause families are **two-state**, relating a prior heap to the current
`$heap`. One reassigned snapshot `$old_heap` serves both roles because a
coroutine step is linear:

* a `guarantees` `old(e)` (surface: `oldGuarantee(e)`) means the heap at the
  start of this step — `$old_heap` when `assert ⋀guarantees` runs, before the
  block reassigns it;
* a `relies` `old(e)` (surface: `oldRelies(e)`) means the heap right before the
  environment acted — `$old_heap` after the pre-havoc reassignment, so a rely
  reads `R($old_heap, $heap)`.

The final `snapshot $old_heap` makes the next step's guarantee `old` refer to
this resume point. `HeapParameterization` lowers `oldGuarantee`/`oldRelies` (both
emitted here as a labeled `Old (some $old_heap)`) against `$old_heap` and
declares the local, seeding it to procedure-entry `$heap`.

### Pipeline placement

Runs **before** `heapParameterizationPass`: it never mentions `$heap` directly,
emitting `Snapshot`/labeled `Old`/`havocHeap()` for heap-param to lower.
Resolution is disabled after this pass, so those artifacts reach heap-param
untouched; the `havocHeap()` call reuses the preamble's resolved identifier.
-/

/-! ### Identifiers and shapes -/

/-- The single procedure-level heap snapshot. Reassigned mid-yield so one
    variable serves both `old` roles: at the guarantee-assert it holds the
    start-of-step heap; the yield block then reassigns it to the pre-havoc heap
    for the rely-assume, then to the post-havoc heap (= next step's start). This
    is a body-local; `HeapParameterization` declares it as a `Heap` seeded to the
    entry `$heap` (see `snapshotLocalDecls`). -/
private def oldHeapName : Identifier := "$old_heap"

/-- The `$havocHeap()` preamble procedure (declared `opaque modifies *` in
    `CoreDefinitionsForLaurel`). The body path emits calls to it to model an
    environment heap step, and `HeapParameterization` threads its `$heap` inout. -/
def havocHeapName : Identifier := "$havocHeap"

/-! ### Tag-aware substitution

Both coroutine two-state `old` forms — `oldGuarantee(e)` (start-of-step, for
guarantees) and `oldRelies(e)` (pre-havoc, for relies) — read the same snapshot
local `$old_heap`; the yield block's reassignment ordering gives each its
intended heap at the point it is read. Both lower to `Old e (some $old_heap)`,
which `HeapParameterization` evaluates against `$old_heap`. A plain `Old` (no
label) is left intact (Core provides its two-state binding). -/

/-- Lower a `OldGuarantee`/`OldRelies` node to a labeled `Old inner (some $old_heap)`. -/
private def substTaggedOldNode (n : StmtExprMd) : StmtExprMd :=
  match n.val with
  | .OldGuarantee inner | .OldRelies inner => { n with val := .Old inner (some oldHeapName) }
  | _ => n

/-- Walk an expression and lower every `OldGuarantee`/`OldRelies` to a labeled
    `Old (some $old_heap)` read. -/
private def substTaggedOlds (e : StmtExprMd) : StmtExprMd :=
  mapStmtExpr substTaggedOldNode e

-- User-written `old(...)` inside a `guarantees` / `relies` clause is retagged
-- to the coroutine-specific `OldGuarantee` / `OldRelies` form (so it gets the
-- correct per-yield two-state meaning without the user spelling out
-- `oldGuarantee` / `oldRelies`). The shared `retagOldAs` lives in `MapStmtExpr`
-- (used identically by `CoroutineElaboration`); use it as
-- `retagOldAs .OldGuarantee` / `retagOldAs .OldRelies`.

/-- Resolved preamble identifiers this pass reuses when synthesizing calls. With
    resolution disabled after this pass, emitted `StaticCall`s must carry an
    already-resolved callee (uniqueId included) so heap-param's heap-effect lookup
    does not fail on an unresolved name. -/
private structure ResolvedOps where
  /-- `$havocHeap` — the environment-step havoc (see `havocCall`). -/
  havocHeap : Identifier
  /-- `$and(bool,bool)` — conjoins multiple guarantee/rely clauses (see `conjoin`). -/
  andOp : Identifier

/-- Conjoin a list of Conditions into a single boolean expression. Empty
    list ⇒ `true`. Singleton ⇒ the lone condition. Otherwise a left-fold
    over the resolved `$and`. -/
private def conjoin (andOp : Identifier) (conds : List Condition) (src : FileRange) : StmtExprMd :=
  match conds with
  | [] => { val := .LiteralBool true, source := src }
  | c :: rest =>
    rest.foldl
      (fun acc nxt =>
        { val := .StaticCall andOp [acc, nxt.condition], source := src })
      c.condition

private def mkAssert (cond : StmtExprMd) (summary : Option String) (src : FileRange) : StmtExprMd :=
  { val := .Assert cond summary, source := src }

private def mkAssume (cond : StmtExprMd) (src : FileRange) : StmtExprMd :=
  { val := .Assume cond, source := src }

/-- A `Snapshot $old_heap` statement (heap-param lowers it to `$old_heap := $heap`). -/
private def takeSnapshot (src : FileRange) : StmtExprMd :=
  { val := .Snapshot oldHeapName, source := src }

/-- A `$havocHeap()` call statement. `havocHeap` carries the resolved preamble
    identifier (uniqueId included) so heap-param recognizes it as a heap writer
    without a re-resolution — resolution is disabled after this pass. -/
private def havocCall (havocHeap : Identifier) (src : FileRange) : StmtExprMd :=
  { val := .StaticCall havocHeap [], source := src }

/-! ### Value-channel bindings

A coroutine's `yields (x: T)` / `resumes (y: U)` bindings are in scope only while
Resolution treats the procedure as a coroutine. `yieldElimProc` demotes the
`$body` copy to a regular procedure, so those bindings must be re-introduced as
ordinary body locals or they dangle (the later re-resolution reports `x`/`y`
"is not defined"). They stay *scalar* locals — not composite/heap state — so the
verify path remains pure YieldElim (no `elaborateForVerification` state machine):

* A `yields (x)` binding is the coroutine's own output. The body writes it before
  every `yield`, the caller only reads it, so it persists across a step untouched;
  one declaration at body entry suffices.
* A `resumes (y)` binding is a fresh caller-supplied value at every resume, so it
  is re-havoced inside each yield step (below), and its entry declaration havocs
  the first resume's value. Nothing constrains it: a `rely` is a two-state *heap*
  relation `R($old_heap, $heap)`, so the body must hold for *every* resumed value.
  The havoc sits right after the environment `havocHeap()` and before the rely is
  assumed, so a rely that does mention the binding reads the fresh value rather
  than the previous step's. -/

/-- `var <p>: <T> := havoc` — an initialized declaration whose right-hand side is
    a nondeterministic hole, so the binding starts with an unconstrained value.
    Uses the binding's own identifier (uniqueId included) so uses in the body
    still bind to it. -/
private def channelDecl (p : Parameter) : StmtExprMd :=
  let src := p.name.source
  let target : AstNode Variable :=
    { val := .Declare { name := p.name, type := some p.type }, source := src }
  let havoc : StmtExprMd := { val := .Hole (deterministic := false) (some p.type), source := src }
  { val := .Assign [target] havoc, source := src }

/-- `<y> := havoc` — re-havoc a `resumes` binding to a fresh caller-supplied
    value. Emitted inside each yield step (after `havocHeap()`, before the rely
    assume). -/
private def resumeHavoc (p : Parameter) (src : FileRange) : StmtExprMd :=
  { val := .Assign [{ val := .Local p.name, source := src }]
      { val := .Hole (deterministic := false) (some p.type), source := src }, source := src }

/-- Build the inline replacement for a single `yield`:
    `assert ⋀G; snapshot $old_heap; havocHeap(); assume ⋀R; snapshot $old_heap`.

    On entry `$old_heap` holds the start-of-step heap (procedure entry, or the
    previous yield's post-havoc snapshot), so `assert ⋀G` — with each
    `oldGuarantee` reading `$old_heap` — is a two-state guarantee over the step.
    Then:

    * snapshot `$old_heap := $heap` (pre-havoc) so a rely's `oldRelies` reads the
      heap right before the environment acted;
    * `havocHeap()` — the environment step (its `modifies *` havocs `$heap`, and
      its monotonic-counter postcondition keeps allocation monotone across it);
    * `assume ⋀R` — each `oldRelies` reads pre-havoc `$old_heap`, the rest reads
      the live post-havoc `$heap`, so a rely reads `R($old_heap, $heap)`;
    * snapshot `$old_heap := $heap` again so the *next* step's guarantee `old`
      refers to this resume point.

    A `resumes` binding is re-havoced between the heap step and the rely assume,
    so no stale channel value is in scope where the rely is assumed (see the
    value-channel note above).

    Empty G/R lists skip the corresponding assert/assume — no `assert true`
    noise, and no `assume true` that would silently satisfy a missing rely. The
    snapshots + havoc still emit: that per-yield framing holds regardless. -/
private def yieldRewrite (ops : ResolvedOps) (relies guarantees : List Condition)
    (resumes : List Parameter) (src : FileRange) : StmtExprMd :=
  let assertGStmt? : Option StmtExprMd :=
    if guarantees.isEmpty then none else
      some (mkAssert
        (substTaggedOlds (conjoin ops.andOp guarantees src))
        (some "coroutine yield: guarantee")
        src)
  let assumeRStmt? : Option StmtExprMd :=
    if relies.isEmpty then none else
      some (mkAssume (substTaggedOlds (conjoin ops.andOp relies src)) src)
  let havocResumes : List StmtExprMd := resumes.map (resumeHavoc · src)
  let stmts : List StmtExprMd :=
    assertGStmt?.toList
      ++ [takeSnapshot src, havocCall ops.havocHeap src]
      ++ havocResumes
      ++ assumeRStmt?.toList
      ++ [takeSnapshot src]
  { val := .Block stmts none, source := src }

/-! ### Procedure rewrite

No auto-injection of guarantees at loop heads. The user writes loop invariants
explicitly using the surface form `oldGuarantee(...)`, which this pass lowers to
a labeled `Old (some $old_heap)` read via `substTaggedOlds`. See
`LoopUserInvariants` for examples. -/

/-- Walk the body once. At each `.Yield` emit the inline rewrite block;
    everywhere else, lower any user-written `oldGuarantee(...)` / `oldRelies(...)`
    to a labeled `Old (some $old_heap)` read (covers loop invariants, body asserts /
    assumes). The `relies`/`guarantees` are retagged but otherwise unmodified;
    `substTaggedOlds` inside `yieldRewrite` does the snapshot lowering. -/
private def rewriteYields (ops : ResolvedOps) (relies guarantees : List Condition)
    (resumes : List Parameter) (impl : StmtExprMd) : StmtExprMd :=
  mapStmtExpr
    (fun e =>
      match e.val with
      | .Yield => yieldRewrite ops relies guarantees resumes e.source
      | _ => substTaggedOlds e)
    impl

/-! ### Exit guarantee

The per-yield asserts cover each `resume → yield` step but not the final
`resume → halt` segment. That segment is still observed by the caller: the
generated opaque `resume` carries `G` as an unguarded postcondition, so without
an exit assert a coroutine could honor `G` at every yield, break it after the
last one, and have the caller assume it anyway. `old(...)` at exit reads
`$old_heap` = the last yield's post-havoc snapshot, i.e. the start of the final
segment. -/

/-- `assert ⋀guarantees` for a body exit, `oldGuarantee` reading `$old_heap`.
    `none` when no guarantees were declared.

    Localized to the first `guarantees` clause rather than the exit site: an
    exit has no keyword of its own (the fall-through is the closing brace), so
    the violated clause is the more useful place to point. -/
private def exitGuaranteeAssert (andOp : Identifier) (guarantees : List Condition) : Option StmtExprMd :=
  match guarantees with
  | [] => none
  | g :: _ =>
    -- Localize the assert to the first guarantee clause, which carries its own
    -- source, rather than to the (keyword-less) exit site.
    let gsrc := g.condition.source
    some (mkAssert
      (substTaggedOlds (conjoin andOp guarantees gsrc))
      (some "coroutine exit: guarantee")
      gsrc)

/-- Assert the guarantee on every path out of the body: before each `return`
    and at the body's end. Runs after `rewriteYields`; the emitted assert is
    already substituted, so guarantees are not walked twice. -/
private def addExitGuarantees (andOp : Identifier) (guarantees : List Condition)
    (impl : StmtExprMd) : StmtExprMd :=
  if guarantees.isEmpty then impl else
  let withReturns := mapStmtExpr (fun e =>
    match e.val with
    | .Return _ =>
      match exitGuaranteeAssert andOp guarantees with
      | some a => { val := .Block [a, e] none, source := e.source }
      | none => e
    | _ => e) impl
  match exitGuaranteeAssert andOp guarantees with
  | none => withReturns
  | some a =>
    match withReturns.val with
    | .Block stmts label =>
      { val := .Block (stmts ++ [a]) label, source := withReturns.source }
    | _ =>
      { val := .Block [withReturns, a] none, source := withReturns.source }

/-- Transform a single coroutine into a regular procedure.
    Inside the body, every `yield` is rewritten to the inline
    assert/havoc/assume block. The `$old_heap` snapshot local is declared and
    seeded to the entry heap by `HeapParameterization` (`Heap` does not exist
    yet at this pass), keyed off the `Snapshot`/labeled-`Old` nodes emitted
    here.

    The user-written `relies` / `guarantees` only fire at yield sites
    (where the rely/guarantee rule applies); they are **not** merged
    into the procedure's `preconditions` or halt-`ensures`. Two reasons:

    * **Entry rely.** At procedure entry no environment step has
      happened yet, so the rely isn't an obligation on the caller — it
      would just be a free fact about the initial heap. Worse, the rely
      typically mentions `old($heap)`, which has no meaning at entry
      (there is no prior state) and would survive into ContractPass-
      generated `peterson$preN` helper functions, where `$heap` is an
      input-only parameter — translating that `old($heap)` triggers
      LaurelToCore's "not an inout" StrataBug check.

    * **Final guarantee.** The guarantee's `old($heap)` is meant to
      refer to the start of the *current step*, i.e. the last
      `$old_heap` — a body-local. That local isn't in scope in the
      `ensures` clause, so we can't lift the guarantee verbatim. The
      user's `ensures Q_final` is the right place for whole-coroutine
      facts. The guarantee is instead asserted at each yield and at every
      body exit (`addExitGuarantees`), covering the final
      `resume → halt` segment. -/
private def yieldElimProc (ops : ResolvedOps) (proc : Procedure) : Procedure :=
  -- Retag every `Old(e)` in the user's clauses to the coroutine-specific
  -- two-state form: `guarantees` → `OldGuarantee(e)` (start-of-step heap),
  -- `relies` → `OldRelies(e)` (pre-havoc heap). Implicit retagging means
  -- the user keeps writing plain `old(s#x)` in either position and the pass
  -- gives it the right per-yield meaning automatically.
  let reliesTagged := proc.relies.map (·.mapCondition (retagOldAs .OldRelies))
  let guarsTagged := proc.guarantees.map (·.mapCondition (retagOldAs .OldGuarantee))
  match proc.body with
  | .Opaque haltPosts (some impl) modif =>
    let impl' := rewriteYields ops reliesTagged guarsTagged proc.resumes impl
    let body' := addExitGuarantees ops.andOp guarsTagged impl'
    -- Re-introduce the `yields` / `resumes` bindings as body locals: Resolution
    -- scoped them only while this was a coroutine, and demoting to `.Regular`
    -- (below) drops that scope, so uses in the (now regular) body would dangle.
    -- They are scalar locals, not composite state — the verify path stays pure
    -- YieldElim (see the value-channel note above).
    let channelDecls : List StmtExprMd := (proc.yields ++ proc.resumes).map channelDecl
    let bodyWithChannels := prependStmts channelDecls body'
    { proc with
      contracts := .Regular
      body := .Opaque haltPosts (some bodyWithChannels) modif }
  | body =>
    -- Bodyless coroutine (abstract / external / transparent / no impl).
    -- Nothing to rewrite; just clear the coroutine-only clauses so this
    -- becomes a regular procedure under Resolution's invariants.
    { proc with
      contracts := .Regular
      body := body }

/-! ### Scheduler-side `Resume` / `HasNext` diagnostics -/

private def collectResumeHasNextDiags (proc : Procedure) : List Message :=
  let report (e : StmtExprMd) : List Message :=
    match e.val with
    | .Resume _ _ => [diagnosticFromSource e.source
        "scheduler-side `resume(...)` is not supported currently with `verifyCoroutine := true`"
        MessageKind.userError]
    | .HasNext _ => [diagnosticFromSource e.source
        "scheduler-side `has_next(...)` is not supported currently with `verifyCoroutine := true`"
        MessageKind.userError]
    | _ => []
  let walk (body : StmtExprMd) : List Message :=
    let acc : StateM (List Message) StmtExprMd :=
      mapStmtExprM (fun e => do modify (· ++ report e); pure e) body
    (acc.run []).2
  match proc.body with
  | .Transparent b => walk b
  | .Opaque _ (some impl) _ => walk impl
  | _ => []

/-! ### Body-path entry point -/

def runYieldElimBody (program : Program) : Program × List Message :=
  -- Reuse resolved preamble identifiers (uniqueIds included) for the calls this
  -- pass synthesizes: `$havocHeap` (env step) and `$and` (clause conjunction).
  -- Resolution is off after this pass, so heap-param's heap-effect lookup must
  -- see already-resolved callees. Fall back to bare names if the preamble proc is
  -- absent — only when there is no coroutine to rewrite, so it is never used.
  -- `$and` is bool-only (arithmetic uses `$add`), so the first match is right.
  let findId (name : String) (fallback : Identifier) : Identifier :=
    (program.staticProcedures.find? (·.name.text == name)).map (·.name) |>.getD fallback
  let ops : ResolvedOps :=
    { havocHeap := findId havocHeapName.text havocHeapName
      andOp := findId Operation.And.procName (mkId Operation.And.procName) }
  let rewritten : List Procedure := program.staticProcedures.map fun proc =>
    if proc.is_coroutine then yieldElimProc ops proc else proc
  let diags : List Message :=
    program.staticProcedures.filter (fun p => !p.is_coroutine)
      |>.flatMap collectResumeHasNextDiags
  ({ program with staticProcedures := rewritten }, diags)

/-! ## Coroutine rely-heap threading (caller path)

Runs on the lifted `resume` procedure a coroutine lowers to. A two-state
coroutine contract relates three heaps:

* `H1` — the heap at the coroutine's most recent suspension,
* `H2` — the heap when `resume` is (re-)entered,
* `H3` — the heap when `resume` next returns.

`resume` writes the heap, so heap-parameterization gives it an inout `$heap`
(entry = `H2`, exit = `H3`). `H1` is the one heap `resume` cannot see natively;
the caller tracks it per instance and passes it in. This adds that extra input
`$h_rely_old : Heap` and lowers the two coroutine `old` forms — but since `$heap`
does not exist yet, it emits the generic snapshot forms for heap-parameterization
to lower:

* `oldRelies(e)` (`H1`, in a rely → precondition) ⟶ `Old e (some $h_rely_old)`,
  which heap-param evaluates against the snapshot heap. No Core `old` — relies
  are preconditions, where `old` is not allowed.
* `oldGuarantees(e)` (`H2`, in a guarantee → postcondition) ⟶ `old(e)`, which
  `pushOldInward` distributes onto the inout `$heap`, giving `resume`'s native
  two-state entry heap.

The caller-side `$h1_co` snapshot is emitted as `Snapshot $h1_co`; heap-param
declares the `Heap` local and lowers it to `$h1_co := $heap`.

Unlike the body path, this runs regardless of `verifyCoroutine`: the non-verify
elaboration path also produces `resume` procedures carrying these markers, and
this is the only pass that lowers them. -/

/-- The extra input heap holding `H1` (the last-suspension snapshot). -/
def relyOldHeapName : Identifier := "$h_rely_old"

private def containsOldRelies (e : StmtExprMd) : Bool :=
  anyStmtExpr (fun n => match n.val with | .OldRelies _ => true | _ => false) e

/-- Lower `oldRelies`/`oldGuarantees` at a single node (bottom-up).
    `oldRelies(e)` reads the H1 snapshot heap `$h_rely_old` — emitted as a
    labeled `Old e (some $h_rely_old)` for `HeapParameterization` to evaluate
    against that param (this runs before `$heap` exists, so it cannot substitute
    `$heap` directly). `oldGuarantees(e)` is the resume's native entry state, so
    it becomes a plain `Old e` (no label) that push-old later distributes onto
    `$heap`. -/
private def lowerNode (n : StmtExprMd) : StmtExprMd :=
  match n.val with
  | .OldRelies inner => { n with val := .Old inner (some relyOldHeapName) }
  | .OldGuarantee inner => { n with val := .Old inner none }
  | _ => n

/-- Whether the H1 param is needed: some precondition mentions `oldRelies`.
    Checked before lowering, since lowering erases the `OldRelies` marker. -/
private def needsRelyOldHeap (proc : Procedure) : Bool :=
  proc.preconditions.any (containsOldRelies ·.condition)

private def heapTy : HighTypeMd := ⟨.UserDefined heapTypeName, .unknown⟩

/-- `$h1_<co>` — the caller's per-instance snapshot of the last-suspension heap. -/
private def instH1Name (co : Identifier) : Identifier := mkId s!"$h1_{co.text}"

/-- `Snapshot $h1_co` — records the current heap as `co`'s H1 (heap-param
    lowers it to `$h1_co := $heap`). -/
private def snapshotH1 (co : Identifier) : StmtExprMd :=
  ⟨.Snapshot (instH1Name co), .unknown⟩

/-! ### Phase 1 — transform each `resume` procedure

Lower its `oldRelies`/`oldGuarantees` and, when it references `oldRelies`, add
the extra `$h_rely_old : Heap` input. -/

private def transformResumeProc (proc : Procedure) : Procedure :=
  let needsH1 := needsRelyOldHeap proc
  let lowered := mapProcedureM (m := Id) (fun e => mapStmtExpr lowerNode e) proc
  if needsH1 then
    { lowered with inputs := lowered.inputs ++ [{ name := relyOldHeapName, type := heapTy }] }
  else lowered

/-! ### Tracking H1 (OldRelies) through callers

The caller tracks three heaps per resumed coroutine instance `co`:

* `H1` — the heap at `co`'s previous suspension, carried in the caller-local
  `$h1_co` (`OldRelies`, the rely's `old`);
* `H2` — the heap on resume entry (`$heap` when the resume is called;
  `OldGuarantee`, the guarantee's `old`);
* `H3` — the heap on resume exit (`$heap` after the resume returns).

This runs **before** heap parameterization, so a resume call is the lifted
static call `<resume>(co, …)` with the receiver `co` as `args[0]` (heap-param
later prepends `$heap`, making it `<resume>($heap, co, …)`). For a resume that
takes `$h_rely_old`, we append `$h1_co` (H1) as the final argument; heap-param's
`$heap` prepend keeps every argument's relative order, so `$h1_co` still lines up
with the `$h_rely_old` parameter. The opaque resume encodes one rely/guarantee
step: precondition `R($h_rely_old, $heap)` = `assert R(H1, H2)`, havoc-`modifies`
produces H3, postcondition `G(old $heap, $heap)` = `assume G(H2, H3)`. After the
call we `Snapshot $h1_co` to set H1 := H3 for the next resume.

`$h1_co` is a snapshot local seeded **at `co`'s own declaration site** (the spawn
`var co := <coro>(…)`) via `Snapshot $h1_co`; heap-param declares it as a
`Heap` local and lowers the snapshot to `$h1_co := $heap`. Seeding to the spawn
heap makes H1 at the first resume the heap at `co`'s creation: with no
intervening mutation `R(H1, H2)` is reflexive; with mutation the rely correctly
constrains the change since creation. -/

/-- The receiver instance of a pre-heap-param resume call `f(co, …)` (argument 0),
    if it is a plain local. -/
private def resumeReceiver (args : List StmtExprMd) : Option Identifier :=
  match args[0]? with
  | some arg =>
    match arg.val with
    | .Var (.Local co) => some co
    | _ => none
  | none => none

/-- The receiver of a resume call `f(co, …)`, if `e` is precisely such a call to a
    resume in `h1Resumes`. Pairs the parse with the receiver lookup so the
    diagnostics below and `threadCallerNode` agree on what counts as a resume
    site. A statement-position resume is a bare `StaticCall` (heap-param has not
    yet wrapped it in a `$heap := …` assignment). -/
private def resumeCallReceiver (h1Resumes : Std.HashSet String)
    (e : StmtExprMd) : Option (Option Identifier) :=
  match e.val with
  | .StaticCall callee args =>
    if h1Resumes.contains callee.text then some (resumeReceiver args) else none
  | _ => none

/-- Every coroutine variable resumed anywhere in `body` through a resume in
    `h1Resumes`. The `$h1_<co>` snapshot local is declared at each such
    variable's declaration site so it dominates all of that variable's resumes,
    regardless of control flow (branches, loops). -/
private def resumedReceiverNames (h1Resumes : Std.HashSet String)
    (body : StmtExprMd) : Std.HashSet String :=
  foldStmtExpr (fun n acc =>
    match resumeCallReceiver h1Resumes n with
    | some (some co) => acc.insert co.text
    | _ => acc) ∅ body

/-- Diagnostic for a resume site this pass cannot thread `$h_rely_old` through:
    the receiver is not a simple variable, so there is no per-instance `$h1_co`
    to track. `resume(self#co)` / `resume(f())` gives an `args[1]` that is not a
    `.Var (.Local _)`; threading is skipped and would otherwise surface as an
    arity mismatch at the generated resume, so we report it here instead. -/
private def resumeThreadingDiags (h1Resumes : Std.HashSet String)
    (body : StmtExprMd) : List Message :=
  foldStmtExpr (fun n acc =>
    match resumeCallReceiver h1Resumes n with
    | some none => acc ++ [diagnosticFromSource n.source
        "coroutine `resume` receiver is not a simple variable; under verifyCoroutine the caller must track a per-instance rely-old heap snapshot per coroutine variable, which requires the resumed instance to be a plain local. Bind the coroutine to a local variable and resume that."
        MessageKind.userError]
    | _ => acc) [] body

/-- The body expression(s) to scan / rewrite for a procedure. -/
private def procResumeBodies (proc : Procedure) : List StmtExprMd :=
  match proc.body with
  | .Transparent b => [b]
  | .Opaque _ (some impl) _ => [impl]
  | _ => []

/-- Rewrite one node while threading H1. Runs before heap parameterization, so a
    resume is a bare `StaticCall f(co, …)` and a spawn is `var co := <coro>(…)`.

    * A resume call `f(co, …)` gets the caller's `$h1_co` appended as the final
      argument (H1), followed by `Snapshot $h1_co` to record H3 for the next
      resume. `$h1_co` is in scope — it is seeded at `co`'s declaration (below),
      which dominates every resume of `co`.
    * A declaration of a coroutine variable `co` resumed somewhere in this body
      (`co ∈ resumed`) is followed by `Snapshot $h1_co`, seeding H1 to the
      spawn heap. Handles both the initialized spawn `var co := <coro>(…)` and a
      bare `var co`. Heap-param declares each `$h1_co` and lowers its snapshots. -/
private def threadCallerNode (h1Resumes : Std.HashSet String)
    (resumed : Std.HashSet String) (used : Bool) (e : StmtExprMd)
    : List StmtExprMd :=
  -- Seed `Snapshot $h1_co` after any declaration of a resumed `co`.
  let seedsFor (targets : List (AstNode Variable)) : List StmtExprMd :=
    targets.filterMap fun t =>
      match t.val with
      | .Declare ⟨name, _⟩ => if resumed.contains name.text then some (snapshotH1 name) else none
      | _ => none
  match e.val with
  -- Only statement-position resumes (`used = false`) are threaded: the follow-up
  -- `Snapshot` must be a sibling statement, which the flatten traversal only
  -- splices in statement position. Expression-position `z := resume(co)` under
  -- `verifyCoroutine` is not supported (no test exercises it); left untouched, it
  -- surfaces as an arity mismatch against the H1-taking resume.
  | .StaticCall callee args =>
    if !used && h1Resumes.contains callee.text then
      match resumeReceiver args with
      | some co =>
        let h1Read : StmtExprMd := ⟨.Var (.Local (instH1Name co)), .unknown⟩
        let threaded : StmtExprMd := { e with val := .StaticCall callee (args ++ [h1Read]) }
        [threaded, snapshotH1 co]
      | none => [e]
    else [e]
  | .Assign targets _ =>
    -- A spawn `var co := <coro>(…)` whose `.Declare co` needs the `$h1_co` seed.
    e :: seedsFor targets
  | .Var (.Declare ⟨name, _⟩) =>
    if resumed.contains name.text then [e, snapshotH1 name] else [e]
  | _ => [e]

private def threadCallerBody (h1Resumes : Std.HashSet String) (body : StmtExprMd) : StmtExprMd :=
  let resumed := resumedReceiverNames h1Resumes body
  mapStmtExprFlattenM (m := Id) (fun _ _ => none)
    (fun used e => threadCallerNode h1Resumes resumed used e) false body

/-! ### Caller-path entry point -/

def coroutineRelyHeap (program : Program) : Program × List Message :=
  -- Phase 1: transform resume procedures, collecting those that gained an H1
  -- input. The body-path rewrite already ran (lowering coroutine `$body` copies
  -- to regular procedures), so no `is_coroutine` procs remain; the generated
  -- `resume` procedures carry the `OldRelies`/`OldGuarantee` markers this lowers.
  let procs := program.staticProcedures.map transformResumeProc
  let h1Resumes : Std.HashSet String :=
    program.staticProcedures.foldl (init := ∅) fun names proc =>
      if needsRelyOldHeap proc then names.insert proc.name.text else names
  let program := { program with staticProcedures := procs }
  -- No resume takes an H1 parameter — the common case, since a program without
  -- coroutines has no resume at all. Both steps below are then identity
  -- (`resumed` is empty, so nothing is threaded, seeded or diagnosed), so skip
  -- their whole-program traversals.
  if h1Resumes.isEmpty then (program, []) else
  -- Diagnostics for resume sites we cannot thread `$h_rely_old` through
  -- soundly (a non-local receiver, which has no per-instance `$h1_co` local).
  -- Collected across every procedure body before threading.
  let diags : List Message :=
    program.staticProcedures.flatMap fun proc =>
      (procResumeBodies proc).flatMap (resumeThreadingDiags h1Resumes ·)
  -- Phase 2: thread H1 through every caller body.
  let program := mapProgramProcedures (fun proc =>
    mapProcedureBodiesM (m := Id) (threadCallerBody h1Resumes) proc) program
  (program, diags)

/-- Pipeline pass: lower coroutine `old`-semantics on both the body and caller
    paths (see the module docstring).

    * **Body path** (only under `verifyCoroutine`): rewrites every `yield` to an
      inline `assert ⋀G; Snapshot $old_heap; havocHeap(); assume ⋀R; Snapshot
      $old_heap` block. The single reassigned `$old_heap` snapshot gives the
      user's `old($heap)` the correct per-yield meaning via a labeled `Old`; the
      `relies`/`guarantees` fire only at yield sites.
    * **Caller path** (always): threads the per-instance `$h_rely_old` (H1)
      snapshot heap through `resume` procedures and their callers, lowering
      `oldRelies`/`oldGuarantees`.

    Runs before HeapParameterization (so it never touches `$heap` directly) and
    with resolution disabled after it — the emitted `Snapshot`/labeled-`Old`
    and `havocHeap()` are consumed by HeapParameterization untouched.

    Scheduler-side `resume(...)` / `has_next(...)` outside coroutine bodies are
    not supported currently - this will be implemented in the next step. -/
public def yieldElimPass : LoweringPass where
  name := "YieldElim"
  documentation := "Lowers coroutine old-semantics. Body path (verifyCoroutine only): replaces every `yield` with an inline `assert ⋀guarantees; Snapshot $old_heap; havocHeap(); assume ⋀relies; Snapshot $old_heap` block. Caller path (always): threads the per-instance $h_rely_old (H1) snapshot heap through resume procedures and callers. Both lower `oldGuarantee`/`oldRelies` to labeled `Old` / `Snapshot` for HeapParameterization to consume (declaring the snapshot locals and threading $heap); resolution is disabled after this pass."
  needsResolves := false
  run := fun options p _ =>
    -- Body path is verify-only; the caller path (resume/caller lowering) always
    -- runs, since the non-verify elaboration path also emits the markers it lowers.
    let (p, bodyDiags) := if options.verifyCoroutine then runYieldElimBody p else (p, [])
    let (p, callerDiags) := coroutineRelyHeap p
    (p, bodyDiags ++ callerDiags, {})
  comesAfter := [⟨ liftInstanceProceduresPass.meta, "caller-path resume calls must already be lifted static calls `<resume>(co, …)` before threading H1." ⟩]
  comesBefore := [⟨ heapParameterizationPass.meta, "Emits Snapshot/labeled-Old/havocHeap() that HeapParameterization lowers (declaring the snapshot locals and threading $heap)." ⟩]

end Strata.Laurel
end
