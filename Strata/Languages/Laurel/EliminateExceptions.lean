/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Laurel.LaurelAST
public import Strata.Languages.Laurel.LaurelPass
public import Strata.Languages.Laurel.SemanticModel
import Strata.Languages.Laurel.MapStmtExpr
import Strata.Languages.Laurel.HeapParameterization
import Strata.Languages.Laurel.ModifiesClauses
import Strata.Languages.Laurel.CoreDefinitionsForLaurel
-- Imported for their pass metadata only, to declare this pass's ordering
-- constraints (see `comesBefore`/`comesAfter` on `eliminateExceptionsPass`).
import Strata.Languages.Laurel.EliminateValueInReturns
import Strata.Languages.Laurel.EliminateReturnStatements
import Strata.Languages.Laurel.ContractPass
import Strata.Util.Tactics

/-!
# Eliminate Exceptions

A Laurel-to-Laurel pass that lowers the exceptional channel — `throw`, `try` /
`catch` / `finally`, and the `throws` / `throwsOn` procedure
contract — into ordinary Laurel (labeled `Block`s, `Exit`s, assignments, and
`Result` datatype construction). After this pass no `Throw`/`Try` statements and
no `throwsType`/a `throwsOn` case's guard and postconditions clauses remain, so the final
`LaurelToCoreTranslator` never needs to know about exceptions.

The encoding lives here, one level above the translator, so the transformation is
reviewable as Laurel before/after (see the `EliminateExceptions` reviewability
test) rather than being buried in the Core translation.

## Encoding

A procedure that declares `throws T` returns a single `Result<Val, T>` output
(`$result`), where `T` is the declared `throws` type. While the body runs, the
in-flight exception is tracked by `$thrown : bool` and a per-`try` local
`$exc_<i>` typed at that `try`'s least-common-ancestor exception type (read from
the resolved `catch` binding). A `try` with no `catch` (finally-only) and the
procedure top level reuse the enclosing region's `$exc`; for a `throws T`
procedure the top-level one is `$exc : T`. `$returning` tracks a `return`
unwinding out of enclosing `try` blocks so their `finally` arms run, and
`$exiting_<l>` does the same for an `exit <l>` whose target label lies outside an
enclosing `try`. All synthesized names are `$`-prefixed, outside the user
namespace.

Because each `$exc_<i>` is typed at the `try`'s LCA, a `catch` handler's
`e#field` type-checks against that supertype with no downcast. Propagating an
exception out of a `try` into an enclosing region whose `$exc` is a *narrower*
type inserts an assumed checked downcast (`assume e is T; … as T`) — sound
because resolution's escape/residual analysis already proved only types `<: T`
escape.

- `throw v`  →  `$exc := v; $thrown := true; exit <nearest try | $exnexit>`.
- `try B catch eᵢ when Pᵢ { Hᵢ } … finally { F }`  →  two nested labeled blocks
  `block $tryfin { block $try { B } <catch chain> } F <re-dispatch>` so `finally`
  runs on every exit edge (the catch binding is substituted by `$exc`).
- `exit l` leaving a `try` with a `finally`  →  `$exiting_l := true; exit $tryfin`,
  and the re-dispatch after that `finally` either continues the unwind (to the
  next crossed `finally`) or delivers the jump (`$exiting_l := false; exit l`).
  An `exit` that stays inside every enclosing `finally` region is left alone.
- a call to a `throws` procedure  →  bind its `Result` to a temp, then `if
  isBad(tmp) then propagate else unwrap value(tmp)`.
- the body is wrapped in `block $exnexit { … }`; after it, `$result` is built
  (`Bad($exc)` if thrown, else `Good(val)`).
- `ensures P`  →  Good-path `isGood($result) ==> P[out := value($result)]`;
  each `throwsOn C { … }` case  →  `C ==> isBad($result)` plus, per `ensures P`,
  `C ∧ isBad($result) ==> P[e := err($result)]`.

Runs *before* heap parameterization (so `$exc_<i>` can be typed at a real
exception type rather than the erased heap `Composite`) and needs a re-resolve
so the synthesized locals get uniqueIds. The heap `modifies` frames — the normal
`Result..isGood`-guarded frame and the exceptional `Result..isBad`-guarded
cases' frames — are left to `ModifiesClauses`, which runs after heap
parameterization where `$heap` exists; this pass keeps `throwsOn` on the
procedure for it to consume.
-/

namespace Strata.Laurel

/-! ### Synthesized names -/

/-- Synthesized local: `true` once an exception is in flight. -/
private def exnThrownVar : String := "$thrown"
/-- Synthesized local: the procedure-level in-flight exception value (typed at
    the declared `throws` type). Per-`try` locals are `$exc_<i>`. -/
private def exnExcVar : String := "$exc"
/-- Synthesized local: `true` once a `return` is unwinding through
    enclosing `try` blocks so their `finally` arms run. -/
private def exnReturningVar : String := "$returning"
/-- Synthesized local: `true` once an `exit <label>` is unwinding through
    enclosing `try` blocks so their `finally` arms run. One flag per target label
    (an `exit` carries no value, so a bool per label is all the unwind needs);
    cleared when the jump is finally delivered to its label. -/
private def exitPendingVar (label : String) : String := s!"$exiting_{label}"
/-- Preferred spelling for a throwing procedure's synthesized output — the
    `Result<Val, T>` carrying its outcome. `resultOutputName` because after the
    lowering the carrier *is* the procedure's result (its only output), and a
    single output of this name prints in the familiar short form.

    A preference only, never load-bearing: `lowerProc` freshens it against every
    identifier the procedure binds (so a short-form procedure, whose own value
    output already takes this name, gets `$result_1`), and every reference to the
    carrier — the `isGood`/`isBad` guards on postconditions and modifies groups —
    is emitted by this pass at the point it mints the name. Correctness cannot
    depend on this spelling — nothing downstream recognizes the carrier at all. -/
private def exnResultVar : String := resultOutputName

/-- The identifiers `proc` binds where a carrier collision could bite: inputs,
    outputs, and every name bound in its body and postconditions — declarations,
    `.Assign` targets, `catch` bindings, and quantifier binders. Binders open
    nested scopes, but the carrier is referenced from postconditions that a
    substitution may land inside (an authored `forall($result: …)` would capture
    a carrier spelled `$result`), so scoping is ignored rather than modelled:
    every bound name is treated as taken. Used to choose a carrier name that
    collides with nothing it collects. -/
private def usedNames (proc : Procedure) : Std.HashSet String :=
  let fromBody (b : StmtExprMd) (acc : Std.HashSet String) : Std.HashSet String :=
    foldStmtExpr (fun n acc =>
      match n.val with
      | .Var (.Declare p) => acc.insert p.name.text
      | .Assign targets _ =>
        targets.foldl (fun acc t =>
          match t.val with
          | .Declare p => acc.insert p.name.text
          | .Local id => acc.insert id.text
          | .Field _ _ => acc) acc
      | .Try _ catches _ =>
        catches.foldl (fun acc c => acc.insert c.binding.text) acc
      | .Quantifier _ param _ _ => acc.insert param.name.text
      | _ => acc) acc b
  let acc := (proc.inputs ++ proc.outputs).foldl
    (fun (acc : Std.HashSet String) p => acc.insert p.name.text) {}
  let acc := match proc.body with
    | .Transparent b => fromBody b acc
    | .Opaque posts impl _ =>
      let acc := posts.foldl (fun acc c => fromBody c.condition acc) acc
      (impl.map (fromBody · acc)).getD acc
    | .Abstract posts => posts.foldl (fun acc c => fromBody c.condition acc) acc
    | .External => acc
  (proc.throwsOn.foldl (fun acc blk =>
    blk.postconditions.foldl (fun acc c => fromBody c.condition acc) acc) acc)

/-- `base` if unused in `taken`, else `base_1`, `base_2`, … -/
private def freshName (base : String) (taken : Std.HashSet String) : String :=
  if !taken.contains base then base
  else
    let rec go (i : Nat) (fuel : Nat) : String :=
      match fuel with
      -- Unreachable by pigeonhole: the search visits `taken.size + 1` candidates,
      -- all distinct (`_1`, `_2`, … suffixes), and `taken` can contain at most
      -- `taken.size` of them — so a free candidate is found before the fuel runs
      -- out. The fuel exists only to make termination structural; this arm keeps
      -- the function total without an in-proof pigeonhole argument.
      | 0 => s!"{base}_{i}"
      | fuel + 1 =>
        let cand := s!"{base}_{i}"
        if taken.contains cand then go (i + 1) fuel else cand
    go 1 (taken.size + 1)

-- Pin `freshName`'s outputs for the cases the carrier naming relies on: the
-- preferred spelling when free, the first suffix when taken (the short-form
-- procedure's case), and stepping past consecutive taken names. Checked at compile
-- time; the end-to-end tests in `ThrowsClause.lean` only assert that the lowered
-- program verifies, which would not catch a freshener returning a wrong-but-unused
-- name.
#guard freshName "$result" {} == "$result"
#guard freshName "$result" (Std.HashSet.ofList ["$result"]) == "$result_1"
#guard freshName "$result" (Std.HashSet.ofList ["$result", "$result_1"]) == "$result_2"
#guard freshName "$result" (Std.HashSet.ofList ["$result_1"]) == "$result"
/-- Label of the block a `throw`/`return` exits to leave the body region; the
    `Result` construction is placed immediately after this block. Distinct from
    the translator's `$body` label (which it auto-wraps around every body). -/
private def exnExitLabel : String := "$exnexit"

/-- The generic result datatype's name (from `resultDefinitions`). Shared in
    `LaurelAST` with `ModifiesClauses`, which guards the frames it builds with
    this datatype's testers. -/
private def resultDatatypeName : String := exnResultDatatypeName

/-! ### Laurel AST constructors (synthesized nodes carry no source) -/

private def nn (e : StmtExpr) : StmtExprMd := ⟨e, .unknown⟩
private def tyNode (t : HighType) : HighTypeMd := ⟨t, .unknown⟩
private def boolTy : HighTypeMd := tyNode .TBool
/-- `Result<valTy, errTy>` — the lowered form of a `throws errTy` procedure (or a
    throwing call), carrying the value type on the Good path and the exception
    type on the Bad path. `errTy` is a real exception type (the declared `throws`
    type), never the erased heap `Composite`. -/
private def resultTyOf (valTy errTy : HighTypeMd) : HighTypeMd :=
  tyNode (.Applied (tyNode (.UserDefined (mkId resultDatatypeName))) [valTy, errTy])

private def litBool (b : Bool) : StmtExprMd := nn (.LiteralBool b)
private def localRef (name : String) : StmtExprMd := nn (.Var (.Local (mkId name)))
/-- Assignment to an existing local. -/
private def setLocal (name : String) (val : StmtExprMd) : StmtExprMd :=
  nn (.Assign [⟨.Local (mkId name), .unknown⟩] val)
/-- Variable declaration without an initializer (standalone statement). -/
private def declNoInit (name : String) (ty : HighTypeMd) : StmtExprMd :=
  nn (.Var (.Declare ⟨mkId name, ty⟩))
/-- Variable declaration with an initializer. -/
private def declInit (name : String) (ty : HighTypeMd) (val : StmtExprMd) : StmtExprMd :=
  nn (.Assign [⟨.Declare ⟨mkId name, ty⟩, .unknown⟩] val)
private def callStatic (name : String) (args : List StmtExprMd) : StmtExprMd :=
  nn (.StaticCall (mkId name) args)
/-- `Ctor(arg)` / `Datatype..fn(arg)` — a single-argument datatype op. -/
private def resultApp (fn : String) (arg : StmtExprMd) : StmtExprMd := callStatic fn [arg]
private def exitTo (label : String) : StmtExprMd := nn (.Exit label)
private def blockOf (stmts : List StmtExprMd) (label : Option String := none) : StmtExprMd :=
  nn (.Block stmts label)
private def iteOf (c t : StmtExprMd) (e : Option StmtExprMd) : StmtExprMd :=
  nn (.IfThenElse c t e)
-- Operators are calls to their built-in wrappers (see `Operation.procName`); neither
-- `$implies` nor `$and` is overloaded, so these names survive `UniqueOverloadNames`.
private def impliesOf (a b : StmtExprMd) : StmtExprMd :=
  nn (.StaticCall (mkId Operation.Implies.procName) [a, b])
private def orOf (a b : StmtExprMd) : StmtExprMd :=
  callStatic Operation.Or.procName [a, b]
private def andOf (a b : StmtExprMd) : StmtExprMd :=
  nn (.StaticCall (mkId Operation.And.procName) [a, b])
/-- `e as ty` — a downcast. On a propagation edge its runtime cast-assert is
    discharged by a preceding `assume e is ty` (see `lowerTry`). -/
private def asTypeOf (e : StmtExprMd) (ty : HighTypeMd) : StmtExprMd := nn (.AsType e ty)
/-- `e is ty` — a runtime type test. -/
private def isTypeOf (e : StmtExprMd) (ty : HighTypeMd) : StmtExprMd := nn (.IsType e ty)
/-- `assume c` — a free assumption. -/
private def assumeOf (c : StmtExprMd) : StmtExprMd := nn (.Assume c)

/-- Give every *still-source-less* node in `e` the range `src`.

    The constructor helpers above build nodes without a source, because the right
    range is not known where the node is shaped — it is known where the node is
    emitted, from the user construct being lowered. So each lowering step fills
    its output with the range of the statement (or clause) that produced it.

    Only `.unknown` sources are filled, so this is applied outermost-last: a node
    emitted while lowering an inner statement already carries that inner
    statement's range and keeps it. The net effect is that every synthesized node
    points at the *innermost* user construct responsible for it — the `try` whose
    machinery it implements, the `throw` it dispatches, the call it unwraps —
    rather than at nowhere. -/
private def fillSrc (src : FileRange) (e : StmtExprMd) : StmtExprMd :=
  mapStmtExpr (fun n => if n.source == .unknown then { n with source := src } else n) e

/-- `fillSrc` over a list of emitted statements. -/
private def fillSrcs (src : FileRange) (es : List StmtExprMd) : List StmtExprMd :=
  es.map (fillSrc src)

/-- Substitute every reference `Var (.Local name)` with `repl` throughout `e`. -/
private def substLocal (name : String) (repl : StmtExprMd) (e : StmtExprMd) : StmtExprMd :=
  mapStmtExpr (fun n => match n.val with
    | .Var (.Local id) => if id.text == name then repl else n
    | _ => n) e

/-- Whether a reference `Var (.Local name)` occurs anywhere in `e`. -/
private def localOccurs (name : String) (e : StmtExprMd) : Bool :=
  ((mapStmtExprM (m := StateM Bool)
      (fun n => do
        match n.val with
        | .Var (.Local id) => if id.text == name then set true else pure ()
        | _ => pure ()
        pure n) e).run false).2

/-! ### Callee lookup -/

/-- The resolved callee procedure, if `callee` names one. -/
private def calleeProc (model : SemanticModel) (callee : Identifier) : Option Procedure :=
  match model.get callee with
  | .staticProcedure p => some p
  | .instanceProcedure _ p => some p
  | _ => none

private def calleeThrows (model : SemanticModel) (callee : Identifier) : Bool :=
  (calleeProc model callee).map (·.throwsType.isSome) |>.getD false

/-- A procedure's value outputs: outputs that are not also inputs (i.e. not
    inout). Only a value output becomes the `Val` of the procedure's `Result`;
    an inout output keeps its own slot. Note this pass runs *before* heap
    parameterization, so the heap `$heap` — the inout output this rule mainly
    exists for — is not threaded through the signature yet; the distinction is
    kept so the lowering stays correct for any inout output. -/
private def valueOutputsOf (proc : Procedure) : List Parameter :=
  let inputNames := proc.inputs.map (·.name.text)
  proc.outputs.filter (fun o => !inputNames.contains o.name.text)

/-- The `Val` type carried on the Good path: the (single) value output's type,
    or `bool` as a placeholder for a void return. -/
private def valTyOf (proc : Procedure) : HighTypeMd :=
  match valueOutputsOf proc with
  | [o] => o.type
  | _ => boolTy

/-! ### Pass state -/

private structure EState where
  /-- Next fresh id for synthesized labels/temps. -/
  nextId : Nat := 0
  /-- Set while lowering a procedure body when a `throw`/`try`/throwing-call is
      lowered — signals that the `$thrown`/`$exc`/`$returning` locals are needed. -/
  usedExc : Bool := false
  /-- Every label whose `exit` had to unwind through a `finally` somewhere in the
      procedure being lowered. Accumulated (never cleared until the next
      procedure) so the procedure preamble can declare one `$exiting_<l>` flag
      per label. -/
  exitFlagLabels : List String := []
  /-- The labels whose `exit` unwound within the *region currently being lowered*
      — a scoped accumulator that `lowerTry` saves, clears and restores around
      its body and handlers, so it can emit re-dispatch arms for exactly the
      unwinding jumps raised inside itself (and hand the still-unfinished ones
      back to the enclosing region). -/
  raisedExits : List String := []
  /-- Procedures this pass deliberately left unlowered after rejecting them with a
      `NotYetImplemented`. The erasure backstop skips them: their exceptional
      constructs are still present *by design*, so reporting them as a bug in this
      pass would bury the real diagnostic under a `StrataBug` cascade. -/
  rejected : List String := []
  diags : List Message := []
  model : SemanticModel
  /-- Nominal subtype lattice over the program's types, used to decide whether a
      cross-`try` exception propagation needs an (assumed) downcast. -/
  lattice : TypeLattice

private abbrev EM := StateM EState

private def freshNat : EM Nat := modifyGet (fun s => (s.nextId, { s with nextId := s.nextId + 1 }))
private def markUsedExc : EM Unit := modify (fun s => { s with usedExc := true })
private def emitDiag (d : Message) : EM Unit := modify (fun s => { s with diags := s.diags ++ [d] })

/-- Append `l` to a label list unless it is already there (order-preserving, so
    the emitted flag declarations and re-dispatch arms are deterministic). -/
private def addLabel (labels : List String) (l : String) : List String :=
  if labels.contains l then labels else labels ++ [l]

/-- Record that an `exit l` is unwinding through a `finally`: the procedure needs
    a `$exiting_l` flag, and the enclosing `try` needs a re-dispatch arm for it. -/
private def recordPendingExit (l : String) : EM Unit :=
  modify (fun s => { s with
    exitFlagLabels := addLabel s.exitFlagLabels l,
    raisedExits := addLabel s.raisedExits l })

/-- An enclosing `try`'s exit targets and its active in-flight-exception local. -/
private structure TryFrame where
  /-- Label a `throw` in this region exits to (the `try`'s catch chain, or its
      `finally` for a re-throw from a handler). -/
  throwLabel : String
  /-- Label a `return` in this region exits to (so the `finally` runs). -/
  finallyLabel : String
  /-- Whether this `try` has a `finally` arm. A jump *out* of the `try` only has
      to be routed through `finallyLabel` when there is an arm to run; a
      `finally`-less `try` is transparent to `exit` (leaving its body means no
      exception is in flight, so there is nothing to re-dispatch). -/
  hasFinally : Bool
  /-- The `$exc` variable (name and type) active in this region: the `try`'s own
      `$exc_<i> : LCA` when it has `catch` clauses, otherwise the enclosing
      region's `$exc` (finally-only trys don't narrow it). `none` when no
      exception value is in play. -/
  exc : Option (String × HighTypeMd)

/-- A lexical region the lowering is currently inside, innermost first. Labeled
    blocks are tracked alongside `try` regions because an `exit` needs to know
    *which* enclosing `finally` arms its jump would leave: a jump to a label
    opened inside the innermost enclosing `try` stays within it, while a jump to a
    label opened outside must run that `try`'s `finally` on the way out. -/
private inductive Frame where
  /-- A user labeled block `{ … } l`. -/
  | labeledBlock (label : String)
  /-- An enclosing `try` region. -/
  | tryRegion (frame : TryFrame)

/-- Per-procedure lowering context. -/
private structure Ctx where
  /-- Whether the enclosing procedure declares `throws`. -/
  procThrows : Bool
  /-- The procedure-level `$exc` (name and declared `throws` type) for a throwing
      procedure — the target for top-level throws and the `Bad` result. `none`
      for a non-throwing procedure (every exception is caught within a `try`). -/
  procExc : Option (String × HighTypeMd)
  /-- Enclosing labeled blocks and `try` regions, innermost first. With no `try`
      frame, `throw`/`return` targets fall back to `$exnexit` (leave the body) and
      the active `$exc` is `procExc`. -/
  frames : List Frame

/-- The innermost enclosing `try` frame, if any. Labeled blocks are transparent
    to `throw`/`return` routing (only `exit` cares about them). -/
private def innerTry (frames : List Frame) : Option TryFrame :=
  frames.findSome? (fun f => match f with | .tryRegion t => some t | .labeledBlock _ => none)

private def throwTargetOf (ctx : Ctx) : String :=
  ((innerTry ctx.frames).map (·.throwLabel)).getD exnExitLabel
private def finallyTargetOf (ctx : Ctx) : String :=
  ((innerTry ctx.frames).map (·.finallyLabel)).getD exnExitLabel
/-- The `$exc` variable (name and type) active in the current region: the
    innermost `try` frame's, or `procExc` at the procedure top level. -/
private def currentExc (ctx : Ctx) : Option (String × HighTypeMd) :=
  match innerTry ctx.frames with
  | some f => f.exc
  | none   => ctx.procExc

/-- The `finally` arm an `exit target` from here must run before it can leave:
    the innermost enclosing `try` that has a `finally` and that the jump would
    exit. `none` when the jump crosses no such `try` — either its target label is
    opened inside the innermost one, or there is none — in which case the `exit`
    needs no unwinding and is emitted unchanged.

    Walking outward and stopping at the target's own label is what distinguishes
    the two cases; a `finally`-less `try` in between is skipped, since a jump out
    of it has nothing to run (its enclosing `try` may still have an arm). -/
private def crossedFinallyOf (frames : List Frame) (target : String) : Option String :=
  match frames with
  | [] => none
  | .labeledBlock l :: rest => if l == target then none else crossedFinallyOf rest target
  | .tryRegion f :: rest => if f.hasFinally then some f.finallyLabel else crossedFinallyOf rest target

/-! ### Statement lowering -/

/-- Lower a call to a throwing procedure. The callee now returns any inout
    outputs it has *and* a `Result` value; bind the `Result`
    to a fresh temp — keeping the inout targets — then propagate on `Bad` or
    unwrap the value on `Good`. (The heap `$heap` becomes such an inout output
    only later, when heap parameterization threads it through both signatures and
    call sites; this pass runs before that.)

    The original call is a (possibly multi-target) assignment whose targets align
    positionally with the callee's original outputs. The inout targets are kept
    in place; the single value target is replaced by the fresh `$callres` and
    unwrapped on the Good path. This matches the callee's new output order
    (inout outputs, then the `Result`).

    Not recursive (it only rewrites the call node itself), so it sits outside the
    statement-lowering `mutual` block below. -/
private def lowerThrowingCall (ctx : Ctx) (callNode : StmtExprMd)
    (targets : List VariableMd) : EM (List StmtExprMd) := do
  markUsedExc
  let model := (← get).model
  let callee := match callNode.val with
    | .StaticCall c _ => c
    | .InstanceCall _ c _ => c
    | _ => mkId "?"
  let p? := calleeProc model callee
  let valTy := p?.map valTyOf |>.getD boolTy
  -- The callee's `Result` carries its declared `throws` type on the Bad path.
  let errTy := (p?.bind (·.throwsType)).getD boolTy
  let calleeInputNames := (p?.map (·.inputs.map (·.name.text))).getD []
  let calleeOutputs := (p?.map (·.outputs)).getD []
  let tid ← freshNat
  let callres := s!"$callres_{tid}"
  -- Split targets (positional with callee outputs) into kept inout targets and
  -- the single value target (replaced by `$callres`, unwrapped on the Good path).
  let paired := targets.zip calleeOutputs
  let inoutTargets := paired.filterMap (fun (t, o) =>
    if calleeInputNames.contains o.name.text then some t else none)
  let valueTarget? := (paired.find? (fun (_, o) => !calleeInputNames.contains o.name.text)).map Prod.fst
  let callresTarget : VariableMd := ⟨.Declare ⟨mkId callres, resultTyOf valTy errTy⟩, .unknown⟩
  let multiCall := nn (.Assign (inoutTargets ++ [callresTarget]) callNode)
  -- Propagate on `Bad` (exits the block), so the Good-path unwrap that follows is
  -- reached only when the call did not throw. An else-less `if` keeps this void.
  -- The propagated exception is written into the current region's `$exc` (whose
  -- type is a supertype of the callee's `throws` type, so no cast is needed).
  let onBad : List StmtExprMd :=
    (match currentExc ctx with
      | some (v, _) => [setLocal v (resultApp exnResultErr (localRef callres))]
      | none => []) ++
    [ setLocal exnThrownVar (litBool true), exitTo (throwTargetOf ctx) ]
  let propagate := iteOf (resultApp exnResultIsBad (localRef callres))
    (blockOf onBad) none
  -- A `Declare` value target is declared up front so it stays in scope for later
  -- statements; it is assigned the unwrapped value only on the Good path.
  let (preDecls, goodStmts) : List StmtExprMd × List StmtExprMd :=
    match valueTarget? with
    | some ⟨.Declare param, declSrc⟩ =>
        -- Reuse the original declaration verbatim, minus its initializer. The type
        -- annotation is optional, so an unannotated `var x := f()` has to stay
        -- unannotated here rather than have one invented for it.
        ([⟨.Var (.Declare param), declSrc⟩],
         [setLocal param.name.text (resultApp exnResultValue (localRef callres))])
    | some ⟨.Local x, _⟩ =>
        ([], [setLocal x.text (resultApp exnResultValue (localRef callres))])
    | _ => ([], [])
  -- All of this is machinery for one call, so it points at the call.
  pure (fillSrcs callNode.source (preDecls ++ [multiCall, propagate] ++ goodStmts))

mutual

/-- Lower a list of statements, concatenating the (possibly expanded) results.
    Statements after an unconditional terminator (`throw`/`return`/`exit`, which
    all lower to an `exit`) are unreachable and dropped, so re-resolution does
    not flag dead code after the synthesized `exit`. -/
private def lowerStmts (ctx : Ctx) (stmts : List StmtExprMd) : EM (List StmtExprMd) := do
  match stmts with
  | [] => pure []
  | s :: rest =>
      -- Everything emitted for `s` that has no range yet gets `s`'s own range.
      let s' := fillSrcs s.source (← lowerStmt ctx s)
      match s.val with
      -- Unconditional terminator: everything after it is unreachable, so stop
      -- (rather than emitting dead code after the synthesized `exit`).
      | .Throw _ | .Return _ | .Exit _ => pure s'
      | _ => pure (s' ++ (← lowerStmts ctx rest))
  termination_by sizeOf stmts
  decreasing_by
    all_goals simp_wf
    all_goals (try term_by_mem)
    all_goals (try (simp_all; omega))

/-- Lower a single statement into a list of exception-free statements. -/
private def lowerStmt (ctx : Ctx) (stmt : StmtExprMd) : EM (List StmtExprMd) := do
  let src := stmt.source
  -- `_h` names the discriminant equation (`stmt.val = …`) so the termination
  -- proof can relate each child's size back to `stmt` (used only there, hence
  -- the `_` prefix).
  match _h : stmt.val with
  | .Block stmts label =>
      -- A labeled block enters a new `exit` target scope: an `exit` to this label
      -- from inside stays within any enclosing `try`, so record it (see `Frame`).
      let inner := match label with
        | some l => { ctx with frames := .labeledBlock l :: ctx.frames }
        | none => ctx
      let stmts' ← lowerStmts inner stmts
      pure [⟨.Block stmts' label, src⟩]
  | .IfThenElse c t e =>
      -- These branch/body recursions do not go through `lowerStmts`, so fill each
      -- child's output with that child's own range here.
      let t' := fillSrcs t.source (← lowerStmt ctx t)
      let e' ← match _he : e with
        | some eb => do pure (some (blockOf (fillSrcs eb.source (← lowerStmt ctx eb))))
        | none => pure none
      pure [⟨.IfThenElse c (blockOf t') e', src⟩]
  | .While c invs dec body postTest =>
      let body' := fillSrcs body.source (← lowerStmt ctx body)
      pure [⟨.While c invs dec (blockOf body') postTest, src⟩]
  | .Throw value =>
      markUsedExc
      -- Write the thrown value into the current region's `$exc` (its type is a
      -- supertype of every type thrown here, so no cast is needed). The `none`
      -- case is unreachable for a well-formed program (a throw with no enclosing
      -- `$exc` would escape, which the resolution-time escape check rejects).
      let setExc := match currentExc ctx with
        | some (v, _) => [setLocal v value]
        | none => []
      pure (setExc ++ [ setLocal exnThrownVar (litBool true), exitTo (throwTargetOf ctx) ])
  | .Return _ =>
      -- Value payloads were removed by EliminateValueInReturns, so this is a
      -- valueless return. Route it so that any enclosing `finally` runs,
      -- else jump to `$exnexit` to build the result / leave the body.
      markUsedExc
      match innerTry ctx.frames with
      | none => pure [exitTo exnExitLabel]
      | some f =>
          pure [ setLocal exnReturningVar (litBool true), exitTo f.finallyLabel ]
  | .Exit target =>
      -- An `exit` that leaves an enclosing `try`/`finally` must run that arm on
      -- the way out, exactly like a `return` does: flag the pending jump, hand
      -- control to the `finally`, and let the re-dispatch after it continue the
      -- unwind (or deliver the jump when no further arm is crossed). An `exit`
      -- that crosses no `finally` needs none of this and is left as it is.
      match crossedFinallyOf ctx.frames target with
      | none => pure [stmt]
      | some finLbl => do
          markUsedExc
          recordPendingExit target
          pure [ setLocal (exitPendingVar target) (litBool true), exitTo finLbl ]
  | .Try body catches finally? =>
      lowerTry ctx src body catches finally?
  | .Assign targets value =>
      -- A call to a throwing procedure on the RHS needs the propagate/unwrap
      -- dispatch; any other assignment is left untouched.
      match value.val with
      | .StaticCall callee _ | .InstanceCall _ callee _ =>
          if calleeThrows (← get).model callee then
            lowerThrowingCall ctx value targets
          else pure [stmt]
      | _ => pure [stmt]
  | .StaticCall callee _ =>
      if calleeThrows (← get).model callee then
        lowerThrowingCall ctx stmt []
      else pure [stmt]
  | .InstanceCall _ callee _ =>
      if calleeThrows (← get).model callee then
        lowerThrowingCall ctx stmt []
      else pure [stmt]
  | _ => pure [stmt]
  termination_by sizeOf stmt
  decreasing_by
    all_goals simp_wf
    all_goals (have hsz := AstNode.sizeOf_val_lt stmt; rw [_h] at hsz)
    all_goals (try term_by_mem)
    all_goals (try (simp_all; omega))

/-- Lower a `try`/`catch`/`finally` into two nested labeled blocks plus the
    `finally` arm and a re-dispatch that keeps a pending throw/return/`exit`
    unwinding. -/
private def lowerTry (ctx : Ctx) (src : FileRange)
    (body : StmtExprMd) (catches : List CatchClause) (finally? : Option StmtExprMd)
    : EM (List StmtExprMd) := do
  markUsedExc
  let saved := ctx.frames
  let parentExc := currentExc ctx
  -- Start a fresh scope for unwinding `exit`s: whatever the body and handlers
  -- raise is this try's to re-dispatch (restored, plus the jumps still travelling
  -- outward, once they are lowered).
  let outerRaisedExits := (← get).raisedExits
  modify (fun s => { s with raisedExits := [] })
  let tryId ← freshNat
  let tryLbl := s!"$try_{tryId}"
  let tryFinLbl := s!"$tryfin_{tryId}"
  -- This try's in-flight-exception local: a fresh `$exc_<id>` typed at the try's
  -- least-common-ancestor exception type (`bindingType`, computed and carried on
  -- the resolved `catch` clause by `Check.tryCatch`) when the try has `catch`
  -- clauses; a finally-only try reuses the enclosing region's `$exc` (there is
  -- no handler to inspect it, so nothing narrows its type).
  -- A `catch` clause is *reachable* only if resolution found a thrown type for
  -- it. A try whose body throws nothing determinable has `bindingType = Unknown`
  -- (resolution's `collectThrownTypeNames` reached no throw), so its catches can
  -- never fire; drop them and lower the try as finally-only. This also avoids an
  -- `Unknown`-typed `$exc_<i>` (which Core rejects) and dead catch guards
  -- (`e is T`) that, at the erased Unknown type, have no valid pre-heap type to
  -- test unrelated `T`s against.
  let catchesReachable : Bool :=
    match catches with
    | c :: _ => match c.bindingType.val with | .Unknown => false | _ => true
    | [] => false
  let effectiveCatches := if catchesReachable then catches else []
  -- `introducedExc` is true when this try introduces its *own* `$exc_<id>` (it
  -- has reachable `catch` clauses, typed at their LCA). A finally-only try (or a
  -- try whose catches were dropped) reuses the enclosing region's `$exc`.
  let (thisExc, introducedExc) : Option (String × HighTypeMd) × Bool :=
    match effectiveCatches with
    | [] => (parentExc, false)
    | c :: _ => (some (s!"$exc_{tryId}", c.bindingType), true)
  let excVar := (thisExc.map Prod.fst).getD exnExcVar
  let excTy := (thisExc.map Prod.snd).getD boolTy
  let hasFinally := finally?.isSome
  -- Body phase: a `throw` enters the catch chain ($try); a `return` runs
  -- `finally` first ($tryfin).
  let bodyFrame : TryFrame :=
    { throwLabel := tryLbl, finallyLabel := tryFinLbl, exc := thisExc, hasFinally }
  let bStmts := fillSrcs body.source
    (← lowerStmt { ctx with frames := .tryRegion bodyFrame :: saved } body)
  -- Catch phase: a re-`throw` or `return` in a handler skips the (remaining)
  -- catch chain but still runs `finally` ($tryfin).
  let catchFrame : TryFrame :=
    { throwLabel := tryFinLbl, finallyLabel := tryFinLbl, exc := thisExc, hasFinally }
  let catchCtx : Ctx := { ctx with frames := .tryRegion catchFrame :: saved }
  -- Map over the `catches` *parameter* (via `attach`, so each clause carries its
  -- membership proof for the termination argument); the unreachable-catch case is
  -- handled by the `catchesReachable` guard rather than by mapping over the
  -- derived `effectiveCatches` list.
  let clauses ← if catchesReachable then catches.attach.mapM (fun ⟨c, _⟩ => do
    -- The guard reads this try's `$exc` directly: it is evaluated at dispatch
    -- time, before the handler runs, so no nested throw has clobbered it yet.
    let pExpr := match c.predicate with
      | some p => substLocal c.binding.text (localRef excVar) p
      | none => litBool true
    let hStmts := fillSrcs c.body.source (← lowerStmt catchCtx c.body)
    -- Snapshot the caught exception into a fresh per-handler local when the
    -- handler references its binding. A `throw`/throwing-call *inside* this
    -- handler that is itself caught (e.g. a nested `try`/`catch`) overwrites
    -- this try's `$exc`; without the snapshot a later use of this handler's
    -- binding would read that inner exception instead. Skipped when the binding
    -- is unused, to avoid an inert local in the common case. The snapshot is
    -- typed at this try's LCA (the binding's own type), so `e#field` in the
    -- handler needs no downcast.
    let (bindDecls, hStmts) ←
      if hStmts.any (localOccurs c.binding.text) then do
        let bid ← freshNat
        let bindLocal := s!"$exc_{c.binding.text}_{bid}"
        pure ([declInit bindLocal excTy (localRef excVar)],
              hStmts.map (substLocal c.binding.text (localRef bindLocal)))
      else
        pure ([], hStmts)
    let guard := andOf (localRef exnThrownVar) pExpr
    let handler := setLocal exnThrownVar (litBool false) :: (bindDecls ++ hStmts)
    pure (guard, handler))
  else pure []
  -- First-match-wins is enforced by clearing `$thrown` on a match: once a clause
  -- fires, later `$thrown && guardⱼ` guards are false. So the chain is a *sequence*
  -- of else-less `if`s rather than a nested `if`/`else` — an else-less `if` types
  -- as void, avoiding a branch-type mismatch when a handler ends in an assignment
  -- (which Laurel types as the assigned value, not void).
  let catchChainStmts : List StmtExprMd := clauses.map (fun (g, h) => iteOf g (blockOf h) none)
  -- The unwinding `exit`s raised by the body and the handlers are this try's to
  -- re-dispatch after its `finally`. A jump whose *next* crossed `finally` lies
  -- further out keeps travelling, so it is also handed back to the enclosing
  -- region's scope; one that gets delivered here is not. (The `finally` arm is
  -- lowered below in the enclosing context, so anything it raises accumulates
  -- there — control never comes back to this re-dispatch.)
  let raisedExits := (← get).raisedExits
  let onwardExits := raisedExits.filter (fun l => (crossedFinallyOf saved l).isSome)
  modify (fun s => { s with raisedExits := onwardExits.foldl addLabel outerRaisedExits })
  -- Finally phase: a `throw`/`return` in F targets the enclosing `try`.
  -- Abrupt completion of the `finally` arm (a `return`/`throw`/unwinding `exit`
  -- inside F) must *supersede* a completion left pending by the body or a handler
  -- (Java JLS §14.20.2 / C#). So snapshot and clear `$thrown`/`$returning`/`$exc`
  -- (and every pending `$exiting_<l>` flag) before F and restore them immediately
  -- after: if F completes abruptly it sets its own flags and `exit`s, jumping
  -- *past* the restore (the pending completion is dropped — finally wins); if F
  -- falls through, the restore re-instates the pending completion so the
  -- re-dispatch below replays it. (`$exc` is restored too so a nested `try` inside
  -- F that clobbers this try's `$exc` can't corrupt the re-propagated exception.)
  -- The `$exc` snapshot is emitted only when this try has an `$exc` (a
  -- finally-only try in a non-throwing procedure may not).
  let (finPrologue, finEpilogue) ← match finally? with
    | none => pure ([], [])
    | some _ => do
        let finId ← freshNat
        let savThrown := s!"$fin_thrown_{finId}"
        let savReturning := s!"$fin_returning_{finId}"
        let (excSnap, excRestore) : List StmtExprMd × List StmtExprMd :=
          match thisExc with
          | some (v, ty) =>
              let savExc := s!"$fin_exc_{finId}"
              ([declInit savExc ty (localRef v)], [setLocal v (localRef savExc)])
          | none => ([], [])
        let exitSnap := raisedExits.map (fun l =>
          declInit s!"$fin_exiting_{l}_{finId}" boolTy (localRef (exitPendingVar l)))
        let exitClear := raisedExits.map (fun l => setLocal (exitPendingVar l) (litBool false))
        let exitRestore := raisedExits.map (fun l =>
          setLocal (exitPendingVar l) (localRef s!"$fin_exiting_{l}_{finId}"))
        pure
          ([ declInit savThrown boolTy (localRef exnThrownVar),
             declInit savReturning boolTy (localRef exnReturningVar) ] ++ excSnap ++ exitSnap ++
           [ setLocal exnThrownVar (litBool false),
             setLocal exnReturningVar (litBool false) ] ++ exitClear,
           [ setLocal exnThrownVar (localRef savThrown),
             setLocal exnReturningVar (localRef savReturning) ] ++ excRestore ++ exitRestore)
  let fStmts ← match _hf : finally? with
    | some f => do pure (fillSrcs f.source (← lowerStmt ctx f))
    | none => pure []
  -- Re-dispatch: keep any pending exception/return unwinding outward. On the
  -- exception edge, copy this try's `$exc` into the enclosing region's `$exc`,
  -- relating this try's LCA `ti` to the enclosing type `tp`:
  --   * `ti <: tp` — plain copy (the residual widens to a supertype).
  --   * `tp <: ti` — assumed checked downcast (`assume … is tp; … as tp`), sound
  --     because the residual analysis proved only types `<: tp` actually escape.
  --   * unrelated — no copy is emitted, because none is well-typed (even
  --     `vi as tp` is rejected as a cast between unrelated types). Reaching this
  --     edge with something actually escaping needs a common subtype of `ti` and
  --     `tp`, which only multiple inheritance can produce (`composite C extends
  --     A, B`); resolution rejects that shape up front in
  --     `checkPropagationEdges`, so what is left here is the dead case: nothing
  --     can escape this try into `tp`.
  -- A finally-only try shares the enclosing `$exc` (same variable), so no copy.
  let thrownExit := ((innerTry saved).map (·.throwLabel)).getD exnExitLabel
  let returnExit := ((innerTry saved).map (·.finallyLabel)).getD exnExitLabel
  let lattice := (← get).lattice
  let copyStmts : List StmtExprMd :=
    match thisExc, parentExc with
    | some (vi, ti), some (vp, tp) =>
        if vi == vp then []
        else if isSubtype lattice ti tp then [ setLocal vp (localRef vi) ]
        else if isSubtype lattice tp ti then
          [ assumeOf (isTypeOf (localRef vi) tp), setLocal vp (asTypeOf (localRef vi) tp) ]
        else []
    | _, _ => []
  -- Pending unwinding `exit`s, one arm each: continue to the next crossed
  -- `finally` if there is one, otherwise deliver the jump — clearing the flag as
  -- it is delivered, so a later completion of an enclosing `try` cannot mistake
  -- the spent flag for a fresh pending jump. At most one completion is pending on
  -- any path (control is linear), so these arms cannot compete with each other or
  -- with the throw/return arms above.
  let exitDispatch : List StmtExprMd := raisedExits.map (fun l =>
    match crossedFinallyOf saved l with
    | some outerFin => iteOf (localRef (exitPendingVar l)) (blockOf [exitTo outerFin]) none
    | none =>
        iteOf (localRef (exitPendingVar l))
          (blockOf [setLocal (exitPendingVar l) (litBool false), exitTo l]) none)
  let reDispatch : List StmtExprMd :=
    [ iteOf (localRef exnThrownVar) (blockOf (copyStmts ++ [exitTo thrownExit])) none,
      iteOf (localRef exnReturningVar) (blockOf [exitTo returnExit]) none ] ++ exitDispatch
  let tryFinBlock := blockOf (blockOf bStmts (some tryLbl) :: catchChainStmts) (some tryFinLbl)
  -- Declare this try's own `$exc_<id>` in the enclosing scope, just before the
  -- try/finally block, so it is live for the body, catch chain, `finally`, and
  -- re-dispatch. Only when this try introduced its own `$exc` (a finally-only
  -- or Unknown-LCA try reuses the enclosing one, which is already declared).
  let declExc : List StmtExprMd :=
    match thisExc with
    | some (v, ty) => if introducedExc then [declNoInit v ty] else []
    | none => []
  pure (declExc ++ (⟨tryFinBlock.val, src⟩ :: (finPrologue ++ fStmts ++ finEpilogue ++ reDispatch)))
  -- `lowerTry` receives a `try`'s *components* rather than the node, so its
  -- measure is their combined size plus one: exactly the size of the `Try` node
  -- `lowerStmt` came from (so that call decreases), while still dominating each
  -- component it recurses into.
  termination_by 1 + sizeOf body + sizeOf catches + sizeOf finally?
  decreasing_by
    all_goals simp_wf
    all_goals (try have := CatchClause.sizeOf_body_lt ‹_›)
    all_goals (try have := CatchClause.sizeOf_predicate_lt ‹_›)
    all_goals (try term_by_mem)
    all_goals (try (simp_all; omega))

end

/-! ### Detecting whether a procedure needs the transform -/

private def stmtUsesExn (model : SemanticModel) (stmt : StmtExprMd) : Bool :=
  match _h : stmt.val with
  | .Throw _ => true
  | .Try _ _ _ => true
  | .StaticCall callee _ => calleeThrows model callee
  | .InstanceCall _ callee _ => calleeThrows model callee
  | .Assign _ v => stmtUsesExn model v
  | .Block stmts _ => stmts.attach.any (fun ⟨s, _⟩ => stmtUsesExn model s)
  | .IfThenElse c t e =>
      stmtUsesExn model c || stmtUsesExn model t || (e.attach.any (fun ⟨x, _⟩ => stmtUsesExn model x))
  | .While c _ _ b _ => stmtUsesExn model c || stmtUsesExn model b
  | _ => false
  termination_by sizeOf stmt
  decreasing_by
    all_goals simp_wf
    all_goals (have hsz := AstNode.sizeOf_val_lt stmt; rw [_h] at hsz)
    all_goals (try term_by_mem)
    all_goals (try (simp_all; omega))

private def bodyHasExn (model : SemanticModel) (proc : Procedure) : Bool :=
  match proc.body.implementation with
  | some b => stmtUsesExn model b
  | none => false

/-! ### Procedure lowering -/

/-- Existing (normal) postconditions declared on a body, if any. -/
private def bodyPostconditions (body : Body) : List Condition :=
  match body with
  | .Opaque posts _ _ => posts
  | .Abstract posts => posts
  | _ => []

/-- Existing (normal) modifies groups declared on a body, if any. -/
private def bodyModifies (body : Body) : List ModifiesGroup :=
  match body with
  | .Opaque _ _ mods => mods
  | _ => []

/-- Lower a single procedure. Non-exceptional procedures are returned unchanged. -/
private def lowerProc (proc : Procedure) : EM Procedure := do
  let procThrows := proc.throwsType.isSome
  let model := (← get).model
  if !(procThrows || bodyHasExn model proc) then
    return proc
  modify (fun s => { s with usedExc := false, exitFlagLabels := [], raisedExits := [] })
  -- Procedure-level `$exc` (throwing procedures only): typed at the declared
  -- `throws` type. Non-throwing procedures have none — every exception they use
  -- is caught within a `try`, which supplies its own `$exc_<i>`.
  let procExc : Option (String × HighTypeMd) := proc.throwsType.map (fun t => (exnExcVar, t))
  let ctx : Ctx := { procThrows, procExc, frames := [] }
  let valueOutputs := valueOutputsOf proc
  -- Lowering limitation: a `throws` procedure lowers to a single `Result` value, so it
  -- can carry at most one value output.
  if procThrows && valueOutputs.length >= 2 then
    emitDiag (diagnosticFromSource proc.name.source
      s!"throwing procedure '{proc.name.text}' has {valueOutputs.length} value outputs; a procedure that declares `throws` may return at most one value, because exception lowering packs its two possible outcomes into a single result that carries either the returned value or the thrown exception. Combine the outputs (e.g. into a composite) or drop the `throws` clause."
      MessageKind.notYetImplemented)
    -- Stop, rather than lowering a shape we have just declared unsupported. Carrying
    -- on would pick `valTy = boolTy` and `valName? = none` from the fall-through in
    -- `valTyOf`, rewriting the procedure to return `Result<bool, T>` with a
    -- placeholder `Good(true)` and dropping its real outputs — a malformed lowering
    -- that outlives the diagnostic and produces confusing secondary errors
    -- downstream. Returning it unlowered leaves the program as authored.
    modify (fun s => { s with rejected := proc.name.text :: s.rejected })
    return proc
  -- Lower the implementation statements (if any).
  let loweredBody? ← match proc.body.implementation with
    | some b => do pure (some (fillSrcs b.source (← lowerStmt ctx b)))
    | none => pure none
  let usedExc := (← get).usedExc
  let exitFlags := (← get).exitFlagLabels
  let isBodiless := loweredBody?.isNone

  if !procThrows then
    -- Non-throwing procedure that uses the exceptional channel locally (a `try`
    -- that catches everything, or a call it handles). Keep its body kind (and
    -- thus its caller-visible transparency), just rewrite the implementation.
    let excDecls := excStateDecls procExc exitFlags (needed := usedExc)
    -- Procedure-level scaffolding (`$thrown`/`$exc` declarations, the body-exit
    -- block) belongs to the procedure, so it points at the procedure name.
    let assembled := fillSrc proc.name.source
      (blockOf (excDecls ++ wrapExit (loweredBody?.getD [])))
    let newBody := match proc.body with
      | .Transparent _ => .Transparent assembled
      | .Opaque posts _ modif => .Opaque posts (some assembled) modif
      | b => b
    return { proc with body := newBody }

  -- Throwing procedure: return a single `Result`, build it after the body, and
  -- turn the exceptional contract into ordinary postconditions over the carrier.
  let valTy := valTyOf proc
  -- The declared `throws` type is the `Result`'s `Err` argument.
  let throwsTy := proc.throwsType.getD boolTy
  let valName? := match valueOutputs with | [o] => some o.name.text | _ => none
  let inputNames := proc.inputs.map (·.name.text)
  let inoutOutputs := proc.outputs.filter (fun o => inputNames.contains o.name.text)
  -- The carrier's name is *chosen*, not fixed: `exnResultVar` is only the preferred
  -- spelling, stepped past any identifier the procedure already uses. No other code
  -- relies on the spelling — every reference to the carrier is emitted below, right
  -- here — so a taken name costs a suffix, not a collision. The short `: T` return form
  -- is the ubiquitous case: it mints its value output under this very name, so such
  -- a procedure's carrier freshens to `$result_1`, keeping the value output and the
  -- carrier distinct identifiers in the lowered signature's scope.
  let carrier := freshName exnResultVar (usedNames proc)
  let newOutputs := inoutOutputs ++ [⟨mkId carrier, resultTyOf valTy throwsTy⟩]
  -- Postconditions.
  let goodWrap (p : StmtExprMd) : StmtExprMd :=
    let p' := match valName? with
      | some n => substLocal n (resultApp exnResultValue (localRef carrier)) p
      | none => p
    impliesOf (resultApp exnResultIsGood (localRef carrier)) p'
  -- A `free` condition corresponds to `ConditionMode.Assume` internally. A
  -- bodiless (abstract/opaque-no-impl) procedure's postconditions are assumed,
  -- not checked, so force `.Assume` there; otherwise keep the original mode.
  let wrappedPosts := (bodyPostconditions proc.body).map (fun c =>
    { c with condition := fillSrc c.condition.source (goodWrap c.condition),
             mode := if isBodiless then .Assume else c.mode })
  -- Preserve the declared exception type as a Bad-path fact:
  -- `Result..isBad($result) ==> Result..err($result) is T`. Derived straight from
  -- `throwsType` rather than from any authored clause, because it holds on every
  -- throwing path — the escape check has already established that only subtypes of
  -- `T` escape. Emitted only for a composite `T`: `e is T` would be ill-formed for
  -- a non-composite one and would cascade a spurious "cannot test unrelated type".
  -- The `is` test itself is lowered later, by heap parameterization and the
  -- type-hierarchy transform, both of which run after this pass.
  let throwsTypePosts : List Condition :=
    match proc.throwsType with
    | some tyNode =>
      match tyNode.val with
      | .UserDefined _ =>
        [{ condition := fillSrc tyNode.source
             (impliesOf (resultApp exnResultIsBad (localRef carrier))
               ⟨.IsType (resultApp exnResultErr (localRef carrier)) tyNode, tyNode.source⟩)
           mode := if isBodiless then .Assume else .Both }]
      | _ => []
    | none => []
  -- Each `throwsOn C { ensures P … }` case: `C ==> (Result..isBad($result) ∧ P)`.
  -- The guard is on the left, so establishing `C` at a call site proves the call
  -- throws; the conjunction on the right is what then holds. The thrown value,
  -- named by the bound `throws (e: T)` form, becomes `Result..err($result)`.
  --
  -- A case splits into two kinds of condition:
  --
  --   forcing:        `C ==> Result..isBad($result)`
  --   postcondition:  `C ∧ Result..isBad($result) ==> P`   (one per `ensures P`)
  --
  -- which together give `C ==> P` — the same strength as one combined
  -- `C ==> (isBad ∧ P)` — while keeping `C` and `isBad` as implication *antecedents*
  -- rather than a conjunct. That matters for two reasons. A cast in `P` lowers to an
  -- embedded `assert (e is T)` (see `HeapParameterization`), which is discharged from
  -- the enclosing antecedents, so the idiomatic
  -- `ensures e is T ==> (e as T)#f …` only verifies in this shape. And a body that
  -- never throws on a guarded path then fails as *one* condition: the forcing claim
  -- fails while every postcondition is vacuous, instead of also failing against a
  -- thrown value read off a `Good` result.
  --
  -- The guard stays in the antecedent rather than being dropped in favour of `isBad`
  -- alone, so one case's postconditions do not constrain another case's throwing path.
  -- An authored `mode` on a case's postcondition is *preserved*, exactly as the
  -- normal-path arm above preserves one on a top-level `ensures`. Only `forcing` and
  -- `throwsTypePosts` have their mode computed here, because this pass synthesizes
  -- them; a case's `ensures` comes from the program and carries a mode that is the
  -- author's to set. `ThrowsOnBlock.postconditions` is public AST and front ends
  -- construct Laurel programs directly rather than through the parser, so an
  -- assume-only case postcondition has to survive the rewrite even though no surface
  -- syntax produces one. The forcing claim stays computed regardless: a `free` forcing
  -- claim would assert nothing about the body, which is the one thing a case exists to
  -- do.
  let throwsOnPosts := proc.throwsOn.flatMap (fun blk =>
    let synthesizedMode := if isBodiless then ConditionMode.Assume else ConditionMode.Both
    let isBad := resultApp exnResultIsBad (localRef carrier)
    let forcing : Condition :=
      { condition := fillSrc blk.guard.source (impliesOf blk.guard isBad)
        summary := "throwsOn case forces a throw"
        mode := synthesizedMode }
    let posts := blk.postconditions.map (fun c =>
      let p' := match proc.throwsBinding with
        | some b => substLocal b.text (resultApp exnResultErr (localRef carrier)) c.condition
        | none => c.condition
      ({ c with condition := fillSrc c.condition.source (impliesOf (andOf blk.guard isBad) p')
                mode := if isBodiless then ConditionMode.Assume else c.mode } : Condition))
    forcing :: posts)
  -- Exhaustiveness: `Result..isBad(<carrier>) ==> (C₁ ∨ … ∨ Cₙ)`. Stating at least
  -- one case is a claim to have enumerated them, so a throwing path matching no
  -- guard is reported here rather than silently escaping every case frame — where
  -- it would be unconstrained, since each frame's antecedent is false on such a
  -- path. Not emitted when the procedure states no cases: it then claims nothing
  -- about its throwing paths, and an empty disjunction would read as "never
  -- throws". For a bodiless procedure it is assumed rather than checked, like every
  -- other clause there — stating the cases *is* the author's enumeration of them.
  let exhaustivenessPost : List Condition :=
    match proc.throwsOn with
    | [] => []
    | blk :: blks =>
      let anyGuard := blks.foldl (fun acc b => orOf acc b.guard) blk.guard
      [{ condition := fillSrc proc.name.source
           (impliesOf (resultApp exnResultIsBad (localRef carrier)) anyGuard)
         summary := "throwsOn cases cover every throwing path"
         mode := if isBodiless then ConditionMode.Assume else ConditionMode.Both }]
  let allPosts := wrappedPosts ++ throwsTypePosts ++ throwsOnPosts ++ exhaustivenessPost
  -- The frames. A frame's two-state axiom needs `$heap` and the field constants,
  -- which only exist after heap parameterization, so it cannot be *built* here —
  -- but everything exceptional about it can be resolved here, into the guard of an
  -- ordinary `ModifiesGroup`. The user's own frame applies to the normal exit, so
  -- it is re-guarded on `Result..isGood(<carrier>)`; each `throwsOn` case
  -- contributes a group guarded on `Result..isBad(<carrier>) && C`. After this,
  -- no downstream pass knows this procedure ever had an exceptional channel:
  -- `ModifiesClauses` lowers "guard implies frame" for any guard.
  --
  -- A case with no frame targets contributes nothing (it constrains no locations),
  -- and a case whose frame is the wildcard `*` likewise: "anything may change" is
  -- the absence of a frame, and emitting an empty-target group instead would claim
  -- the opposite ("nothing may change").
  let isBadGuard (extra : Option StmtExprMd) : StmtExprMd :=
    let isBad := resultApp exnResultIsBad (localRef carrier)
    match extra with
    | some c => andOf isBad c
    | none => isBad
  let normalGroups := (bodyModifies proc.body).map (fun g =>
    { g with guard := some (match g.guard with
        | some c => andOf (resultApp exnResultIsGood (localRef carrier)) c
        | none => resultApp exnResultIsGood (localRef carrier)) })
  let caseGroups : List ModifiesGroup := proc.throwsOn.filterMap (fun blk =>
    if blk.modifies.isEmpty || hasModifiesWildcard blk.modifies then none
    else some { targets := blk.modifies
                guard := some (fillSrc blk.guard.source (isBadGuard (some blk.guard)))
                summary := some "throwsOn modifies clause" })
  let newModifies := normalGroups ++ caseGroups
  -- Body assembly (only when there is an implementation).
  let goodArg := match valName? with | some n => localRef n | none => litBool true
  let construct := iteOf (localRef exnThrownVar)
    (blockOf [setLocal carrier (resultApp exnResultBadCtor (localRef exnExcVar))])
    (some (blockOf [setLocal carrier (resultApp exnResultGoodCtor goodArg)]))
  let assembledBody? : Option StmtExprMd := loweredBody?.map (fun bstmts =>
    fillSrc proc.name.source <|
    let excDecls := excStateDecls procExc exitFlags (needed := true)
    let valDecl := match valName? with | some n => [declNoInit n valTy] | none => []
    blockOf (excDecls ++ valDecl ++ [blockOf bstmts (some exnExitLabel), construct]))
  let newBody := match proc.body with
    | .Abstract _ => .Abstract allPosts
    | _ => .Opaque allPosts assembledBody? newModifies
  -- `throwsOn` is fully consumed: its postconditions became guarded conditions, its
  -- frames became guarded `ModifiesGroup`s, and the exhaustiveness claim is emitted
  -- above. After this pass, nothing downstream can tell the procedure ever had an
  -- exceptional channel.
  return { proc with
    outputs := newOutputs
    body := newBody
    throwsType := none
    throwsBinding := none
    throwsOn := [] }
where
  /-- The `$thrown`/`$returning` declarations (always) plus the procedure-level
      `$exc` (only for a throwing procedure, typed at its `throws` type) and one
      `$exiting_<l>` flag per label an `exit` had to unwind to, emitted when the
      body uses the exceptional channel. -/
  excStateDecls (procExc : Option (String × HighTypeMd)) (exitFlags : List String)
      (needed : Bool) : List StmtExprMd :=
    if needed then
      [ declInit exnThrownVar boolTy (litBool false) ] ++
      (match procExc with | some (v, ty) => [declNoInit v ty] | none => []) ++
      [ declInit exnReturningVar boolTy (litBool false) ] ++
      exitFlags.map (fun l => declInit (exitPendingVar l) boolTy (litBool false))
    else []
  /-- Wrap the lowered body statements in the `$exnexit` block (for non-throwing
      procedures there is no trailing result construction). -/
  wrapExit (stmts : List StmtExprMd) : List StmtExprMd := [blockOf stmts (some exnExitLabel)]

public section

/-- Number of `throw` and `try` nodes left in `proc`'s body and postconditions —
    the part of the erasure invariant three downstream passes rely on.

    Zero is the invariant this pass establishes, and three downstream passes rely on
    it — `LaurelToCoreSchemaPass` reports a `strata-bug` for a `Throw`/`Try` it
    meets, and `HeapParameterization` and `LiftImperativeExpressions` document those
    nodes as unreachable. Measuring it makes the invariant checkable instead of
    assumed: the transform below reports a `strata-bug` at the offending procedure
    when the count is not zero (so a future `lowerStmt` arm that forgets to recurse
    fails at this pass rather than far downstream), and
    `UnitTests/EliminateExceptionsErasureTest.lean` pins it over a construct-heavy
    program.

    A `throwsOn` case's guard and frame targets are deliberately *not* counted:
    this pass leaves them on the procedure for `ModifiesClauses` to lower after heap
    parameterization. Its postconditions are counted, since this pass does clear
    those. -/
def exceptionalBodyNodeCount (proc : Procedure) : Nat :=
  let inBody (b : StmtExprMd) : Nat :=
    foldStmtExpr (fun n acc =>
      match n.val with
      | .Throw _ | .Try .. => acc + 1
      | _ => acc) 0 b
  let posts (ps : List Condition) : Nat := (ps.map (fun p => inBody p.condition)).foldl (· + ·) 0
  match proc.body with
  | .Transparent b => inBody b
  | .Opaque ps impl _ => posts ps + (impl.map inBody).getD 0
  | .Abstract ps => posts ps
  | .External => 0

/-- `exceptionalBodyNodeCount` plus the parts of the exceptional contract this pass
    consumes: the declared `throws` type, the name it bound for the thrown value,
    and each `throwsOn` case's postconditions. The cases' guards and frame targets
    survive this pass by design, so they are not counted. -/
def exceptionalNodeCount (proc : Procedure) : Nat :=
  exceptionalBodyNodeCount proc + (if proc.throwsType.isSome then 1 else 0)
    + (if proc.throwsBinding.isSome then 1 else 0)
    + (proc.throwsOn.map (·.postconditions.length)).foldl (· + ·) 0

/-- Transform a program by eliminating the exceptional channel from all static
    procedures. -/
def eliminateExceptionsTransform (model : SemanticModel) (program : Program)
    : Program × List Message :=
  let init : EState := { model, lattice := TypeLattice.ofTypes program.types }
  let (procs, st) := (program.staticProcedures.mapM lowerProc).run init
  -- Backstop for the erasure invariant (see `exceptionalNodeCount`): a leftover
  -- `throw`/`try` or exceptional clause is a bug in *this* pass, so report it here
  -- rather than let a downstream pass trip over it with no indication of which
  -- `lowerStmt` arm failed to recurse.
  --
  -- Measured against the procedure as it came in. A clause on a procedure with no
  -- `throws` type is a *user* error (resolution reports it, and this pass leaves
  -- such a procedure alone), so only the `throw`/`try` nodes are required to be gone
  -- there; everything else is this pass's responsibility.
  let leftovers : List Message :=
    (program.staticProcedures.zip procs).filterMap fun (before, after) =>
      -- Skip a procedure this pass deliberately declined to lower: it still carries
      -- its exceptional constructs by design, and it has already been reported.
      if st.rejected.contains after.name.text then none else
      let n := if before.throwsType.isSome then exceptionalNodeCount after
               else exceptionalBodyNodeCount after
      if n == 0 then none
      else some (diagnosticFromSource after.name.source
        s!"internal error: 'EliminateExceptions' left {n} exceptional construct(s) in procedure '{after.name.text}'; every `throw`/`try` and `throws`/`throwsOn` clause must be lowered by this pass"
        MessageKind.strataBug)
  -- Inject the `Result` datatype (the lowering target) only when the program
  -- actually uses exceptions — a `throws` procedure, a `throw`, or a call to a
  -- throwing procedure — so a program that never throws does not carry it. This
  -- is why `Result` is not in the always-on prelude (`coreDefinitionsForLaurel`)
  -- but in `resultDefinitions`, which only this pass prepends.
  let usesExceptions := program.staticProcedures.any
    (fun p => p.throwsType.isSome || bodyHasExn model p)
  let types' := if usesExceptions then resultDefinitions.types ++ program.types else program.types
  ({ program with staticProcedures := procs, types := types' }, st.diags ++ leftovers)

end -- public section

/-- Pipeline pass: eliminate exceptions. -/
public def eliminateExceptionsPass : LoweringPass where
  name := "EliminateExceptions"
  needsResolves := true
  documentation := "Lowers the exceptional channel (throw, try/catch/finally, throws/throwsOn) into ordinary Laurel: labeled blocks, exits, and Result datatype construction. A `throws T` procedure returns a single `Result<Val, T>`; the in-flight exception rides in $thrown and a per-try `$exc_<i>` typed at that try's least-common-ancestor exception type, and the result is assembled after the body. Exception contracts become ordinary postconditions over $result. After this pass no Throw/Try remains and the throws type and the cases' postconditions are gone (each case's guard and frame targets are left for ModifiesClauses, which builds the per-case frames and the exhaustiveness claim)."
  -- The two `return`-related constraints and the `contractPass` one are declared
  -- rather than left to the pipeline comment because violating them fails *silently*:
  -- a `return` that this pass never intercepted would skip its `finally` arm, and an
  -- exceptional contract lowered after `contractPass` would be dropped, making every
  -- `throwsOn` case pass vacuously. Neither trips the post-pass re-resolve gate, so
  -- `orderingRespected` is the only thing that can catch a reordering.
  comesBefore := [⟨heapParameterizationPass.meta,
    "types `$exc_<i>` at each try's least-common-ancestor exception type, which heap parameterization erases to `Composite`; so it must run first"⟩,
    ⟨eliminateReturnStatementsPass.meta,
    "intercepts `return` to run the enclosing `finally` arms before leaving the procedure; once returns are eliminated there is no `return` left to intercept, and the arm would be skipped silently"⟩,
    ⟨contractPass.meta,
    "rewrites the exceptional contract into ordinary postconditions over `$result`, which `contractPass` then lowers; running after it would drop those postconditions and make every `throwsOn` case vacuous"⟩]
  comesAfter := [⟨eliminateValueInReturnsPass.meta,
    "assembles the single `Result` output from the named value output, so `return <value>` payloads must already have been rewritten into assignments"⟩]
  run := fun _ p m =>
    let (p', diags) := eliminateExceptionsTransform m p
    (p', diags, {})

end Laurel
