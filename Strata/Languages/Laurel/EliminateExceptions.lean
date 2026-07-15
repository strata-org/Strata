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
import Strata.Util.Tactics

/-!
# Eliminate Exceptions (E7)

A Laurel-to-Laurel pass that lowers the exceptional channel — `throw`, `try` /
`catch` / `finally`, and the `throws` / `onThrow` / `when C throws` procedure
contract — into ordinary Laurel (labeled `Block`s, `Exit`s, assignments, and
`Result` datatype construction). After this pass no `Throw`/`Try` statements and
no `throwsType`/`onThrow`/`onThrows` clauses remain, so the final
`LaurelToCoreTranslator` never needs to know about exceptions.

This mirrors the encoding that used to live inside the translator, but expressed
one level up so the transformation is reviewable as Laurel before/after (see the
`EliminateExceptions` reviewability test).

## Encoding

A procedure that declares `throws` returns a single `Result<Val, Composite>`
output (`$result`). While the body runs, the in-flight exception is tracked by
two synthesized locals, `$thrown : bool` and `$exc : Composite`; `$returning`
tracks a `return` unwinding out of enclosing `try` blocks so their `finally`
arms run (F18). All synthesized names are `$`-prefixed, outside the user
namespace.

- `throw v`  →  `$exc := v; $thrown := true; exit <nearest try | $exnexit>`.
- `try B catch eᵢ when Pᵢ { Hᵢ } … finally { F }`  →  two nested labeled blocks
  `block $tryfin { block $try { B } <catch chain> } F <re-dispatch>` so `finally`
  runs on every exit edge (the catch binding is substituted by `$exc`).
- a call to a `throws` procedure  →  bind its `Result` to a temp, then `if
  isBad(tmp) then propagate else unwrap value(tmp)`.
- the body is wrapped in `block $exnexit { … }`; after it, `$result` is built
  (`Bad($exc)` if thrown, else `Good(val)`).
- `ensures P`  →  Good-path `isGood($result) ==> P[out := value($result)]`;
  each `onThrow (e) Q`  →  `isBad($result) ==> Q[e := err($result)]`; each
  `when C throws (e) P`  →  `C ==> (isBad($result) ∧ P[e := err($result)])`.

Runs last (after heap parameterization, so exceptions are heap `Composite`
references and `is`-tests are already lowered) and needs a re-resolve so the
synthesized locals get uniqueIds.
-/

namespace Strata.Laurel

/-! ### Synthesized names -/

/-- Synthesized local: `true` once an exception is in flight. -/
private def exnThrownVar : String := "$thrown"
/-- Synthesized local: the in-flight exception value (a heap `Composite`). -/
private def exnExcVar : String := "$exc"
/-- Synthesized local (F18): `true` once a `return` is unwinding through
    enclosing `try` blocks so their `finally` arms run. -/
private def exnReturningVar : String := "$returning"
/-- Synthesized output of a throwing procedure: its `Result<Val, Composite>`. -/
private def exnResultVar : String := "$result"
/-- Label of the block a `throw`/`return` exits to leave the body region; the
    `Result` construction is placed immediately after this block. Distinct from
    the translator's `$body` label (which it auto-wraps around every body). -/
private def exnExitLabel : String := "$exnexit"

/-- The generic result datatype's name (from `exceptionDefinitionsForLaurel`). -/
private def resultDatatypeName : String := "Result"
/-- The heap composite reference datatype name (from the heap prelude). -/
private def compositeTypeName : String := "Composite"

/-! ### Laurel AST constructors (synthesized nodes carry no source) -/

private def nn (e : StmtExpr) : StmtExprMd := ⟨e, none⟩
private def tyNode (t : HighType) : HighTypeMd := ⟨t, none⟩
private def boolTy : HighTypeMd := tyNode .TBool
private def compositeTy : HighTypeMd := tyNode (.UserDefined (mkId compositeTypeName))
private def resultTyOf (valTy : HighTypeMd) : HighTypeMd :=
  tyNode (.Applied (tyNode (.UserDefined (mkId resultDatatypeName))) [valTy, compositeTy])

private def litBool (b : Bool) : StmtExprMd := nn (.LiteralBool b)
private def localRef (name : String) : StmtExprMd := nn (.Var (.Local (mkId name)))
/-- Assignment to an existing local. -/
private def setLocal (name : String) (val : StmtExprMd) : StmtExprMd :=
  nn (.Assign [⟨.Local (mkId name), none⟩] val)
/-- Variable declaration without an initializer (standalone statement). -/
private def declNoInit (name : String) (ty : HighTypeMd) : StmtExprMd :=
  nn (.Var (.Declare ⟨mkId name, ty⟩))
/-- Variable declaration with an initializer. -/
private def declInit (name : String) (ty : HighTypeMd) (val : StmtExprMd) : StmtExprMd :=
  nn (.Assign [⟨.Declare ⟨mkId name, ty⟩, none⟩] val)
private def callStatic (name : String) (args : List StmtExprMd) : StmtExprMd :=
  nn (.StaticCall (mkId name) args)
/-- `Ctor(arg)` / `Datatype..fn(arg)` — a single-argument datatype op. -/
private def resultApp (fn : String) (arg : StmtExprMd) : StmtExprMd := callStatic fn [arg]
private def exitTo (label : String) : StmtExprMd := nn (.Exit label)
private def blockOf (stmts : List StmtExprMd) (label : Option String := none) : StmtExprMd :=
  nn (.Block stmts label)
private def iteOf (c t : StmtExprMd) (e : Option StmtExprMd) : StmtExprMd :=
  nn (.IfThenElse c t e)
private def impliesOf (a b : StmtExprMd) : StmtExprMd := nn (.PrimitiveOp .Implies [a, b])
private def andOf (a b : StmtExprMd) : StmtExprMd := nn (.PrimitiveOp .And [a, b])

/-- Attach a source range to a (synthesized) node so verification-condition
    diagnostics point at the originating clause rather than at nowhere. -/
private def withSrc (src : Option FileRange) (e : StmtExprMd) : StmtExprMd := { e with source := src }

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
    inout, notably not the heap `$heap`). -/
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
  diags : List DiagnosticModel := []
  model : SemanticModel

private abbrev EM := StateM EState

private def freshNat : EM Nat := modifyGet (fun s => (s.nextId, { s with nextId := s.nextId + 1 }))
private def markUsedExc : EM Unit := modify (fun s => { s with usedExc := true })
private def emitDiag (d : DiagnosticModel) : EM Unit := modify (fun s => { s with diags := s.diags ++ [d] })

/-- Per-procedure lowering context. -/
private structure Ctx where
  /-- Whether the enclosing procedure declares `throws`. -/
  procThrows : Bool
  /-- Enclosing `try` exit targets, innermost first: `(throwTarget, finallyTarget)`.
      A `throw` exits to the head's `throwTarget`; a `return` to its
      `finallyTarget`. Empty ⇒ both fall back to `$exnexit` (leave the body). -/
  tryStack : List (String × String)

private def throwTargetOf (ctx : Ctx) : String := (ctx.tryStack.head?.map Prod.fst).getD exnExitLabel
private def finallyTargetOf (ctx : Ctx) : String := (ctx.tryStack.head?.map Prod.snd).getD exnExitLabel

/-! ### Statement lowering -/

mutual

/-- Lower a list of statements, concatenating the (possibly expanded) results.
    Statements after an unconditional terminator (`throw`/`return`/`exit`, which
    all lower to an `exit`) are unreachable and dropped, so re-resolution does
    not flag dead code after the synthesized `exit`. -/
private partial def lowerStmts (ctx : Ctx) (stmts : List StmtExprMd) : EM (List StmtExprMd) := do
  let mut acc : List StmtExprMd := []
  for s in stmts do
    acc := acc ++ (← lowerStmt ctx s)
    match s.val with
    | .Throw _ | .Return _ | .Exit _ => break
    | _ => pure ()
  pure acc

/-- Lower a single statement into a list of exception-free statements. -/
private partial def lowerStmt (ctx : Ctx) (stmt : StmtExprMd) : EM (List StmtExprMd) := do
  let src := stmt.source
  match stmt.val with
  | .Block stmts label =>
      let stmts' ← lowerStmts ctx stmts
      pure [⟨.Block stmts' label, src⟩]
  | .IfThenElse c t e =>
      let t' ← lowerStmt ctx t
      let e' ← match e with
        | some eb => do pure (some (blockOf (← lowerStmt ctx eb)))
        | none => pure none
      pure [⟨.IfThenElse c (blockOf t') e', src⟩]
  | .While c invs dec body =>
      let body' ← lowerStmt ctx body
      pure [⟨.While c invs dec (blockOf body'), src⟩]
  | .Throw value =>
      markUsedExc
      pure [ setLocal exnExcVar value,
             setLocal exnThrownVar (litBool true),
             exitTo (throwTargetOf ctx) ]
  | .Return _ =>
      -- Value payloads were removed by EliminateValueInReturns, so this is a
      -- valueless return. Route it so that any enclosing `finally` runs (F18),
      -- else jump to `$exnexit` to build the result / leave the body.
      markUsedExc
      match ctx.tryStack.head? with
      | none => pure [exitTo exnExitLabel]
      | some (_, finTarget) =>
          pure [ setLocal exnReturningVar (litBool true), exitTo finTarget ]
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

/-- Lower a `try`/`catch`/`finally` into two nested labeled blocks plus the
    `finally` arm and a re-dispatch that keeps a pending throw/return unwinding. -/
private partial def lowerTry (ctx : Ctx) (src : Option FileRange)
    (body : StmtExprMd) (catches : List CatchClause) (finally? : Option StmtExprMd)
    : EM (List StmtExprMd) := do
  markUsedExc
  let saved := ctx.tryStack
  let tryId ← freshNat
  let tryLbl := s!"$try_{tryId}"
  let tryFinLbl := s!"$tryfin_{tryId}"
  -- Body phase: a `throw` enters the catch chain ($try); a `return` runs
  -- `finally` first ($tryfin).
  let bStmts ← lowerStmt { ctx with tryStack := (tryLbl, tryFinLbl) :: saved } body
  -- Catch phase: a re-`throw` or `return` in a handler skips the (remaining)
  -- catch chain but still runs `finally` ($tryfin).
  let catchCtx : Ctx := { ctx with tryStack := (tryFinLbl, tryFinLbl) :: saved }
  let clauses ← catches.mapM (fun c => do
    -- The guard reads the shared `$exc` directly: it is evaluated at dispatch
    -- time, before the handler runs, so no nested throw has clobbered it yet.
    let pExpr := match c.predicate with
      | some p => substLocal c.binding.text (localRef exnExcVar) p
      | none => litBool true
    let hStmts ← lowerStmt catchCtx c.body
    -- Snapshot the caught exception into a fresh per-handler local when the
    -- handler references its binding. A `throw`/throwing-call *inside* this
    -- handler that is itself caught (e.g. a nested `try`/`catch`) overwrites the
    -- shared `$exc`; without the snapshot a later use of this handler's binding
    -- would read that inner exception instead. Skipped when the binding is
    -- unused, to avoid an inert local in the common case.
    let (bindDecls, hStmts) ←
      if hStmts.any (localOccurs c.binding.text) then do
        let bid ← freshNat
        let bindLocal := s!"$exc_{c.binding.text}_{bid}"
        pure ([declInit bindLocal compositeTy (localRef exnExcVar)],
              hStmts.map (substLocal c.binding.text (localRef bindLocal)))
      else
        pure ([], hStmts)
    let guard := andOf (localRef exnThrownVar) pExpr
    let handler := setLocal exnThrownVar (litBool false) :: (bindDecls ++ hStmts)
    pure (guard, handler))
  -- First-match-wins is enforced by clearing `$thrown` on a match: once a clause
  -- fires, later `$thrown && guardⱼ` guards are false. So the chain is a *sequence*
  -- of else-less `if`s rather than a nested `if`/`else` — an else-less `if` types
  -- as void, avoiding a branch-type mismatch when a handler ends in an assignment
  -- (which Laurel types as the assigned value, not void).
  let catchChainStmts : List StmtExprMd := clauses.map (fun (g, h) => iteOf g (blockOf h) none)
  -- Finally phase: a `throw`/`return` in F targets the enclosing `try`.
  let fStmts ← match finally? with
    | some f => lowerStmt ctx f
    | none => pure []
  -- Re-dispatch: keep any pending exception/return unwinding outward.
  let thrownExit := (saved.head?.map Prod.fst).getD exnExitLabel
  let returnExit := (saved.head?.map Prod.snd).getD exnExitLabel
  let reDispatch : List StmtExprMd :=
    [ iteOf (localRef exnThrownVar) (blockOf [exitTo thrownExit]) none,
      iteOf (localRef exnReturningVar) (blockOf [exitTo returnExit]) none ]
  let tryFinBlock := blockOf (blockOf bStmts (some tryLbl) :: catchChainStmts) (some tryFinLbl)
  pure (⟨tryFinBlock.val, src⟩ :: (fStmts ++ reDispatch))

/-- Lower a call to a throwing procedure. The callee now returns its inout
    outputs (notably the heap `$heap`) *and* a `Result` value; bind the `Result`
    to a fresh temp — keeping the inout targets — then propagate on `Bad` or
    unwrap the value on `Good`.

    The original call is a (possibly multi-target) assignment whose targets align
    positionally with the callee's original outputs. The inout targets are kept
    in place; the single value target is replaced by the fresh `$callres` and
    unwrapped on the Good path. This matches the callee's new output order
    (inout outputs, then the `Result`). -/
private partial def lowerThrowingCall (ctx : Ctx) (callNode : StmtExprMd)
    (targets : List VariableMd) : EM (List StmtExprMd) := do
  markUsedExc
  let model := (← get).model
  let callee := match callNode.val with
    | .StaticCall c _ => c
    | .InstanceCall _ c _ => c
    | _ => mkId "?"
  let p? := calleeProc model callee
  let valTy := p?.map valTyOf |>.getD boolTy
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
  let callresTarget : VariableMd := ⟨.Declare ⟨mkId callres, resultTyOf valTy⟩, none⟩
  let multiCall := nn (.Assign (inoutTargets ++ [callresTarget]) callNode)
  -- Propagate on `Bad` (exits the block), so the Good-path unwrap that follows is
  -- reached only when the call did not throw. An else-less `if` keeps this void.
  let propagate := iteOf (resultApp "Result..isBad" (localRef callres))
    (blockOf
      [ setLocal exnExcVar (resultApp "Result..err" (localRef callres)),
        setLocal exnThrownVar (litBool true),
        exitTo (throwTargetOf ctx) ])
    none
  -- A `Declare` value target is declared up front so it stays in scope for later
  -- statements; it is assigned the unwrapped value only on the Good path.
  let (preDecls, goodStmts) : List StmtExprMd × List StmtExprMd :=
    match valueTarget? with
    | some ⟨.Declare ⟨x, xTy⟩, _⟩ =>
        ([declNoInit x.text xTy], [setLocal x.text (resultApp "Result..value" (localRef callres))])
    | some ⟨.Local x, _⟩ =>
        ([], [setLocal x.text (resultApp "Result..value" (localRef callres))])
    | _ => ([], [])
  pure (preDecls ++ [multiCall, propagate] ++ goodStmts)

end

/-! ### Detecting whether a procedure needs the transform -/

private partial def stmtUsesExn (model : SemanticModel) (stmt : StmtExprMd) : Bool :=
  match stmt.val with
  | .Throw _ => true
  | .Try _ _ _ => true
  | .StaticCall callee _ => calleeThrows model callee
  | .InstanceCall _ callee _ => calleeThrows model callee
  | .Assign _ v => stmtUsesExn model v
  | .Block stmts _ => stmts.attach.any (fun ⟨s, _⟩ => stmtUsesExn model s)
  | .IfThenElse c t e =>
      stmtUsesExn model c || stmtUsesExn model t || (e.attach.any (fun ⟨x, _⟩ => stmtUsesExn model x))
  | .While c _ _ b => stmtUsesExn model c || stmtUsesExn model b
  | _ => false

private def bodyImpl (body : Body) : Option StmtExprMd :=
  match body with
  | .Transparent b => some b
  | .Opaque _ impl _ => impl
  | _ => none

private def bodyHasExn (model : SemanticModel) (proc : Procedure) : Bool :=
  match bodyImpl proc.body with
  | some b => stmtUsesExn model b
  | none => false

/-! ### Procedure lowering -/

/-- Existing (normal) postconditions declared on a body, if any. -/
private def bodyPostconditions (body : Body) : List Condition :=
  match body with
  | .Opaque posts _ _ => posts
  | .Abstract posts => posts
  | _ => []

/-- Lower a single procedure. Non-exceptional procedures are returned unchanged. -/
private def lowerProc (proc : Procedure) : EM Procedure := do
  let procThrows := proc.throwsType.isSome
  let model := (← get).model
  if !(procThrows || bodyHasExn model proc) then
    return proc
  modify (fun s => { s with usedExc := false })
  let ctx : Ctx := { procThrows, tryStack := [] }
  let valueOutputs := valueOutputsOf proc
  -- E7 limitation: a `throws` procedure lowers to a single `Result` value, so it
  -- can carry at most one value output.
  if procThrows && valueOutputs.length >= 2 then
    emitDiag (diagnosticFromSource proc.name.source
      s!"throwing procedure '{proc.name.text}' has {valueOutputs.length} value outputs; a procedure declaring `throws` may have at most one value output (its result is a single `Result` value). Combine the outputs (e.g. into a composite) or drop the `throws` clause."
      DiagnosticType.NotYetImplemented)
  -- Lower the implementation statements (if any).
  let loweredBody? ← match bodyImpl proc.body with
    | some b => do pure (some (← lowerStmt ctx b))
    | none => pure none
  let usedExc := (← get).usedExc
  let isBodiless := loweredBody?.isNone

  if !procThrows then
    -- Non-throwing procedure that uses the exceptional channel locally (a `try`
    -- that catches everything, or a call it handles). Keep its body kind (and
    -- thus its caller-visible transparency), just rewrite the implementation.
    let excDecls := excStateDecls (needed := usedExc)
    let assembled := blockOf (excDecls ++ wrapExit (loweredBody?.getD []))
    let newBody := match proc.body with
      | .Transparent _ => .Transparent assembled
      | .Opaque posts _ modif => .Opaque posts (some assembled) modif
      | b => b
    return { proc with body := newBody }

  -- Throwing procedure: return a single `Result`, build it after the body, and
  -- turn the exceptional contract into ordinary postconditions over `$result`.
  let valTy := valTyOf proc
  let valName? := match valueOutputs with | [o] => some o.name.text | _ => none
  let inputNames := proc.inputs.map (·.name.text)
  let inoutOutputs := proc.outputs.filter (fun o => inputNames.contains o.name.text)
  let newOutputs := inoutOutputs ++ [⟨mkId exnResultVar, resultTyOf valTy⟩]
  -- Postconditions.
  let goodWrap (p : StmtExprMd) : StmtExprMd :=
    let p' := match valName? with
      | some n => substLocal n (resultApp "Result..value" (localRef exnResultVar)) p
      | none => p
    impliesOf (resultApp "Result..isGood" (localRef exnResultVar)) p'
  let wrappedPosts := (bodyPostconditions proc.body).map (fun c =>
    { c with condition := withSrc c.condition.source (goodWrap c.condition), free := c.free || isBodiless })
  let onThrowPosts := proc.onThrow.map (fun c =>
    let p' := substLocal c.binding.text (resultApp "Result..err" (localRef exnResultVar)) c.predicate
    ({ condition := withSrc c.predicate.source (impliesOf (resultApp "Result..isBad" (localRef exnResultVar)) p')
       free := isBodiless } : Condition))
  let onThrowsPosts := proc.onThrows.map (fun c =>
    let p' := substLocal c.binding.text (resultApp "Result..err" (localRef exnResultVar)) c.postcondition
    let conj := andOf (resultApp "Result..isBad" (localRef exnResultVar)) p'
    ({ condition := withSrc c.condition.source (impliesOf c.condition conj), free := isBodiless } : Condition))
  -- Exceptional frame (`onThrow modifies …`): a two-state frame axiom guarded by
  -- `Result..isBad($result)`, so on the throwing path only the listed locations
  -- may change. Built here (not in `ModifiesClauses`, which runs earlier) because
  -- `$result` only exists after this pass. Emitted only when the user declared an
  -- exceptional frame; otherwise the throwing path is left unconstrained (the
  -- normal `modifies` frame is already `isGood`-guarded via `goodWrap` above, so
  -- it says nothing on the Bad path). Reuses the normal frame-axiom builder.
  let onThrowModifiesPosts : List Condition :=
    if proc.onThrowModifies.isEmpty then []
    else match buildModifiesEnsures proc model proc.onThrowModifies (mkId "$heap") with
      | some frame =>
        [{ condition := withSrc proc.name.source
             (impliesOf (resultApp "Result..isBad" (localRef exnResultVar)) frame)
           free := isBodiless }]
      | none => []
  let allPosts := wrappedPosts ++ onThrowPosts ++ onThrowsPosts ++ onThrowModifiesPosts
  -- Body assembly (only when there is an implementation).
  let goodArg := match valName? with | some n => localRef n | none => litBool true
  let construct := iteOf (localRef exnThrownVar)
    (blockOf [setLocal exnResultVar (resultApp "Bad" (localRef exnExcVar))])
    (some (blockOf [setLocal exnResultVar (resultApp "Good" goodArg)]))
  let assembledBody? : Option StmtExprMd := loweredBody?.map (fun bstmts =>
    let excDecls := excStateDecls (needed := true)
    let valDecl := match valName? with | some n => [declNoInit n valTy] | none => []
    blockOf (excDecls ++ valDecl ++ [blockOf bstmts (some exnExitLabel), construct]))
  let origModif := match proc.body with | .Opaque _ _ m => m | _ => []
  let newBody := match proc.body with
    | .Abstract _ => .Abstract allPosts
    | _ => .Opaque allPosts assembledBody? origModif
  return { proc with
    outputs := newOutputs
    body := newBody
    throwsType := none
    onThrow := []
    onThrows := []
    onThrowModifies := [] }
where
  /-- The `$thrown`/`$exc`/`$returning` declarations, emitted when the body uses
      the exceptional channel. -/
  excStateDecls (needed : Bool) : List StmtExprMd :=
    if needed then
      [ declInit exnThrownVar boolTy (litBool false),
        declNoInit exnExcVar compositeTy,
        declInit exnReturningVar boolTy (litBool false) ]
    else []
  /-- Wrap the lowered body statements in the `$exnexit` block (for non-throwing
      procedures there is no trailing result construction). -/
  wrapExit (stmts : List StmtExprMd) : List StmtExprMd := [blockOf stmts (some exnExitLabel)]

public section

/-- Transform a program by eliminating the exceptional channel from all static
    procedures. -/
def eliminateExceptionsTransform (model : SemanticModel) (program : Program)
    : Program × List DiagnosticModel :=
  let init : EState := { model }
  let (procs, st) := (program.staticProcedures.mapM lowerProc).run init
  ({ program with staticProcedures := procs }, st.diags)

end -- public section

/-- Pipeline pass: eliminate exceptions (E7). -/
public def eliminateExceptionsPass : LaurelPass where
  name := "EliminateExceptions"
  needsResolves := true
  documentation := "Lowers the exceptional channel (throw, try/catch/finally, throws/onThrow/when-throws) into ordinary Laurel: labeled blocks, exits, and Result datatype construction. A throwing procedure returns a single Result<Val, Composite>; the in-flight exception rides in synthesized $thrown/$exc locals and the result is assembled after the body. Exception contracts become ordinary postconditions over $result. After this pass no Throw/Try or throws/onThrow clauses remain."
  run := fun p m =>
    let (p', diags) := eliminateExceptionsTransform m p
    (p', diags, {})

end Laurel
