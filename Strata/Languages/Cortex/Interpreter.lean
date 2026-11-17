/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Cortex.Heap
public import Strata.Languages.Cortex.Module
public import Strata.Languages.Cortex.TypeCheck
public import Strata.Languages.Cortex.Pipeline
public import Strata.Languages.Cortex.LowerDispatch
public import Strata.Languages.Cortex.LowerExceptions
public import Strata.Languages.Cortex.LowerComposites
public import Strata.Languages.Cortex.FieldCasts
public import Strata.Languages.Cortex.LowerHeapExec
public import Strata.Languages.Cortex.LowerGlobals
public import Strata.Languages.Cortex.LowerCTE
public import Strata.Languages.Core.Factory
public import Strata.Languages.Core.Program
public import Strata.Languages.Core.Interpreter
public import Strata.Languages.Core.StatementSemantics
public import Strata.DL.Imperative.InterpreterCall

namespace Cortex.Interp

open Lambda
open Imperative (Cmd InterpLang InterpEffects IStore IEnv ICFGConfig IEvent REvent REventArg
  stepBaseCmdStore HasBool HasFvar HasOldIdent CallArg CmdDefs ProcedureHeader)
open Imperative.Calls (CmdView stepCmdWith)

public section

abbrev LFactory := Lambda.Factory Core.CoreLParams

abbrev CortexExpression : Imperative.PureExpr := Core.Expression

@[expose] def exprFuel : Nat := 1000

@[expose] def isRefTy (prog : UnorderedProgram) (ty : Core.Expression.Ty) : Bool :=
  match (ty : LTy) with
  | .forAll [] (.tcons n []) => n.startsWith "$Any" || (prog.findComposite? n).isSome
  | _ => false

abbrev Store := IStore CortexExpression
abbrev Env := IEnv CortexExpression
abbrev Event := IEvent CortexExpression
abbrev EventArg := REventArg CortexExpression LFactory
abbrev Trace := List Event
abbrev Config := ICFGConfig Label IRCmd CortexExpression

@[expose] def Store.empty : Store := IStore.ofStore fun _ => none

structure Hdr where
  name : String
  inputs : List Core.Expression.Ident
  outputs : List Core.Expression.Ident
  deriving DecidableEq, Inhabited

instance : ProcedureHeader CortexExpression Hdr where
  name h := ⟨h.name, ()⟩
  inputParams h := h.inputs
  outputParams h := h.outputs

abbrev IProcedure := Imperative.Procedure CortexExpression IRCmd Hdr

instance : CmdDefs CortexExpression IRCmd where
  defs
    | .cmd (.init x _ _ _) => [x]
    | _ => []

inductive StopReason where
  | engine (reason : Imperative.StopReason)
  | lowering (msg : String)
  | typeError (msg : String)
  | notLowered (what : String)
  | exceptionsUnsupported
  | inoutArgumentMismatch (name : ProcName)
  | procedureWithoutBody (name : ProcName)
  | callWithoutBody (name : ProcName)
  | invalidDatatypes (msg : String)
  /-- A stop that a frontend placed where it has no model (`stopSummary?`). -/
  | stop (summary : String)
  | at (md : MD) (r : StopReason)
  deriving Repr, Inhabited

@[expose] def StopReason.locate (md : MD) : StopReason → StopReason
  | r@(.at m inner) => if (Imperative.getFileRange m).isSome then r else .at md inner
  | r => .at md r

/-- The kinds of stop, each the start of a stop's summary, `<kind>: <detail>`. -/
def stopKinds : List String :=
  ["unsupported", "no-model", "implementation-defined", "dangling-reference", "resource-limit"]

/-- The summary of the stop that an assertion or precondition `e` at `md` is: the literal `false` with a summary
that starts with a kind of stop. Any other `assert false` is an ordinary check, as Strata's exception lowerings use
it for an uncaught exception. -/
@[expose] def stopSummary? (e : Expr) (md : MD) : Option String :=
  if Core.eraseLocs e = HasBool.ff (P := Core.Expression) then
    md.getPropertySummary.filter fun s => stopKinds.any fun k => s.startsWith s!"{k}: "
  else none

variable {m : Type → Type} [Monad m] [InterpEffects CortexExpression m]
  [MonadExcept Imperative.StopReason m] [MonadExceptOf StopReason m]

@[expose] def stop {α : Type} (r : Imperative.StopReason) : m α := throw r

@[expose] def evalExpr (fuel : Nat) (f : LFactory) (σ : Store) (e : Expr) : m Expr :=
  match InterpLang.boundedEval (P := CortexExpression) fuel f σ.get e with
  | some v => pure v
  | none => stop .expressionDidNotEvaluate

@[expose] def setVar (σ : Store) (x : Core.Expression.Ident) (v : Expr) : m Store :=
  if (σ.get x).isSome then pure (σ.update x v)
  else stop .programSetTargetUndefined

@[expose] def chooseTyped (f : LFactory) (σ : Store) (ty : Core.Expression.Ty) : m Expr :=
  InterpEffects.choose (P := CortexExpression) f σ.get ty

@[expose] def stepBase (fuel : Nat) (f : LFactory) (σ : Store) (c : Cmd Core.Expression) : m Store :=
  stepBaseCmdStore (P := CortexExpression) fuel f σ c

def datatypeDefault (prog : UnorderedProgram) (n : String) : Option Expr :=
  if n == LowerComposites.compositeTy then (LowerHeapExec.defaultOf prog (.forAll [] (.tcons n []))).toOption else
  prog.datatypes.find? (·.name == n) >>= fun d =>
    if d.typeArgs.isEmpty then
      (d.constrs.find? (·.args.isEmpty)).map fun c => (constrFunc (T := Core.CoreLParams) c d).opExpr
    else none

def defaultValue (prog : UnorderedProgram) (_f : LFactory) (ty : Core.Expression.Ty) (_n : Nat) : Option Expr :=
  match (ty : LTy) with
  | .forAll [] (.tcons "int" []) => some (.const Core.valueLoc (.intConst 0) : Core.Expression.Expr)
  | .forAll [] (.tcons "bool" []) => some (.const Core.valueLoc (.boolConst false) : Core.Expression.Expr)
  | .forAll [] (.tcons "string" []) => some (.const Core.valueLoc (.strConst "") : Core.Expression.Expr)
  | .forAll [] (.tcons "real" []) => some (.const Core.valueLoc (.rationalConst 0) : Core.Expression.Expr)
  | .forAll [] (.bitvec n) => some (.const Core.valueLoc (.bitvecConst n 0) : Core.Expression.Expr)
  | t@(.forAll [] (.tcons n [])) =>
    if isRefTy prog t then some (.const Core.valueLoc (.intConst (-1)) : Core.Expression.Expr)
    else datatypeDefault prog n
  | _ => none

@[expose] def extCmd (fuel : Nat) (f : LFactory) (σ : Store) : IRCmd → m Store
  | .cast x _ e _ _ => do
    setVar σ x (← evalExpr fuel f σ e)
  | .new .. => throwThe StopReason (.notLowered "new")
  | .readField .. => throwThe StopReason (.notLowered "readField")
  | .writeField .. => throwThe StopReason (.notLowered "writeField")
  | .instanceOf .. => throwThe StopReason (.notLowered "instanceOf")
  | .newArray .. => throwThe StopReason (.notLowered "newArray")
  | .readElem .. => throwThe StopReason (.notLowered "readElem")
  | .writeElem .. => throwThe StopReason (.notLowered "writeElem")
  | .arrayLength .. => throwThe StopReason (.notLowered "arrayLength")
  | .instanceOfComponent .. => throwThe StopReason (.notLowered "instanceOfComponent")
  | _ => pure σ

@[expose] def callArgs (p : Procedure) (lhs : List Core.Expression.Ident)
    (args : List Expr) : Option (List (CallArg CortexExpression)) :=
  let ins := p.inputs.map Prod.fst
  let outs := p.outputs.map Prod.fst
  if ins.length != args.length || outs.length != lhs.length then none
  else merge (ins.zip args) (outs.zip lhs)
where
  merge : List (Core.Expression.Ident × Expr) → List (Core.Expression.Ident × Core.Expression.Ident) →
      Option (List (CallArg CortexExpression))
    | [], os => some (os.map fun (_, x) => .outArg x)
    | (n, a) :: is, os =>
      match os.findIdx? (·.1 == n) with
      | some j =>
        match os.drop j, a with
        | (_, x) :: after, .fvar _ y _ =>
          if x == y then
            (merge is after).map fun rest =>
              ((os.take j).map fun (_, z) => CallArg.outArg (P := CortexExpression) z) ++
                [CallArg.inoutArg (P := CortexExpression) x] ++ rest
          else none
        | _, _ => none
      | none => (merge is os).map (CallArg.inArg (P := CortexExpression) a :: ·)

/-- Whether a call to `p` fails the run at once: `p` has no body to run, and no precondition of it marks a stop. -/
@[expose] def callsWithoutBody (p : Procedure) : Bool :=
  p.body.isNone && (p.requires.findSome? fun pre => stopSummary? pre.cond pre.md).isNone

@[expose] def view (prog : UnorderedProgram) : IRCmd → CmdView CortexExpression IRCmd Hdr m
  | .cmd c =>
    -- A stop ends the run here, rather than continuing on values a frontend invented.
    match c with
    | .assert _ e md => match stopSummary? e md with
      | some s => .ext fun _ _ => throwThe StopReason (.stop s)
      | none => .base c
    | _ => .base c
  | .call lhs n args md =>
    match prog.findProcedure? n with
    | none => .call n (args.map (CallArg.inArg (P := CortexExpression)) ++
        lhs.map (CallArg.outArg (P := CortexExpression))) md some
    | some p =>
      if callsWithoutBody p then .ext fun _ _ => throwThe StopReason (.callWithoutBody n) else
      match callArgs p lhs args with
      | some cas => .call n cas md some
      | none => .ext fun _ _ => throwThe StopReason (.inoutArgumentMismatch n)
  | .virtualCall .. => .ext fun _ _ => throwThe StopReason (.notLowered "virtualCall")
  | .throw _ _ => .ext fun _ _ => throwThe StopReason .exceptionsUnsupported
  | c => .ext fun fuel env => do
    pure (.done (← extCmd fuel env.factory env.store c))

@[expose] def calleeTable (prog : UnorderedProgram) (n : String) : Option IProcedure :=
  (prog.findProcedure? n).map fun p =>
    let body := (p.body.getD { cfg := { entry := "$none", blocks := [] }, handlers := [] }).cfg
    -- A call checks the callee's other preconditions, then stops at its first command, without running the callee.
    let body := match p.requires.findSome? (fun pre => stopSummary? pre.cond pre.md) with
      | none => body
      | some s =>
        let entry := freshLabel "$stop" (body.blocks.map (·.1))
        let marker : Cortex.LBlock :=
          { cmds := [.cmd (.assert "$stop" HasBool.ff ((.empty : MD).withPropertySummary s))],
            transfer := .goto body.entry }
        { entry, blocks := (entry, marker) :: body.blocks }
    { header := { name := p.name, inputs := p.inputs.map Prod.fst,
                  outputs := p.outputs.map Prod.fst }
      spec := { preconditions := ListMap.ofList ((p.requires.zipIdx.filter fun (pre, _) =>
                    (stopSummary? pre.cond pre.md).isNone).map fun (pre, i) =>
                  (s!"requires_{i}", ({ expr := pre.cond, md := pre.md } : Imperative.Check CortexExpression)))
                postconditions := ListMap.ofList [] }
      body := .cfg body false }

@[expose] def locatedAt {α : Type} (md : MD) (x : m α) : m α :=
  tryCatchThe StopReason x fun e => throwThe StopReason (e.locate md)

@[expose] def stepper (prog : UnorderedProgram) :
    Imperative.StepCmdM CortexExpression IRCmd m :=
  fun fuel env c =>
    locatedAt (IRCmd.md c) (stepCmdWith (view prog) (fun c x => locatedAt (IRCmd.md c) x)
      (calleeTable prog) .execute Imperative.defaultMaxCallDepth fuel env c)

/-- The first source location the run reaches from `cmds` and then `tr`: the passes that lower a program add commands
and jumps without one, as the prologue of an entry, which runs before its first command. A jump without a location
to one block is followed there, at most `n` blocks deep. -/
@[expose] def firstLocated (g : Cortex.LCFG) :
    Nat → List IRCmd → Imperative.DetTransferCmd Label Core.Expression → MD
  | n, cmds, tr =>
    match cmds.find? (fun c => (Imperative.getFileRange (IRCmd.md c)).isSome) with
    | some c => IRCmd.md c
    | none =>
      match n, tr with
      | n + 1, .condGoto _ lt lf md =>
        if (Imperative.getFileRange md).isNone && lt == lf then
          match List.lookup lt g.blocks with
          | some blk => firstLocated g n blk.cmds blk.transfer
          | none => md
        else md
      | _, .condGoto _ _ _ md | _, .finish md => md

/-- Where the run in `c` goes on: its next command, or its block's transfer, the first of them with a source
location. -/
@[expose] def nextMd : Config → MD
  | .atBlock g t _ =>
    match List.lookup t g.blocks with
    | some blk => firstLocated g g.blocks.length blk.cmds blk.transfer
    | none => .empty
  | .inBlock g _ cmds tr _ => firstLocated g g.blocks.length cmds tr
  | .terminal _ => .empty

@[expose] def runCFG (step : Imperative.StepCmdStoreM CortexExpression IRCmd m) :
    Nat → Config → m Config
  | fuel, cfgc =>
    match cfgc with
    | .terminal _ => pure cfgc
    | _ =>
      match fuel with
      -- Out of fuel: the stop is where the run would have gone on; in a callee, which Core's call rule runs, the call.
      | 0 => locatedAt (nextMd cfgc) (throw .replayFuelExhausted)
      | fuel + 1 => do
        let next ← match cfgc with
          | .inBlock _ _ [] (.condGoto _ _ _ md) _ =>
            locatedAt md (Imperative.stepInterpCFG step (fuel + 1) cfgc)
          | _ => Imperative.stepInterpCFG step (fuel + 1) cfgc
        runCFG step fuel next

abbrev Oracle := LFactory → Core.Expression.Ty → Nat → Option Expr

structure HostState where
  trace : Array Event := #[]
  choices : Nat := 0

abbrev HostM := ReaderT Oracle (ExceptT StopReason (StateM HostState))

instance : MonadExceptOf Imperative.StopReason HostM where
  throw r := throwThe StopReason (.engine r)
  tryCatch x h := tryCatchThe StopReason x fun e =>
    match e with
    | .engine r => h r
    | e => throwThe StopReason e

instance : InterpEffects CortexExpression HostM where
  choose rf _ ty := do
    let oracle ← read
    let n ← modifyGetThe HostState fun st => (st.choices, { st with choices := st.choices + 1 })
    match oracle rf ty n with
    | some v =>
      let ops := InterpLang.ops (P := CortexExpression)
      if ops.isValue rf v && ops.hasType rf v ty then pure v
      else throwThe Imperative.StopReason .illTypedValue
    | none => throwThe Imperative.StopReason .oracleExhausted
  emit ev := modifyThe HostState fun st => { st with trace := st.trace.push ev }

structure RunResult where
  final : Config
  trace : Trace

def programFactory (prog : UnorderedProgram) : Except Strata.Message LFactory := do
  let F ← prog.datatypes.foldlM (init := Core.Factory) fun F d => do
    let bf ← Lambda.genBlockFactory (T := Core.CoreLParams) [d]
    Lambda.Factory.addFactory F bf
  Lambda.Factory.addFactory F (Lambda.Factory.ofArray prog.functions.toArray)

def isEntry (p : Procedure) : Bool :=
  match p.md.findElem Imperative.MetaData.interpretEntry with
  | some { value := .switch true, .. } => true
  | _ => false

/-- The CFG an entry procedure runs: when `globalInit` is nonempty, the body's CFG with a fresh
entry block in front, which runs the `globalInit` commands and then jumps to the body's entry;
otherwise the body's CFG unchanged. -/
@[expose] def entryCfg (prog : UnorderedProgram) (body : Body) :
    Imperative.DetCFG Core.Expression IRCmd :=
  if prog.globalInit.isEmpty then body.cfg else
    let entry := freshLabel "$globalsEntry" (body.cfg.blocks.map (·.1))
    let initBlock : Cortex.LBlock :=
      { cmds := prog.globalInit.map .cmd, transfer := .goto body.cfg.entry }
    { entry := entry, blocks := (entry, initBlock) :: body.cfg.blocks }

/-- Start `p` as the program's entry: its frame has no caller to take the globals from, so
the globals are defined by running `globalInit` first, in a block in front of the body. -/
def startProc (prog : UnorderedProgram) (f : LFactory) (fuel : Nat) (p : Procedure) : HostM Config := do
  match p.body with
  | none => throwThe StopReason (.procedureWithoutBody p.name)
  | some body =>
    let outs ← (p.outputs.map Prod.snd).mapM (chooseTyped f Store.empty)
    let σ₀ := Store.empty.bindPositional (p.outputs.map Prod.fst) outs
    let g := entryCfg prog body
    runCFG (stepper prog).toStore fuel (.atBlock g g.entry { store := σ₀, factory := f })

def lower (prog : UnorderedProgram) : Except String UnorderedProgram := do
  let typed ← match ← runPasses (sharedPasses true ++ interpreterPasses) (.unordered prog) with
    | .unordered p => pure p
    | .ordered _ => throw "the shared passes gave an ordered program"
  let prog ← (LowerCTE.runWith true typed).mapError (s!"LowerCTE: {·}")
  return LowerHeapExec.eraseArrays prog

def prepare (prog : UnorderedProgram) : Except StopReason UnorderedProgram := do
  let prog ← (lower prog).mapError StopReason.lowering
  (TypeCheck.run prog).mapError StopReason.typeError

/-- Run `name` of a prepared program as its entry: how the run ended, and the trace up to there, also when a stop
ended it. -/
def runPreparedTraced (prog : UnorderedProgram) (fuel : Nat) (name : ProcName) : Except StopReason Config × Trace :=
  match prog.findProcedure? name with
  | none => (.error (.procedureWithoutBody name), [])
  | some p =>
    if p.body.isNone then (.error (.procedureWithoutBody p.name), []) else
    match programFactory prog with
    | .error e => (.error (.invalidDatatypes e.message), [])
    | .ok lf =>
      let oracle : Oracle := match TypeCheck.context prog with
        | .ok C => fun lf ty n => (defaultValue prog lf ty n).map fun v =>
            (TypeCheck.annotate prog C [] v (LTy.toMonoType? (ty : LTy))).toOption.getD v
        | .error _ => defaultValue prog
      let (r, st) := (((startProc prog lf fuel p).run oracle).run).run {}
      (r, st.trace.toList)

def runPrepared (prog : UnorderedProgram) (fuel : Nat) (name : ProcName) : Except StopReason RunResult :=
  match runPreparedTraced prog fuel name with
  | (.ok c, trace) => .ok { final := c, trace }
  | (.error e, _) => .error e

def runEntry (prog : UnorderedProgram) (fuel : Nat) (p : Procedure) : Except StopReason RunResult := do
  if p.body.isNone then throw (.procedureWithoutBody p.name)
  runPrepared (← prepare prog) fuel p.name

def evalsTo (a : EventArg) (b : Bool) : Bool :=
  match InterpLang.boundedEval (P := CortexExpression) exprFuel a.factory a.store a.expr with
  | some v => InterpLang.boolLit? (P := CortexExpression) v == some b
  | none => false

def unevaluated : Trace → Nat
  | [] => 0
  | .assert a :: rest =>
    (if evalsTo a true || evalsTo a false then 0 else 1) + unevaluated rest
  | _ :: rest => unevaluated rest

def failures : Trace → List (MD × String)
  | [] => []
  | .assert a :: rest =>
    if evalsTo a false then
      ((a.metadata : MD), (((a.metadata : MD).getPropertySummary).getD "assertion")) :: failures rest
    else failures rest
  | .assume _ :: rest => failures rest
  | .cover _ :: rest => failures rest

end

end Cortex.Interp
