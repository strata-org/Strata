/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Cortex.Semantics
public import Strata.Languages.Core.Logic.LangDef

/-! # Cortex as an event-trace language

`EventLang.cortex prog` packages the Cortex relation of a program as a
`Strata.Logic.EventLang Core.Expression CEvent`, gated by `CortexInitEnvWF`, so that the
transform-specification framework (`OverapproximatesTracesUptoWhen` and its composition
lemmas) relates a Cortex pass's input and output programs.

The framework's validity notions are stated over `Event Core.Expression`. A Cortex trace
is read through the erasure `CEvent.erase`, which reads an `uncaught` event as the failing
assertion and the assumption `LowerExceptions` emits for it; `EventLang.eraseEvents` is a
Cortex language with its traces erased, and `EventLang.liftStd` a Core language with its
events lifted to `CEvent`.

## Key definitions

- `Frame`, `EventLang.cortex`, `CortexInitEnvWF`.
- `SafeStart`, `notRefTy`, `noRefOp`, `exprNoRefOps`, `Body.noRefOps`,
  `UnorderedProgram.noRefOps`: a run that starts with safe references, and the check that
  source expressions build no reference.
- `CEvent.erase`, `CEvent.liftRel`, `EventLang.eraseEvents`, `EventLang.liftStd`.
- `liftCFG`, `eraseCFG`: a CFG of base commands as a Cortex CFG, and as the relation runs
  it, with its constraint checks inserted and its types erased.
-/

namespace Cortex.Sem

open Imperative Lambda Strata.Logic

public section

/-! ## Variables of a body -/

/-- The expressions a command evaluates. -/
@[expose] def _root_.Cortex.IRCmd.exprs : IRCmd → List Expr
  | .cmd (.init _ _ (.det e) _) | .cmd (.set _ (.det e) _) => [e]
  | .cmd (.assert _ e _) | .cmd (.assume _ e _) | .cmd (.cover _ e _) => [e]
  | .cmd _ | .new .. => []
  | .readField _ o _ _ | .instanceOf _ o _ _ | .throw o _ => [o]
  | .writeField o _ v _ => [o, v]
  | .cast _ _ e _ _ => [e]
  | .newArray _ _ len _ => [len]
  | .readElem _ a i _ _ => [a, i]
  | .writeElem a i v _ _ => [a, i, v]
  | .arrayLength _ a _ => [a]
  | .instanceOfComponent _ o a _ => [o, a]
  | .call _ _ args _ | .virtualCall _ _ _ args _ => args

/-- The variables a command updates, which must be defined before it runs. -/
@[expose] def _root_.Cortex.IRCmd.updated : IRCmd → List Core.Expression.Ident
  | .cmd (.set x _ _) | .new x _ _ | .readField x _ _ _ | .instanceOf x _ _ _ => [x]
  | .cast x _ _ _ _ | .newArray x _ _ _ | .readElem x _ _ _ _ | .arrayLength x _ _ => [x]
  | .instanceOfComponent x _ _ _ => [x]
  | .call lhs .. | .virtualCall lhs .. => lhs
  | _ => []

/-- The variables a command declares. -/
@[expose] def _root_.Cortex.IRCmd.declared : IRCmd → List Core.Expression.Ident
  | .cmd (.init x ..) => [x]
  | _ => []

/-- The variables a body reads or updates. -/
@[expose] def _root_.Cortex.Body.used (b : Body) : List Core.Expression.Ident :=
  b.cfg.blocks.flatMap fun (_, blk) =>
    blk.cmds.flatMap (fun c => c.exprs.flatMap (HasFvars.getFvars (P := Core.Expression)) ++
      c.updated) ++
    match blk.transfer with
    | .condGoto e _ _ _ => HasFvars.getFvars (P := Core.Expression) e
    | .finish _ => []

/-- The variables a body declares. -/
@[expose] def _root_.Cortex.Body.declared (b : Body) : List Core.Expression.Ident :=
  b.cfg.blocks.flatMap fun (_, blk) => blk.cmds.flatMap IRCmd.declared

/-! ## Initial-environment well-formedness -/

/-- The entry of a run: a procedure body with its `throws` clause, its postconditions and
the names of its inputs and outputs. -/
structure Frame where
  body : Body
  throws : Option TypeName
  ensures : List Postcondition
  inputs : List Core.Expression.Ident
  outputs : List Core.Expression.Ident

/-- The running frame of an entry in the program context `Γ`, with the entry values `old`
its postconditions read. Its body checks the writes of the variables its `init`s give a
constrained type; a frame names its parameters without their types, so their constraints
are not checked. -/
@[expose] def Frame.toFr (Γ : UnorderedProgram) (st : Frame) (old : Store) : Fr :=
  ⟨st.body, st.throws, st.ensures, old, constrainedVars Γ [] (some st.body), []⟩

/-- Well-formedness of a Cortex run of the entry frame `fr` from `ρ` in the program
context `Γ`: the evaluator is well formed, the store holds only values, the factory is a
lawful model of the references and of the heap API, every procedure body has distinct
inputs, distinct outputs and a well-formed handler table, the entry body's handler table is
well formed, every variable the entry body uses and does not declare is defined, the store
binds each global and each parameter of a procedure whose body is the entry body only to a
value of its declared type, the store binds the heap the run starts from, a well-tagged heap,
under `$entryHeap`, and binds no other name with a reserved prefix. -/
structure CortexInitEnvWF (Γ : UnorderedProgram) (params : Core.Logic.InitEnvWFParams)
    (fr : Frame) (ρ : Imperative.Env Core.Expression) : Prop
    extends WellFormedSemanticEval (P := Core.Expression) ρ.factory where
  /-- The store holds only values. -/
  storeWellDefined : WellFormedStore ρ.store ρ.factory
  /-- The factory models `Ref` and `Tag`. -/
  refTag : RefTagModel Γ ρ.factory
  /-- The factory is a lawful model of the heap API. -/
  heapApi : HeapApiModel Γ ρ.factory
  /-- Every procedure body has distinct inputs, distinct outputs and a well-formed handler
  table. A name may be both an input and an output: it holds the argument at entry and is
  passed back. -/
  procsWF : ∀ p ∈ Γ.procedures, ∀ b, p.body = some b →
    (p.inputs.map Prod.fst).Nodup ∧ (p.outputs.map Prod.fst).Nodup ∧ b.checkHandlers Γ = .ok ()
  /-- The entry body's handler table is well formed. -/
  entryHandlers : fr.body.checkHandlers Γ = .ok ()
  /-- Every variable the entry body uses and does not declare is defined. -/
  entryReadsDefined : ∀ x ∈ fr.body.used, x ∉ fr.body.declared → (ρ.store x).isSome
  /-- The store binds each global only to a value of its declared type, read as the relation
  reads types (`eraseTy`). -/
  globalsTyped : ∀ xt ∈ Γ.globals, ∀ v, ρ.store xt.1 = some v →
    HasVal.valueOfTy (P := Core.Expression) ρ.factory v (eraseTy Γ xt.2)
  /-- The store binds each input and output of a procedure whose body is the entry body only
  to a value of its declared type, read as the relation reads types (`eraseTy`). -/
  paramsTyped : ∀ p ∈ Γ.procedures, p.body = some fr.body → ∀ xt ∈ p.inputs ++ p.outputs,
    ∀ v, ρ.store xt.1 = some v →
      HasVal.valueOfTy (P := Core.Expression) ρ.factory v (eraseTy Γ xt.2)
  /-- The store binds the heap the run starts from: any heap whose allocated objects have the
  tag of a composite. -/
  entryHeap : ∃ h, ρ.store entryHeapVar = some h ∧ IsOfTy ρ.factory h heapTy ∧
    WellTagged Γ ρ.factory h
  /-- The store binds no name but `$entryHeap` with a reserved prefix. -/
  reservedFresh : ∀ n, n ≠ entryHeapVar → (ρ.store n).isSome →
    ∀ p ∈ params.prefixIdents, ¬ p.toList.isPrefixOf n.name.toList

/-! ## The event language -/

/-- The Cortex event-trace language of `prog`. A run starts at the entry block of an entry
frame, with the heap the initial store binds to `$entryHeap` (`entryHeap`) and the entry
values of the initial store as the frame's `old` store. -/
@[expose] def EventLang.cortex (prog : Program) : EventLang Core.Expression CEvent where
  StmtT := Frame
  CfgT := CConfig
  step := StepCortex prog.ctx (EvalIRCmd prog.ctx)
  stmtCfg st ρ :=
    .atBlock (st.toFr prog.ctx (entryOld prog.ctx st.inputs st.outputs ρ.store))
    st.body.cfg.entry
    ⟨ρ, entryHeap ρ.factory ρ.store⟩
  terminalCfg := .terminal
  exitingCfg _ := .terminal
  terminal_no_step _ _ _ := nofun
  exiting_no_step _ _ _ _ := nofun
  getEnv := CConfig.getEnv
  InitEnvWFParamsTy := Core.Logic.InitEnvWFParams
  initEnvWF := CortexInitEnvWF prog.ctx

/-! ## Event adapters -/

/-- A Cortex event as Core events: a Core event is itself, and an `uncaught` event is the
failing assertion and the assumption that `LowerExceptions` emits for it. -/
@[expose] def CEvent.erase : CEvent → Trace Core.Expression
  | .std e => [e]
  | .uncaught f σ md summary =>
    [.assert { factory := f, store := σ, label := "uncaught_exception", expr := ff,
               metadata := LowerExceptions.uncaughtMd summary md },
     .assume { factory := f, store := σ, label := "uncaught_exception", expr := ff,
               metadata := md }]

/-- A relation between Core traces as a relation between Cortex traces, through their
erasures. -/
@[expose] def CEvent.liftRel (R : Relation (Trace Core.Expression)) : Relation (List CEvent) :=
  fun τ τ' => R (τ.flatMap CEvent.erase) (τ'.flatMap CEvent.erase)

/-- A Cortex language with its traces erased to Core events. -/
@[expose] def EventLang.eraseEvents (L : EventLang Core.Expression CEvent) :
    EventLang Core.Expression (Event Core.Expression) where
  StmtT := L.StmtT
  CfgT := L.CfgT
  step c evs c' := ∃ evs', L.step c evs' c' ∧ evs = evs'.flatMap CEvent.erase
  stmtCfg := L.stmtCfg
  terminalCfg := L.terminalCfg
  exitingCfg := L.exitingCfg
  terminal_no_step ρ _ c' := fun ⟨_, h, _⟩ => L.terminal_no_step ρ _ c' h
  exiting_no_step l ρ _ c' := fun ⟨_, h, _⟩ => L.exiting_no_step l ρ _ c' h
  getEnv := L.getEnv
  InitEnvWFParamsTy := L.InitEnvWFParamsTy
  initEnvWF := L.initEnvWF

/-- A Core language with its events lifted to Cortex events by `CEvent.std`. -/
@[expose] def EventLang.liftStd (L : EventLang Core.Expression (Event Core.Expression)) :
    EventLang Core.Expression CEvent where
  StmtT := L.StmtT
  CfgT := L.CfgT
  step c evs c' := ∃ evs₀, L.step c evs₀ c' ∧ evs = evs₀.map .std
  stmtCfg := L.stmtCfg
  terminalCfg := L.terminalCfg
  exitingCfg := L.exitingCfg
  terminal_no_step ρ _ c' := fun ⟨_, h, _⟩ => L.terminal_no_step ρ _ c' h
  exiting_no_step l ρ _ c' := fun ⟨_, h, _⟩ => L.exiting_no_step l ρ _ c' h
  getEnv := L.getEnv
  InitEnvWFParamsTy := L.InitEnvWFParamsTy
  initEnvWF := L.initEnvWF

/-! ## Runs that start with safe references

`cortex_reachable_safe` (`SafeRefsProps.lean`) proves that every reference of a run is `Null` or
allocated, for a run that starts with such references (`SafeStart`). The invariant follows from
the premises of the relation's writes, which step only with such references. A source expression
could still compute another reference, with the constructor `Obj` or with a function that
returns a reference, and a write of it has no step. `SafeStart` also refuses such programs
(`SafeStart.noRefOps`). No proof uses that check. It is there so that the premises of the
writes exclude no run of a program a front end produces; that they exclude none is not proved,
because it would need a lemma about the denotation of expressions. The premise is separate from `CortexInitEnvWF`, which every pass must
establish of its output: it is about programs whose heap is still implicit, and a pass that
makes the heap explicit reads fields with operators that return references. -/

/-- The type `r` is ground and does not erase to `Ref` in `Γ`, so no value of it is a
reference. -/
@[expose] def notRefTy (Γ : UnorderedProgram) (r : LMonoTy) : Bool :=
  r.freeVars.isEmpty && eraseMono Γ r != refTy

/-- The operator `o`, with the annotation `ty`, builds no reference of `Γ`. It is not `Obj`,
and it is `Null`, or it has no annotation, or the result type of its annotation is ground and
does not erase to `Ref` (`notRefTy`). An expression's type is the result type of the annotation
of its head operator (`LExpr.typeCheck`), and an expression has a value only at a ground type,
so an operator without an annotation has no value, and one whose annotation is checked builds
no reference, whatever its declaration. That the check makes the premises of the relation's
writes cut no run is not proved (`SafeStart.noRefOps`). -/
@[expose] def noRefOp (Γ : UnorderedProgram) (o : String) (ty : Option LMonoTy) : Bool :=
  o != "Obj" && (o == "Null" || ty.all fun t => notRefTy Γ ((t.destructArrow).getLastD t))

/-- The expression `e` mentions no operator that builds a reference (`noRefOp`). -/
@[expose] def exprNoRefOps (Γ : UnorderedProgram) : Expr → Bool
  | .op _ o ty => noRefOp Γ o.name ty
  | .abs _ _ _ e => exprNoRefOps Γ e
  | .quant _ _ _ _ tr e => exprNoRefOps Γ tr && exprNoRefOps Γ e
  | .app _ fn a => exprNoRefOps Γ fn && exprNoRefOps Γ a
  | .ite _ c t e => exprNoRefOps Γ c && exprNoRefOps Γ t && exprNoRefOps Γ e
  | .eq _ a b => exprNoRefOps Γ a && exprNoRefOps Γ b
  | .const .. | .bvar .. | .fvar .. => true

/-- No expression that a command of the body `b` evaluates, nor a jump condition, mentions an
operator that builds a reference. -/
@[expose] def _root_.Cortex.Body.noRefOps (Γ : UnorderedProgram) (b : Body) : Bool :=
  b.cfg.blocks.all fun (_, blk) =>
    blk.cmds.all (fun c => c.exprs.all (exprNoRefOps Γ)) &&
      match blk.transfer with
      | .condGoto e _ _ _ => exprNoRefOps Γ e
      | .finish _ => true

/-- No procedure body of `Γ` mentions an operator that builds a reference. -/
@[expose] def _root_.Cortex.UnorderedProgram.noRefOps (Γ : UnorderedProgram) : Bool :=
  Γ.procedures.all fun p => p.body.all (Body.noRefOps Γ)

/-- A run of the entry frame `st` of `prog` from `ρ` starts with safe references: every value
the store binds, but the heap, is a reference that is `Null` or allocated in the heap the run
starts from, or no reference; that heap is closed; and no procedure body and not the entry
body mentions an operator that builds a reference. -/
structure SafeStart (prog : Program) (st : Frame) (ρ : Imperative.Env Core.Expression) :
    Prop where
  /-- The store holds only safe references in the heap the run starts from, but the heap. -/
  storeSafe : ∀ x v, x ≠ entryHeapVar → ρ.store x = some v →
    SafeRef ρ.factory (entryHeap ρ.factory ρ.store) v
  /-- The heap the run starts from is closed. -/
  heapClosed : HeapClosed prog.ctx ρ.factory (entryHeap ρ.factory ρ.store)
  /-- No procedure body and not the entry body mentions an operator that builds a
  reference. -/
  noRefOps : prog.ctx.noRefOps = true ∧ st.body.noRefOps prog.ctx = true

/-! ## CFGs of base commands -/

/-- A block of base commands as a Cortex block. -/
@[expose] def liftBlock (b : DetBlock Label (Cmd Core.Expression) Core.Expression) :
    DetBlock Label IRCmd Core.Expression :=
  { cmds := b.cmds.map .cmd, transfer := b.transfer }

/-- A block of base commands as the Cortex relation runs it, with the constrained
variables `vars`: each command followed by its constraint check, and the types erased. -/
@[expose] def eraseBlock (Γ : UnorderedProgram) (vars : List (String × String))
    (b : DetBlock Label (Cmd Core.Expression) Core.Expression) :
    DetBlock Label (Cmd Core.Expression) Core.Expression :=
  { cmds := (b.cmds.flatMap (checkedBaseCmd Γ vars)).map (eraseCmd Γ)
    transfer := mapTransfer (eraseExpr Γ) b.transfer }

/-- A CFG of base commands as a Cortex CFG. -/
@[expose] def liftCFG (g : DetCFG Core.Expression (Cmd Core.Expression)) :
    DetCFG Core.Expression IRCmd :=
  { entry := g.entry, blocks := g.blocks.map fun (l, b) => (l, liftBlock b) }

/-- A CFG of base commands as the Cortex relation runs it as an entry body: the checks of
the constraints of the variables its `init`s give a constrained type inserted, and the
types erased. -/
@[expose] def eraseCFG (Γ : UnorderedProgram) (g : DetCFG Core.Expression (Cmd Core.Expression)) :
    DetCFG Core.Expression (Cmd Core.Expression) :=
  { entry := g.entry
    blocks := g.blocks.map fun (l, b) =>
      (l, eraseBlock Γ (constrainedVars Γ [] (some ⟨liftCFG g, []⟩)) b) }

end -- public section

end Cortex.Sem
