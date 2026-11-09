/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Cortex.Heap
public import Strata.Languages.Cortex.Module
public import Strata.Languages.Core.Factory
public import Strata.Languages.Core.Program
import all Strata.DL.Lambda.FactoryProps

namespace Cortex.Interp

open Imperative hiding Trace Event EventArg
open Lambda

public section

abbrev LFactory := Lambda.Factory Core.CoreLParams

abbrev Store := Core.Expression.Ident → Option Expr

@[expose] def Store.empty : Store := fun _ => none

@[expose] def Store.update (σ : Store) (x : Core.Expression.Ident) (v : Expr) : Store :=
  fun y => if y = x then some v else σ y

structure EventArg where
  factory : LFactory
  store : Store
  label : String
  expr : Expr
  metadata : MD

inductive Event where
  | assert : EventArg → Event
  | assume : EventArg → Event
  | cover : EventArg → Event

abbrev Trace := List Event

@[expose] def emittedEvents : Cmd Core.Expression → LFactory → Store → Trace
  | .assert label expr metadata, f, σ => [.assert { factory := f, store := σ, label, expr, metadata }]
  | .assume label expr metadata, f, σ => [.assume { factory := f, store := σ, label, expr, metadata }]
  | .cover label expr metadata, f, σ => [.cover { factory := f, store := σ, label, expr, metadata }]
  | _, _, _ => []

@[expose] def exprFuel : Nat := 1000

@[expose] def evalPure (f : LFactory) (σ : Store) (e : Expr) : Option Expr :=
  match LExpr.eval exprFuel f σ e with
  | (v, .value true) => some v
  | _ => none

inductive StopReason where
  | fuelExhausted
  | noChoice
  | missingBlock (label : Label)
  | expressionDidNotEvaluate
  | expressionWasNotBoolean
  | unknownProcedure (name : ProcName)
  | procedureWithoutBody (name : ProcName)
  | unknownComposite (name : TypeName)
  | unknownField (field : FieldRef)
  | notAReference
  | danglingReference
  | missingObjectField (field : FieldRef)
  | illTypedValue
  | notAValue
  | undefinedVariable
  | variableAlreadyDefined
  | variableNotDefined
  | arityMismatch
  | aliasedResults
  | exceptionWithoutType
  | calleeDidNotTerminate (name : ProcName)
  | invalidDatatypes (msg : String)
  deriving Repr, Inhabited

class Effects (m : Type → Type) where
  emit : Trace → m Unit
  choose : LFactory → Core.Expression.Ty → m Expr

@[expose] def isValue (f : LFactory) (v : Expr) : Bool :=
  LExpr.isValue f v

@[expose] def isRefExpr (e : Expr) : Bool :=
  match e with
  | .const _ (.intConst _) => true
  | _ => false

@[expose] def isRefTy (prog : Program) (ty : Core.Expression.Ty) : Bool :=
  match (ty : LTy) with
  | .forAll [] (.tcons n []) => n.startsWith "$Any" || (prog.findComposite? n).isSome
  | _ => false

@[expose] def coreHasType (f : LFactory) (v : Expr) (ty : Core.Expression.Ty) : Bool :=
  isValue f v &&
    match LTy.toMonoType? (ty : LTy), LExpr.typeCheck [] v with
    | some a, some b => a == b
    | _, _ => false

@[expose] def hasType (prog : Program) (f : LFactory) (v : Expr) (ty : Core.Expression.Ty) : Bool :=
  coreHasType f v ty || (isRefTy prog ty && isRefExpr v && isValue f v) ||
    (isValue f v &&
      match _h : Factory.callOfLFunc f v true, (ty : LTy) with
      | some (_, args, fn), .forAll [] (.tcons n []) =>
        fn.isConstr && fn.typeArgs.isEmpty && fn.output == .tcons n [] &&
          args.length == fn.inputs.length &&
          ((args.attach.zip fn.inputs.values).all fun (⟨a, _ha⟩, aty) =>
            hasType prog f a (.forAll [] aty))
      | _, _ => false)
termination_by v.sizeOf
decreasing_by exact Factory.callOfLFunc_smaller (T := Core.CoreLParams.mono) _h a _ha

@[expose] def typeOf? (f : LFactory) (v : Expr) : Option Core.Expression.Ty :=
  if isValue f v then
    match LExpr.typeCheck [] v with
    | some t => if LTy.toMonoType? (LTy.forAll [] t) == some t then some (LTy.forAll [] t) else none
    | none => none
  else none

structure IEnv where
  store : Store
  heap : Heap
  factory : LFactory
  next : Nat
  tys : Core.Expression.Ident → Option Core.Expression.Ty := fun _ => none

inductive IConfig where
  | atBlock : Body → Label → IEnv → IConfig
  | inBlock : Body → Label → List IRCmd → DetTransferCmd Label Core.Expression → IEnv → IConfig
  | terminal : IEnv → IConfig
  | raised : IEnv → Expr → MD → IConfig

@[expose] def IRCmd.md : IRCmd → MD
  | .cmd (.init _ _ _ md) | .cmd (.set _ _ md) | .cmd (.assert _ _ md) | .cmd (.assume _ _ md)
  | .cmd (.cover _ _ md) => md
  | .new _ _ md | .readField _ _ _ md | .writeField _ _ _ md | .instanceOf _ _ _ md
  | .call _ _ _ md | .virtualCall _ _ _ _ md | .throw _ md => md

structure CmdResult where
  store : Store
  heap : Heap
  next : Nat
  outcome : Outcome

variable {m : Type → Type} [Monad m] [Effects m] [MonadExcept StopReason m]

@[expose] def evalExpr (f : LFactory) (σ : Store) (e : Expr) : m Expr :=
  match evalPure f σ e with
  | some v => pure v
  | none => throw .expressionDidNotEvaluate

@[expose] def initVar (σ : Store) (x : Core.Expression.Ident) (v : Expr) : m (Store) :=
  if (σ x).isNone then pure (σ.update x v) else throw .variableAlreadyDefined

@[expose] def setVar (σ : Store) (x : Core.Expression.Ident) (v : Expr) : m (Store) :=
  if (σ x).isSome then pure (σ.update x v) else throw .variableNotDefined

@[expose] def chooseTyped (prog : Program) (f : LFactory) (ty : Core.Expression.Ty) : m Expr := do
  let v ← Effects.choose f ty
  if hasType prog f v ty then pure v else throw .illTypedValue

@[expose] def storedTyOk (prog : Program) (f : LFactory) (σ : Store) (x : Core.Expression.Ident) (v : Expr) : Bool :=
  match σ x with
  | some prev =>
    match typeOf? f prev with
    | some ty => hasType prog f v ty
    | none => false
  | none => false

@[expose] def evalBaseCmd (prog : Program) (f : LFactory) (σ : Store) (tys : Core.Expression.Ident → Option Core.Expression.Ty) :
    Cmd Core.Expression → m (Store)
  | .init x ty (.det e) _ => do
    let v ← evalExpr f σ e
    if hasType prog f v ty then initVar σ x v else throw .illTypedValue
  | .init x ty .nondet _ => do
    let v ← chooseTyped prog f ty
    initVar σ x v
  | .set x (.det e) _ => do
    let v ← evalExpr f σ e
    if storedTyOk prog f σ x v then setVar σ x v else throw .illTypedValue
  | .set x .nondet _ => do
    match (tys x).orElse fun _ => (σ x).bind (typeOf? f) with
    | some ty =>
      let v ← chooseTyped prog f ty
      if storedTyOk prog f σ x v then setVar σ x v else throw .illTypedValue
    | none => throw .illTypedValue
  | c@(.assert ..) | c@(.assume ..) | c@(.cover ..) => do
    Effects.emit (emittedEvents c f σ)
    pure σ

@[expose] def deref (h : Heap) (v : Expr) : m (Nat × Obj) :=
  match getRef? v with
  | none => throw .notAReference
  | some a =>
    match h a with
    | some o => pure (a, o)
    | none => throw .danglingReference

@[expose] def objectFieldRefs (prog : Program) (ty : TypeName) : List FieldRef :=
  prog.composites.flatMap fun c =>
    if prog.isSubtype ty c.name then c.fields.map fun fd => ⟨c.name, fd.name⟩ else []

@[expose] def chooseFields (prog : Program) (f : LFactory) :
    List FieldRef → m (List (FieldRef × Expr))
  | [] => pure []
  | r :: rs => do
    match prog.findField? r with
    | some d =>
      let v ← chooseTyped prog f d.ty
      let vs ← chooseFields prog f rs
      pure ((r, v) :: vs)
    | none => throw (.unknownField r)

@[expose] def freshObject (prog : Program) (f : LFactory) (ty : TypeName) : m (Obj) := do
  let vals ← chooseFields prog f (objectFieldRefs prog ty)
  pure { type := ty
         fields := fun r =>
           if prog.isSubtype ty r.owner && (prog.findField? r).isSome then vals.lookup r else none }

@[expose] def evalArgs (f : LFactory) (σ : Store) : List Expr → m (List Expr)
  | [] => pure []
  | e :: es => do
    if (HasFvars.getFvars (P := Core.Expression) e).all (fun x => (σ x).isSome) then
      let v ← evalExpr f σ e
      let vs ← evalArgs f σ es
      pure (v :: vs)
    else throw .undefinedVariable

@[expose] def readValues (f : LFactory) (σ : Store) : List Core.Expression.Ident → m (List Expr)
  | [] => pure []
  | x :: xs =>
    match σ x with
    | some v =>
      if isValue f v then do
        let vs ← readValues f σ xs
        pure (v :: vs)
      else throw .notAValue
    | none => throw .variableNotDefined

@[expose] def initStates (σ : Store) : List Core.Expression.Ident → List Expr → m (Store)
  | [], [] => pure σ
  | x :: xs, v :: vs => do
    let σ' ← initVar σ x v
    initStates σ' xs vs
  | _, _ => throw .arityMismatch

@[expose] def updateStates (σ : Store) : List Core.Expression.Ident → List Expr → m (Store)
  | [], [] => pure σ
  | x :: xs, v :: vs => do
    let σ' ← setVar σ x v
    updateStates σ' xs vs
  | _, _ => throw .arityMismatch

@[expose] def chooseValues (prog : Program) (f : LFactory) : List Core.Expression.Ty → m (List Expr)
  | [] => pure []
  | ty :: tys => do
    let v ← chooseTyped prog f ty
    let vs ← chooseValues prog f tys
    pure (v :: vs)

@[expose] def callFrame (prog : Program) (f : LFactory) (σ : Store) (p : Procedure)
    (args : List Expr) : m (Store) := do
  let gnames := prog.globals.map Prod.fst
  let gvals ← readValues f σ gnames
  let σG ← initStates Store.empty gnames gvals
  let ins ← evalArgs f σ args
  let σI ← initStates σG (p.inputs.map Prod.fst) ins
  let outs ← chooseValues prog f (p.outputs.map Prod.snd)
  initStates σI (p.outputs.map Prod.fst) outs

@[expose] def globalsBack (prog : Program) (f : LFactory) (σ σEnd : Store) :
    m (Store) := do
  let gnames := prog.globals.map Prod.fst
  let gvals ← readValues f σEnd gnames
  updateStates σ gnames gvals

@[expose] def paramTys (p : Procedure) (x : Core.Expression.Ident) : Option Core.Expression.Ty :=
  (p.inputs ++ p.outputs).lookup x

@[expose] def stepWith (prog : Program) (evalCmd : IEnv → IRCmd → m CmdResult) :
    IConfig → m (IConfig)
  | .atBlock b t ρ =>
    match List.lookup t b.cfg.blocks with
    | some blk => pure (.inBlock b t blk.cmds blk.transfer ρ)
    | none => throw (.missingBlock t)
  | .inBlock b t (c :: cs) tr ρ => do
    let r ← evalCmd ρ c
    let tys := match c with
      | .cmd (.init x ty _ _) => fun y => if y = x then some ty else ρ.tys y
      | _ => ρ.tys
    let ρ' : IEnv := { ρ with store := r.store, heap := r.heap, next := r.next, tys }
    match r.outcome with
    | .normal => pure (.inBlock b t cs tr ρ')
    | .exn v =>
      match dynType r.heap v with
      | none => throw .exceptionWithoutType
      | some ty =>
        match b.handlerFor? prog t ty with
        | some hd => pure (.atBlock b hd.target { ρ' with store := r.store.update hd.binder v })
        | none => pure (.raised ρ' v (IRCmd.md c))
  | .inBlock b _ [] (.condGoto e lt lf _) ρ =>
    match evalPure ρ.factory ρ.store e with
    | some v =>
      if v = HasBool.tt (P := Core.Expression) then pure (.atBlock b lt ρ)
      else if v = HasBool.ff (P := Core.Expression) then pure (.atBlock b lf ρ)
      else throw .expressionWasNotBoolean
    | none => throw .expressionDidNotEvaluate
  | .inBlock _ _ [] (.finish _) ρ => pure (.terminal ρ)
  | .terminal ρ => pure (.terminal ρ)
  | .raised ρ v md => pure (.raised ρ v md)

@[expose] def callProc (prog : Program) (runBody : IConfig → m (IConfig)) (ρ : IEnv)
    (lhs : List Core.Expression.Ident) (n : ProcName) (args : List Expr) : m CmdResult := do
  match prog.findProcedure? n with
  | none => throw (.unknownProcedure n)
  | some p =>
    match p.body with
    | none => throw (.procedureWithoutBody n)
    | some body =>
      let σ₀ ← callFrame prog ρ.factory ρ.store p args
      let final ← runBody (.atBlock body body.cfg.entry
        { store := σ₀, heap := ρ.heap, factory := ρ.factory, next := ρ.next, tys := paramTys p })
      match final with
      | .terminal ρE =>
        if lhs.Nodup then
          let outs ← readValues ρ.factory ρE.store (p.outputs.map Prod.fst)
          let σL ← updateStates ρ.store lhs outs
          let σ' ← globalsBack prog ρ.factory σL ρE.store
          pure ⟨σ', ρE.heap, ρE.next, .normal⟩
        else throw .aliasedResults
      | .raised ρE v _ =>
        let σ' ← globalsBack prog ρ.factory ρ.store ρE.store
        pure ⟨σ', ρE.heap, ρE.next, .exn v⟩
      | _ => throw (.calleeDidNotTerminate n)

mutual

@[expose] def evalCmd (prog : Program) : Nat → IEnv → IRCmd → m CmdResult
  | _, ρ, .cmd c => do
    let σ' ← evalBaseCmd prog ρ.factory ρ.store ρ.tys c
    pure ⟨σ', ρ.heap, ρ.next, .normal⟩
  | _, ρ, .new x ty _ => do
    if (prog.findComposite? ty).isSome then
      let o ← freshObject prog ρ.factory ty
      let σ' ← setVar ρ.store x (mkRef ρ.next)
      pure ⟨σ', ρ.heap.update ρ.next o, ρ.next + 1, .normal⟩
    else throw (.unknownComposite ty)
  | _, ρ, .readField x obj r _ => do
    let v ← evalExpr ρ.factory ρ.store obj
    let (_, o) ← deref ρ.heap v
    match o.fields r with
    | some w =>
      let σ' ← setVar ρ.store x w
      pure ⟨σ', ρ.heap, ρ.next, .normal⟩
    | none => throw (.missingObjectField r)
  | _, ρ, .writeField obj r rhs _ => do
    let v ← evalExpr ρ.factory ρ.store obj
    let (a, o) ← deref ρ.heap v
    if (o.fields r).isSome then
      let w ← evalExpr ρ.factory ρ.store rhs
      match prog.findField? r with
      | some d =>
        if hasType prog ρ.factory w d.ty then
          pure ⟨ρ.store, ρ.heap.update a (o.setField r w), ρ.next, .normal⟩
        else throw .illTypedValue
      | none => throw (.unknownField r)
    else throw (.missingObjectField r)
  | _, ρ, .instanceOf x obj ty _ => do
    let v ← evalExpr ρ.factory ρ.store obj
    let (_, o) ← deref ρ.heap v
    let σ' ← setVar ρ.store x (if prog.isSubtype o.type ty then HasBool.tt (P := Core.Expression) else HasBool.ff (P := Core.Expression))
    pure ⟨σ', ρ.heap, ρ.next, .normal⟩
  | _, ρ, .throw e _ => do
    let v ← evalExpr ρ.factory ρ.store e
    pure ⟨ρ.store, ρ.heap, ρ.next, .exn v⟩
  | 0, _, .call _ _ _ _ | 0, _, .virtualCall _ _ _ _ _ => throw .fuelExhausted
  | fuel + 1, ρ, .call lhs n args _ => callProc prog (run prog fuel) ρ lhs n args
  | fuel + 1, ρ, .virtualCall lhs owner meth args _ => do
    let recv ← match args with
      | r :: _ => evalExpr ρ.factory ρ.store r
      | [] => throw .arityMismatch
    let (_, o) ← deref ρ.heap recv
    callProc prog (run prog fuel) ρ lhs (prog.dispatch owner meth o.type) args

@[expose] def run (prog : Program) : Nat → IConfig → m (IConfig)
  | _, .terminal ρ => pure (.terminal ρ)
  | _, .raised ρ v md => pure (.raised ρ v md)
  | 0, _ => throw .fuelExhausted
  | fuel + 1, c => do
    let c' ← stepWith prog (fun ρ cmd => evalCmd prog fuel ρ cmd) c
    run prog fuel c'

end

abbrev HostM :=
  ReaderT (LFactory → Core.Expression.Ty → Nat → Option Expr) (StateT (Trace × Nat) (Except StopReason))

instance : Effects HostM where
  emit es := modify fun (t, n) => (t ++ es, n)
  choose f ty := do
    let oracle ← read
    let (t, n) ← get
    set (t, n + 1)
    match oracle f ty n with
    | some v => pure v
    | none => throw .noChoice

@[expose] def runHost (prog : Program) (fuel : Nat) (oracle : LFactory → Core.Expression.Ty → Nat → Option Expr)
    (c : IConfig) : Except StopReason (IConfig × Trace) :=
  match ((run prog fuel c : HostM IConfig).run oracle).run ([], 0) with
  | .ok (c', (t, _)) => .ok (c', t)
  | .error e => .error e

def moduleDatatypes (m : Module) : List (LDatatype Unit) :=
  m.decls.flatMap fun
    | .type (.data ds) _ => ds
    | _ => []

def moduleFactory (m : Module) : Except Strata.Message LFactory :=
  m.decls.foldlM (init := Core.Factory) fun F d =>
    match d with
    | .type (.data ds) _ => do
      let bf ← Lambda.genBlockFactory (T := Core.CoreLParams) ds
      Lambda.Factory.addFactory F bf
    | _ => pure F

def datatypeDefault (m : Module) (n : String) : Option Expr :=
  (moduleDatatypes m).find? (·.name == n) >>= fun d =>
    if d.typeArgs.isEmpty then
      (d.constrs.find? (·.args.isEmpty)).map fun c => (constrFunc (T := Core.CoreLParams) c d).opExpr
    else none

def defaultValue (m : Module) (_f : LFactory) (ty : Core.Expression.Ty) (_n : Nat) : Option Expr :=
  match (ty : LTy) with
  | .forAll [] (.tcons "int" []) => some (.const () (.intConst 0) : Core.Expression.Expr)
  | .forAll [] (.tcons "bool" []) => some (.const () (.boolConst false) : Core.Expression.Expr)
  | .forAll [] (.tcons "string" []) => some (.const () (.strConst "") : Core.Expression.Expr)
  | .forAll [] (.tcons "real" []) => some (.const () (.rationalConst 0) : Core.Expression.Expr)
  | .forAll [] (.bitvec n) => some (.const () (.bitvecConst n 0) : Core.Expression.Expr)
  | t@(.forAll [] (.tcons n [])) =>
    if isRefTy m.program t then some (.const () (.intConst (-1)) : Core.Expression.Expr)
    else datatypeDefault m n
  | _ => none

def isEntry (p : Procedure) : Bool :=
  match p.md.findElem Imperative.MetaData.interpretEntry with
  | some { value := .switch true, .. } => true
  | _ => false

def startProc (prog : Program) (f : LFactory) (fuel : Nat) (p : Procedure) : HostM IConfig := do
  match p.body with
  | none => throw (.procedureWithoutBody p.name)
  | some body =>
    let σ₀ ← callFrame prog f Store.empty p []
    run prog fuel (.atBlock body body.cfg.entry
      { store := σ₀, heap := fun _ => none, factory := f, next := 0, tys := paramTys p })

def runEntry (m : Module) (fuel : Nat) (p : Procedure) :
    Except StopReason (IConfig × Trace) :=
  match moduleFactory m with
  | .error e => .error (.invalidDatatypes e.message)
  | .ok f =>
    match ((startProc m.program f fuel p).run (defaultValue m)).run ([], 0) with
    | .ok (c, (t, _)) => .ok (c, t)
    | .error e => .error e

def evalsTo (a : EventArg) (b : Bool) : Bool :=
  match evalPure a.factory a.store a.expr with
  | some v => decide (v = if b then HasBool.tt (P := Core.Expression) else HasBool.ff (P := Core.Expression))
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
