/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import StrataLaurel.Implementation.Resolution
public import StrataLaurel.Implementation.LaurelPass
import StrataLaurel.Implementation.MapStmtExpr
import StrataLaurel.Implementation.GlobalVarAnalysis

/-!
# Bind Field Receivers

A field access evaluates its receiver once, before a store's value, and reads the heap after it.
This pass binds a receiver to a fresh local wherever evaluating it again, or later within the
access, would be observable, so that no `Pseudo.unstableFieldReceiver` remains:

    { setB(p); p }#b       ~>  { var $receiver0: Box := { setB(p); p }; $receiver0#b }
    x#g := { x := y; 5 }   ~>  var $receiver1: Box := x; $receiver1#g := { x := y; 5 }

A receiver stays only where it reads nothing but locals and fields that the access does not
change, so `x#r#r := v` binds `x#r`, which the store itself replaces when `x#r` is `x`. A receiver
that only calls or declares is bound too, although it has no effect: a copy of a declaration
declares twice, and a local costs nothing.
-/

namespace Strata.Laurel

public section

namespace BindFieldReceivers

/-- By procedure id, whether a call may write the heap and which globals it may write; and the
    names a `yield` may change, as it lets other code run, which may change any global or field. -/
structure Effects where
  heap : Std.HashSet Nat
  globals : Std.HashMap Nat (List String)
  yielded : List String

/-- What calling the procedures of `program` may do. -/
def Effects.of (model : SemanticModel) (program : LaurelProgram) : Effects :=
  let procs := program.staticProcedures
  let globals := program.staticFields
  let globalWriters := (computeGlobalEffectsByProcId model procs globals).writers
  { heap := model.heapWriters
    globals := globals.foldl (init := {}) fun acc g =>
      match g.name.uniqueId with
      | none => acc
      | some id => (globalWriters.getD id {}).fold (init := acc) fun acc p =>
        acc.insert p (g.name.text :: acc.getD p [])
    yielded := globals.map (·.name.text) }

/-- An over-approximation, by name, of what evaluating an expression may change: the locals and
    globals it assigns, and the fields it writes (`none`: any field). The default, nothing, is
    what a read changes. -/
structure Changes where
  locals : List String := []
  fields : Option (List String) := some []

/-- What evaluating `e` may change, a store's own targets included. -/
def Changes.of (effects : Effects) (e : StmtExprMd) : Changes :=
  -- Only `.Assign` targets: an update operator's target is never composite-typed, so no receiver
  -- that stays reads it.
  let assigned := collectStmtExprList (fun n => match n.val with
    | .Assign ts _ => ts
    | _ => []) e
  let callees := collectStmtExprList (fun n => match n.val with
    | .Call none callee _ _ => callee.uniqueId.toList
    | _ => []) e
  let yields := anyStmtExpr (fun n => n.val matches .Yield) e
  { locals := assigned.filterMap (fun t => match t.val with
        | .Local x => some x.text
        | _ => none)
      ++ callees.flatMap (effects.globals.getD · [])
      ++ (if yields then effects.yielded else [])
    fields := if yields || callees.any effects.heap.contains then none
      else some (assigned.filterMap fun t => match t.val with
        | .Field _ f => some f.text
        | _ => none) }

/-- Whether an access that makes `changes` leaves its receiver `recv` in place: `recv` only reads
    locals and fields, and the access changes none of them. -/
def Changes.keeps (changes : Changes) (recv : StmtExprMd) : Bool :=
  !anyStmtExpr (fun n => match n.val with
    | .Var (.Local x) => changes.locals.contains x.text
    | .Var (.Field _ f) => changes.fields.all (·.contains f.text)
    | _ => true) recv

/-- Bind `target`'s receiver to a fresh local unless an access making `changes` keeps it; return
    the binding and the target rewritten through it. The local is typed at the field's owner: at a
    constrained receiver type, ConstrainedTypeElim would check a constraint the source does not. A
    receiver whose field does not resolve (one of unknown type) stays: no local could hold it. -/
def bindTarget (model : SemanticModel) (changes : Changes) (target : VariableMd) :
    StateM Nat (List StmtExprMd × VariableMd) := do
  let .Field recv f := target.val | return ([], target)
  let .field owner _ := model.get f | return ([], target)
  if changes.keeps recv then return ([], target)
  let n ← modifyGet fun n => (n, n + 1)
  let r : Identifier := s!"$receiver{n}"
  return ([⟨.Assign [⟨.Declare ⟨r, some ⟨.UserDefined owner, recv.source⟩⟩, recv.source⟩] recv,
      recv.source⟩],
    ⟨.Field ⟨.Var (.Local r), recv.source⟩ f, target.source⟩)

/-- The bottom-up rewrite: bind the receiver of a field read, store or update operator (see
    `bindTarget`). -/
def bindNode (model : SemanticModel) (effects : Effects) (_resultUsed : Bool) (node : StmtExprMd) :
    StateM Nat (List StmtExprMd) := do
  let source := node.source
  match node.val with
  | .Var (.Field recv f) =>
    let (decls, access) ← bindTarget model {} ⟨.Field recv f, source⟩
    return decls ++ [⟨.Var access.val, source⟩]
  | .Assign targets value =>
    let bound ← targets.mapM (bindTarget model (Changes.of effects node))
    return (bound.map (·.1)).flatten ++ [⟨.Assign (bound.map (·.2)) value, source⟩]
  | .IncrDecr mode op target =>
    let (decls, target') ← bindTarget model (Changes.of effects node) target
    return decls ++ [⟨.IncrDecr mode op target', source⟩]
  | .CompoundAssign op target rhs =>
    let (decls, target') ← bindTarget model (Changes.of effects node) target
    return decls ++ [⟨.CompoundAssign op target' rhs, source⟩]
  | _ => return [node]

/-- Move the access `wrap` makes of `recv` after `recv`'s statements: `{ s; e }#f` becomes
    `{ s; e#f }`, `(if c then a else b)#f` becomes `if c then a#f else b#f`, and a one-argument
    call or a cast, whose operand runs first anyway, moves inside: `pick({ s; e })#f` becomes
    `{ s; pick(e)#f }`. -/
partial def floatAccess (wrap : StmtExprMd → StmtExprMd) (recv : StmtExprMd) : StmtExprMd :=
  match recv.val with
  | .Block stmts none [] none =>
    match stmts.getLast? with
    | some last => ⟨.Block (stmts.dropLast ++ [floatAccess wrap last]) none [] none, recv.source⟩
    | none => wrap recv
  | .IfThenElse c a (some b) =>
    ⟨.IfThenElse c (floatAccess wrap a) (some (floatAccess wrap b)), recv.source⟩
  | .Call none callee [arg] targs =>
    floatAccess (fun a => wrap ⟨.Call none callee [a] targs, recv.source⟩) arg
  | .AsType t ty => floatAccess (fun t' => wrap ⟨.AsType t' ty, recv.source⟩) t
  | _ => wrap recv

/-- The locals `e` reads. -/
def localReads (e : StmtExprMd) : List String :=
  collectStmtExprList (fun n => match n.val with
    | .Var (.Local x) => [x.text]
    | _ => []) e

/-- In a loop's condition, float each field access after its receiver's statements
    (`floatAccess`), so that it reads and writes the heap after them. A store or update operator
    moves its value into the receiver's block or branches, so it floats only when the value reads
    nothing that the receiver declares. Reads are all such a move can capture: a program whose
    receiver declares a local shadowing another stops at a duplicate definition, and a loop's
    condition cannot write a global. -/
def floatCondition (e : StmtExprMd) : StmtExprMd :=
  let movable (recv value : StmtExprMd) : Bool :=
    let declared := boundNamesInStmtExpr recv
    !(localReads value).any declared.contains
  mapStmtExpr (fun n => match n.val with
    | .Var (.Field recv f) => floatAccess (fun r => ⟨.Var (.Field r f), n.source⟩) recv
    | .Assign [⟨.Field recv f, ts⟩] v =>
      if movable recv v then floatAccess (fun r => ⟨.Assign [⟨.Field r f, ts⟩] v, n.source⟩) recv
      else n
    | .CompoundAssign op ⟨.Field recv f, ts⟩ v =>
      if movable recv v then
        floatAccess (fun r => ⟨.CompoundAssign op ⟨.Field r f, ts⟩ v, n.source⟩) recv
      else n
    | .IncrDecr mode op ⟨.Field recv f, ts⟩ =>
      floatAccess (fun r => ⟨.IncrDecr mode op ⟨.Field r f, ts⟩, n.source⟩) recv
    | _ => n) e

/-- Bind field receivers in `e`, except in a loop's condition: `LiftImperativeExpressions`
    evaluates a statement there once, before the loop, where a binding would fix the receiver for
    every test of the condition. There each access floats after its receiver's statements instead
    (`floatCondition`). An invariant is evaluated where it stands, so its receivers are bound like
    the body's. -/
partial def bindIn (model : SemanticModel) (effects : Effects) (e : StmtExprMd) :
    StateM Nat StmtExprMd :=
  mapStmtExprFlattenM
    (fun _ n => match n.val with
      | .While cond invs dec body postTest => do
        -- No syntax or front end sets a loop's measure, so `dec` is left alone.
        return some [⟨.While (floatCondition cond) (← invs.mapM (bindIn model effects)) dec
          (← bindIn model effects body) postTest, n.source⟩]
      | _ => pure none)
    (bindNode model effects) false e

end BindFieldReceivers

/-- Bind field receivers in every body, numbering each body's `$receiver` locals from 0. Contracts
    are left alone, as they cannot have effects. A procedure whose body has no field access is
    returned as it is, and so is the program when no body has one. -/
def bindFieldReceivers (model : SemanticModel) (program : LaurelProgram) : LaurelProgram :=
  let hasFieldAccess (e : StmtExprMd) : Bool := anyStmtExpr (fun n => match n.val with
    | .Var (.Field _ _) => true
    | .Assign ts _ => ts.any (·.val matches .Field ..)
    | .IncrDecr _ _ t | .CompoundAssign _ t _ => (t.val matches .Field ..)
    | _ => false) e
  let touches (proc : Procedure) : Bool := match proc.body with
    | .Opaque _ impl _ => impl.any hasFieldAccess
    | .Transparent b => hasFieldAccess b
    | _ => false
  if !program.staticProcedures.any touches then program else
  let effects := BindFieldReceivers.Effects.of model program
  let inProc (proc : Procedure) : Procedure :=
    if !touches proc then proc else
    match proc.body with
    | .Opaque posts impl modif =>
      -- A coroutine also resumes from a `yield` with new values for its `resumes` bindings.
      let effects := { effects with yielded := effects.yielded ++ proc.resumes.map (·.name.text) }
      let impl' := (impl.mapM (BindFieldReceivers.bindIn model effects)).run' 0
      { proc with body := .Opaque posts impl' modif }
    | .Transparent b =>
      { proc with body := .Transparent ((BindFieldReceivers.bindIn model effects b).run' 0) }
    | _ => proc
  { program with staticProcedures := program.staticProcedures.map inProc }

/-- Pipeline pass: bind every field receiver that its access could not leave in place. -/
public def bindFieldReceiversPass : LaurelPass := .onUnordered {
  name := "BindFieldReceivers"
  creates := [
      NodeKind.StmtExpr.Assign,
      NodeKind.StmtExpr.Block,
      NodeKind.StmtExpr.Var,
      NodeKind.Pseudo.statementExpression,
      -- a binding in a short-circuit's guarded operand makes that operand imperative
      NodeKind.Pseudo.imperativeShortCircuit
    ]
  removes := [NodeKind.Pseudo.unstableFieldReceiver]
  -- A call's effects are looked up by callee, which an instance call does not name, and a
  -- `resume` runs a coroutine, which may change anything.
  unsupported := [
      NodeKind.StmtExpr.Call.receiver?.some,
      NodeKind.StmtExpr.Resume,
      NodeKind.LaurelProgram.staticFunctions.cons
    ]
  documentation := "Binds a field access's receiver to a fresh `$receiver` local, ahead of the access, unless the receiver only reads locals and fields that the access does not change, so that the passes after it may repeat or delay any receiver of known type outside a loop's condition."
  -- The two passes after it ignore the model, and `CopyMutatedInputs` resolves again.
  needsResolves := false }
  fun _ p m => (bindFieldReceivers m p, [], {})

end -- public section
end Strata.Laurel
