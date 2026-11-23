/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Cortex.Module
public import Strata.Languages.Core.Statement
public import Strata.Languages.Core.Procedure
public import Strata.Languages.Core.MarkerLabels

/-!
# Cortex to Core

`programToCore` turns an ordered Cortex program into a Core program.
Each procedure body becomes a Core CFG body (`.cfg`), block for block: labels,
commands and transfers are kept, so no control flow is rebuilt. Core can
type-check and print the result. The evaluator behind
`Core.Program.interpretEntries` accepts only structured bodies, and the verifier
(`Core.verify`) accepts CFG bodies only under `--vcgen symexec`, and only without loops.

Core's CFG type checker puts two requirements on the Cortex CFG:
* Every `init` sits in a block that dominates the uses of its variable and
  that is not on a cycle. `FromLaurel` output meets this: it declares every
  local in one block that runs once, before the body, and the passes declare
  theirs in blocks that run before that one. Nothing here hoists declarations;
  a frontend that declares a local inside a loop has to hoist it first.
* Every block that uses a local is reachable from the entry. An unreachable
  block is scoped without the locals of any dominator, so its uses are
  rejected. `PruneUnreachable` removes unreachable blocks.
-/

namespace Cortex.ToCore

open Imperative Lambda

public section

structure Sig where
  inputs : List String
  outputs : List String

def toMono (t : LTy) : Except String LMonoTy :=
  match t with
  | .forAll [] m => .ok m
  | _ => .error "polymorphic type in Cortex"

def callArgs (sig : Option Sig) (lhs : List Core.Expression.Ident) (args : List Expr) :
    Except String (List (CallArg Core.Expression)) := do
  match sig with
  | none => return args.map .inArg ++ lhs.map .outArg
  | some s =>
    let inouts := s.inputs.filter s.outputs.contains
    let ins ← (s.inputs.zip args).mapM fun (n, a) =>
      if inouts.contains n then
        match a with
        | .fvar _ x _ => pure (CallArg.inoutArg x)
        | _ => throw s!"inout argument '{n}' is not a variable"
      else pure (.inArg a)
    let outs : List (String × CallArg Core.Expression) := (s.outputs.zip lhs).map fun (n, x) =>
      (n, if inouts.contains n then CallArg.inoutArg x else CallArg.outArg x)
    let rec merge (is : List (String × CallArg Core.Expression)) (os : List (String × CallArg Core.Expression)) :
        List (CallArg Core.Expression) :=
      match is with
      | [] => os.filterMap fun (n, a) => if inouts.contains n then none else some a
      | (n, a) :: irest =>
        if inouts.contains n then
          let (before, after) := os.span fun (m, _) => m != n
          before.map (·.2) ++ [a] ++ merge irest (after.drop 1)
        else a :: merge irest os
    termination_by is.length
    return merge (s.inputs.zip ins) outs

def toCoreCmd (sigs : Std.HashMap String Sig) : IRCmd → Except String Core.Command
  | .cmd c => .ok (.cmd c)
  | .call lhs p args md => do
    return .call p none (← callArgs (sigs.get? p) lhs args) md
  | .virtualCall .. => .error "Cortex `virtualCall` must be lowered by LowerDispatch before Core"
  | .new .. => .error "Cortex `new` must be lowered before Core"
  | .cast .. => .error "Cortex `cast` must be lowered by LowerCTE before Core"
  | .readField .. => .error "Cortex field read must be lowered before Core"
  | .writeField .. => .error "Cortex field write must be lowered before Core"
  | .instanceOf .. => .error "Cortex `instanceOf` must be lowered before Core"
  | .newArray .. | .readElem .. | .writeElem .. | .arrayLength .. | .instanceOfComponent .. =>
    .error "Cortex array commands are not lowered to Core"
  | .throw .. => .error "Cortex `throw` must be lowered before Core"

/-- The Core header of a procedure: its name and its parameters with monomorphic
types. A body may assign only its outputs and its locals, so an assigned input
that is not an output is an error: the `CopyAssignedInputs` pass replaces such
an assignment by one to a local copy. -/
def procedureHeader (p : Procedure) : Except String Core.Procedure.Header := do
  let outNames := p.outputs.map (·.1.name)
  let assigned := (p.body.map Body.assignedNames).getD []
  if let some (x, _) := p.inputs.find? fun (x, _) => assigned.contains x.name && !outNames.contains x.name then
    throw s!"procedure '{p.name}' assigns its input '{x.name}': the CopyAssignedInputs pass must run before Core"
  let inputs ← p.inputs.mapM fun (x, t) => do return (x, ← toMono t)
  let outputs ← p.outputs.mapM fun (x, t) => do return (x, ← toMono t)
  return { name := ⟨p.name, ()⟩, typeArgs := [], inputs, outputs }

/-- A procedure's preconditions as Core's, labelled `requires_<i>`, and its
postconditions as Core's, with their own labels. -/
def procedureSpec (p : Procedure) : Core.Procedure.Spec :=
  let preconditions := (p.requires.zipIdx).map fun (pre, i) =>
    ((s!"requires_{i}" : Core.CoreLabel), ({ expr := pre.cond, md := pre.md } : Core.Procedure.Check))
  let postconditions := p.ensures.map fun post =>
    ((post.label : Core.CoreLabel), ({ expr := post.cond, md := post.md } : Core.Procedure.Check))
  { preconditions, postconditions }

/-- A Cortex CFG as a Core CFG with the same labels and transfers. -/
private def cfgToCore (sigs : Std.HashMap String Sig) (cfg : LCFG) : Except String Core.DetCFG := do
  let blocks ← cfg.blocks.mapM fun (l, b) => do
    let cmds ← b.cmds.mapM (toCoreCmd sigs)
    return (l, ({ cmds, transfer := b.transfer } : DetBlock String Core.Command Core.Expression))
  return { entry := cfg.entry, blocks }

/-- A Cortex procedure as a Core procedure with a CFG body. A procedure without a body is an
abstract Core procedure (`.abstract`): a call to it means its contract. -/
def procedureToCore (sigs : Std.HashMap String Sig) (p : Procedure) : Except String Core.Procedure := do
  let header ← procedureHeader p
  let body ← match p.body with
    | none => pure .abstract
    | some b => do
      b.refuseHandlers "Core"
      pure (.cfg (← cfgToCore sigs b.cfg) false)
  return { header, spec := procedureSpec p, body }

/-- `p` with every call to a procedure named in `externals` followed by the marker
`assume [$__externalAssume_N]: true` (`Core.externalAssumePrefix`), `N` counting the markers. An
external procedure (`Procedure.external`) models code that Strata does not see: the call means
its contract, so a counterexample through the call may come from the model. -/
def markExternalCalls (externals : Std.HashSet String) (p : Core.Program) : Core.Program :=
  let markCmd (c : Core.Command) : StateM Nat (List Core.Command) := match c with
    | .call q _ _ md =>
      if externals.contains q then do
        let n ← modifyGet fun n => (n, n + 1)
        pure [c, .cmd (.assume s!"{Core.externalAssumePrefix}{n}" (Lambda.LExpr.true default) md)]
      else pure [c]
    | c => pure [c]
  let markDecl (d : Core.Decl) : StateM Nat Core.Decl := match d with
    | .proc q md => match q.body with
      | .cfg g o => do
        let blocks ← g.blocks.mapM fun (l, b) => do
          return (l, { b with cmds := ← b.cmds.flatMapM markCmd })
        pure (.proc { q with body := .cfg { g with blocks } o } md)
      | _ => pure d
    | d => pure d
  { p with decls := (p.decls.mapM markDecl).run' 0 }

/-- An ordered Cortex program as a Core program whose procedure bodies are CFGs, with each call
to an external procedure marked (`markExternalCalls`). The marker prefix is reserved for those
markers: a program that already has a label with it is rejected (`Core.rejectMarkerLabels`). -/
def programToCore : Program → Except String Core.Program
  | .unordered _ => .error "Internal error: Cortex must be ordered by the Ordering pass before Core"
  | .ordered prog => do
    let sigs : Std.HashMap String Sig := prog.decls.foldl (fun s d => match d with
      | .procedure p => s.insert p.name { inputs := p.inputs.map (·.1.name), outputs := p.outputs.map (·.1.name) }
      | _ => s) {}
    let decls ← prog.decls.mapM fun
      | .datatypes ds => pure (Core.Decl.type (.data ds) .empty)
      | .opaqueType tc => pure (Core.Decl.type (.con tc) .empty)
      | .function f => pure (Core.Decl.recFuncBlock [f.toFunc] .empty)
      | .procedure p => do return Core.Decl.proc (← procedureToCore sigs p) p.md
    let core : Core.Program := { decls }
    if let .error e := Core.Transform.run core
        (Core.rejectMarkerLabels "the lowering of Cortex to Core" Core.externalAssumePrefix) then
      throw (toString e.message)
    let externals := Std.HashSet.ofList <| prog.decls.filterMap fun
      | .procedure p => if p.external then some p.name else none
      | _ => none
    return markExternalCalls externals core

end

end Cortex.ToCore
