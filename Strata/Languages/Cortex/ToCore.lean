/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Cortex.Module
public import Strata.Languages.Core.Statement
public import Strata.Languages.Core.Procedure

namespace Cortex.ToCore

open Imperative Lambda

public section

instance : Inhabited LBlock := ⟨{ cmds := [], transfer := .finish .empty }⟩

structure Graph where
  blocks : Std.HashMap String LBlock
  order : Array String
  rpo : Std.HashMap String Nat
  preds : Std.HashMap String (List String)
  idom : Std.HashMap String String
  children : Std.HashMap String (List String)
  headers : Std.HashSet String
  merges : Std.HashSet String
  loops : Std.HashMap String (Std.HashSet String) := {}
  exits : Std.HashSet String := {}

def succs (b : LBlock) : List String :=
  match b.transfer with
  | .condGoto _ lt lf _ => if lt == lf then [lt] else [lt, lf]
  | .finish _ => []

partial def postorder (blocks : Std.HashMap String LBlock) (entry : String) : Array String := Id.run do
  let mut seen : Std.HashSet String := {}
  let mut out : Array String := #[]
  let mut stack : List (String × List String) := []
  seen := seen.insert entry
  stack := [(entry, (blocks.get? entry).map succs |>.getD [])]
  while true do
    match stack with
    | [] => break
    | (n, []) :: rest =>
      out := out.push n
      stack := rest
    | (n, s :: ss) :: rest =>
      stack := (n, ss) :: rest
      if !seen.contains s && blocks.contains s then
        seen := seen.insert s
        stack := (s, (blocks.get? s).map succs |>.getD []) :: stack
  return out

partial def intersect (rpo : Std.HashMap String Nat) (idom : Std.HashMap String String)
    (a b : String) : String :=
  if a == b then a
  else
    let ra := rpo.getD a 0
    let rb := rpo.getD b 0
    if ra > rb then intersect rpo idom (idom.getD a a) b
    else intersect rpo idom a (idom.getD b b)

def buildGraph (cfg : LCFG) : Except String Graph := do
  let blocks : Std.HashMap String LBlock := cfg.blocks.foldl (fun m (l, b) => m.insert l b) {}
  let order := (postorder blocks cfg.entry).reverse
  let rpo : Std.HashMap String Nat := order.zipIdx.foldl (fun m (l, i) => m.insert l i) {}
  let preds : Std.HashMap String (List String) := order.foldl (fun m l =>
    (succs (blocks.getD l default)).foldl (fun m s => m.insert s (l :: m.getD s [])) m) {}
  let mut idom : Std.HashMap String String := ({} : Std.HashMap String String).insert cfg.entry cfg.entry
  let mut changed := true
  let mut fuel := order.size * order.size + 10
  while changed && fuel > 0 do
    changed := false
    fuel := fuel - 1
    for b in order do
      if b == cfg.entry then continue
      let ps := (preds.getD b []).filter idom.contains
      match ps with
      | [] => pure ()
      | p :: rest =>
        let new := rest.foldl (fun acc q => intersect rpo idom q acc) p
        if idom.get? b != some new then
          idom := idom.insert b new
          changed := true
  let dominates (a b : String) : Bool := Id.run do
    let mut x := b
    for _ in [0:order.size + 1] do
      if x == a then return true
      let y := idom.getD x x
      if y == x then return x == a
      x := y
    return false
  let mut headers : Std.HashSet String := {}
  let mut fwdCount : Std.HashMap String Nat := {}
  for u in order do
    for v in succs (blocks.getD u default) do
      if rpo.getD v 0 ≤ rpo.getD u 0 then
        unless dominates v u do
          throw s!"irreducible control flow: edge {u} → {v}"
        headers := headers.insert v
      else
        fwdCount := fwdCount.insert v (fwdCount.getD v 0 + 1)
  let merges : Std.HashSet String := fwdCount.fold (fun s k n => if n ≥ 2 then s.insert k else s) {}
  let children : Std.HashMap String (List String) := order.foldl (fun m b =>
    if b == cfg.entry then m else
      let d := idom.getD b b
      m.insert d (m.getD d [] ++ [b])) {}
  let mut loops : Std.HashMap String (Std.HashSet String) := {}
  for h in headers.toList do
    let mut body : Std.HashSet String := ({} : Std.HashSet String).insert h
    let mut work : List String := order.toList.filter fun u =>
      (succs (blocks.getD u default)).contains h && rpo.getD h 0 ≤ rpo.getD u 0
    let mut lfuel := order.size * order.size + 10
    while lfuel > 0 do
      lfuel := lfuel - 1
      match work with
      | [] => break
      | u :: rest =>
        work := rest
        if body.contains u then continue
        body := body.insert u
        work := (preds.getD u []) ++ work
    loops := loops.insert h body
  let mut exits : Std.HashSet String := {}
  for h in headers.toList do
    let body := loops.getD h {}
    for c in children.getD h [] do
      unless body.contains c do exits := exits.insert c
  return { blocks, order, rpo, preds, idom, children, headers, merges, loops, exits }

def contLabel (l : String) : String := s!"$cont${l}"
def blkLabel (l : String) : String := s!"$blk${l}"
def bodyLabel : String := "$body"

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

def toCoreCmd (sigs : Std.HashMap String Sig) : IRCmd → Except String Core.Statement
  | .cmd c => .ok (.cmd (.cmd c))
  | .call lhs p args md => do
    return Core.Statement.call p (← callArgs (sigs.get? p) lhs args) md
  | .virtualCall .. => .error "Cortex `virtualCall` must be lowered by LowerDispatch before Core"
  | .new .. => .error "Cortex `new` must be lowered before Core"
  | .readField .. => .error "Cortex field read must be lowered before Core"
  | .writeField .. => .error "Cortex field write must be lowered before Core"
  | .instanceOf .. => .error "Cortex `instanceOf` must be lowered before Core"
  | .throw .. => .error "Cortex `throw` must be lowered before Core"

mutual

partial def doTree (sigs : Std.HashMap String Sig) (g : Graph) (x : String) :
    Except String (List Core.Statement) := do
  let byRpo := fun (l : List String) => l.mergeSort fun a b => g.rpo.getD a 0 ≥ g.rpo.getD b 0
  let kids := g.children.getD x []
  if g.headers.contains x then
    let body := g.loops.getD x {}
    let inside := byRpo (kids.filter fun c => body.contains c && g.merges.contains c)
    let outside := byRpo (kids.filter fun c => !body.contains c)
    let code ← nodeWithin sigs g x inside
    let loopStmt : Core.Statement := .loop (.det tt) none [] [.block (contLabel x) code .empty] .empty
    wrapAfter sigs g [loopStmt] outside
  else
    nodeWithin sigs g x (byRpo (kids.filter g.merges.contains))

partial def wrapAfter (sigs : Std.HashMap String Sig) (g : Graph) (core : List Core.Statement) :
    List String → Except String (List Core.Statement)
  | [] => .ok core
  | y :: ys => do
    let inner ← wrapAfter sigs g core ys
    let after ← doTree sigs g y
    return [.block (blkLabel y) inner .empty] ++ after

partial def nodeWithin (sigs : Std.HashMap String Sig) (g : Graph) (x : String) :
    List String → Except String (List Core.Statement)
  | y :: ys => do
    let inner ← nodeWithin sigs g x ys
    let after ← doTree sigs g y
    return [.block (blkLabel y) inner .empty] ++ after
  | [] => do
    let blk := g.blocks.getD x default
    let cmds ← blk.cmds.mapM (toCoreCmd sigs)
    let tail ← match blk.transfer with
      | .condGoto c lt lf md =>
        if lt == lf then doBranch sigs g x lt
        else do
          let t ← doBranch sigs g x lt
          let f ← doBranch sigs g x lf
          pure [Stmt.ite (.det c) t f md]
      | .finish md => pure [Stmt.exit bodyLabel md]
    return cmds ++ tail

partial def doBranch (sigs : Std.HashMap String Sig) (g : Graph) (x l : String) :
    Except String (List Core.Statement) :=
  if g.rpo.getD l 0 ≤ g.rpo.getD x 0 then .ok [.exit (contLabel l) .empty]
  else if g.merges.contains l || g.exits.contains l then .ok [.exit (blkLabel l) .empty]
  else doTree sigs g l

end

def assignedNames : IRCmd → List String
  | .cmd (.init x ..) | .cmd (.set x ..) => [x.name]
  | .call lhs .. | .virtualCall lhs .. => lhs.map (·.name)
  | .new x .. | .readField x .. | .instanceOf x .. => [x.name]
  | _ => []

def structureBody (sigs : Std.HashMap String Sig) (b : Body) : Except String (List Core.Statement) := do
  unless b.handlers.isEmpty do throw "exception handlers must be lowered before Core"
  let g ← buildGraph b.cfg
  let code ← doTree sigs g b.cfg.entry
  return [.block bodyLabel code .empty]

def procedureToCore (sigs : Std.HashMap String Sig) (p : Procedure) : Except String Core.Procedure := do
  let outNames := p.outputs.map (·.1.name)
  let assigned : List String := match p.body with
    | some b => b.cfg.blocks.flatMap fun (_, blk) => blk.cmds.flatMap assignedNames
    | none => []
  let mutatedInputs := p.inputs.filter fun (x, _) => assigned.contains x.name && !outNames.contains x.name
  let rename := fun (x : Core.Expression.Ident) =>
    if mutatedInputs.any (·.1 == x) then (⟨s!"{x.name}$in", ()⟩ : Core.Expression.Ident) else x
  let inputs ← p.inputs.mapM fun (x, t) => do return (rename x, ← toMono t)
  let outputs ← p.outputs.mapM fun (x, t) => do return (x, ← toMono t)
  let copies : List Core.Statement := mutatedInputs.map fun (x, t) =>
    Core.Statement.init x t (.det (.fvar () (rename x) none)) .empty
  let body ← match p.body with
    | some b => do pure (copies ++ (← structureBody sigs b))
    | none => pure [Core.Statement.assume "assume_true" (.true ()) .empty]
  let header : Core.Procedure.Header :=
    { name := ⟨p.name, ()⟩, typeArgs := [], inputs, outputs }
  return { header, spec := { preconditions := [], postconditions := [] }, body := .structured body }

def moduleToCore (m : Module) : Except String Core.Program := do
  unless m.program.globals.isEmpty do throw "globals must be lowered before Core"
  unless m.program.composites.isEmpty do throw "composites must be lowered before Core"
  let sigs : Std.HashMap String Sig := m.program.procedures.foldl (fun s p =>
    s.insert p.name { inputs := p.inputs.map (·.1.name), outputs := p.outputs.map (·.1.name) }) {}
  let procs ← m.program.procedures.mapM fun p => do
    let cp ← procedureToCore sigs p
    return Core.Decl.proc cp p.md
  return { decls := m.decls ++ procs }

end

end Cortex.ToCore
