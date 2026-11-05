/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Cortex.LowerComposites

namespace Cortex.LowerHeap

open Imperative Lambda
open Cortex.LowerComposites (compositeTy compositeCtor refOf tagOf)

public section

def heapVar : String := "$heap"
def heapTy : String := "$Heap"
def heapCtor : String := "$MkHeap"
def fieldTy : String := "$Field"
def boxTy : String := "$Box"
def heapData (h : Expr) : Expr := mkCall "$Heap..data!" [h]
def heapNext (h : Expr) : Expr := mkCall "$Heap..nextReference!" [h]
def heap : Expr := mkFvar heapVar
def snapVar : String := "$heapNextSnap"

def ident (n : String) : Core.Expression.Ident := ⟨n, ()⟩

partial def mangle : LMonoTy → String
  | .tcons n [] => n
  | .tcons n args => n ++ "$" ++ String.intercalate "$" (args.map mangle)
  | .bitvec n => s!"bv{n}"
  | .ftvar n => n

def boxCtor (t : LMonoTy) : String := s!"$Box${mangle t}"
def boxField (t : LMonoTy) : String := s!"$val${mangle t}"
def unbox (t : LMonoTy) (e : Expr) : Expr := mkCall s!"$Box..{boxField t}!" [e]
def box (t : LMonoTy) (e : Expr) : Expr := mkCall (boxCtor t) [e]
def fieldCtor (f : FieldRef) : String := s!"$field${f.owner}.{f.field}"

def isComposite : LMonoTy → Bool
  | .tcons n [] => n == compositeTy
  | _ => false

def freshAssume (e : Expr) (md : MD) : IRCmd :=
  .cmd (.assume "allocated" (mkCall "Int.Lt" [refOf e, heapNext heap]) md)

def fieldMono (p : Program) (f : FieldRef) : Except String LMonoTy :=
  match p.findField? f with
  | some fd => match fd.ty with
    | .forAll [] t => .ok t
    | _ => .error s!"polymorphic field {f.owner}.{f.field}"
  | none => .error s!"unknown field {f.owner}.{f.field}"

def directWriter (pr : Procedure) : Bool :=
  match pr.body with
  | none => true
  | some b => b.cfg.blocks.any fun (_, blk) => blk.cmds.any fun
    | .new .. | .writeField .. => true
    | _ => false

def callees (p : Program) (pr : Procedure) : List String :=
  match pr.body with
  | none => []
  | some b => b.cfg.blocks.flatMap fun (_, blk) => blk.cmds.flatMap (IRCmd.callees p)

def heapWriters (p : Program) : Std.HashSet String := Id.run do
  let mut ws : Std.HashSet String := p.procedures.foldl (fun s pr => if directWriter pr then s.insert pr.name else s) {}
  let mut changed := true
  let mut fuel := p.procedures.length + 2
  while changed && fuel > 0 do
    changed := false
    fuel := fuel - 1
    for pr in p.procedures do
      if !ws.contains pr.name && (callees p pr).any ws.contains then
        ws := ws.insert pr.name
        changed := true
  return ws

def lowerCmd (p : Program) (outs : Std.HashMap String (List Bool)) (writers : Std.HashSet String) :
    IRCmd → Except String (List IRCmd)
  | .new x c md => .ok
    [.cmd (.set x (.det (mkCall compositeCtor [heapNext heap, tagOf c])) md),
     .cmd (.set (ident heapVar) (.det (mkCall heapCtor [heapData heap, mkCall "Int.Add" [heapNext heap, intLit 1]])) md)]
  | .readField x o f md => do
    let t ← fieldMono p f
    let row := mkCall "select" [heapData heap, refOf o]
    let v := unbox t (mkCall "select" [row, mkOp (fieldCtor f)])
    return [.cmd (.set x (.det v) md)] ++ (if isComposite t then [freshAssume (mkFvar x.name) md] else [])
  | .writeField o f v md => do
    let t ← fieldMono p f
    let r := refOf o
    let row := mkCall "select" [heapData heap, r]
    let row' := mkCall "update" [row, mkOp (fieldCtor f), box t v]
    let data' := mkCall "update" [heapData heap, r, row']
    return [.cmd (.set (ident heapVar) (.det (mkCall heapCtor [data', heapNext heap])) md)]
  | c@(.call lhs q _ md) =>
    let flags := (outs.get? q).getD []
    let post := (lhs.zip flags).filterMap fun (x, comp) => if comp then some (freshAssume (mkFvar x.name) md) else none
    if writers.contains q then
      .ok ([.cmd (.set (ident snapVar) (.det (heapNext heap)) md), c,
            .cmd (.assume "heapMonotone" (mkCall "Int.Le" [mkFvar snapVar, heapNext heap]) md)] ++ post)
    else .ok (c :: post)
  | .virtualCall .. => .error "Cortex `virtualCall` must be lowered by LowerDispatch before LowerHeap"
  | c => .ok [c]

def lowerBody (p : Program) (outs : Std.HashMap String (List Bool)) (writers : Std.HashSet String) (inputs : List (Core.Expression.Ident × LTy))
    (b : Body) : Except String Body := do
  let blocks ← b.cfg.blocks.mapM fun (l, blk) => do
    let cmds ← blk.cmds.mapM (lowerCmd p outs writers)
    return (l, ({ blk with cmds := cmds.flatten } : LBlock))
  let ins : List IRCmd := inputs.filterMap fun (x, t) => match t with
    | .forAll [] m => if isComposite m then some (freshAssume (mkFvar x.name) .empty) else none
    | _ => none
  let entry := "$heapEntry"
  let usesSnap := blocks.any fun (_, blk) => blk.cmds.any fun
    | .cmd (.set x _ _) => x.name == snapVar
    | _ => false
  let init : List IRCmd := if usesSnap then [.cmd (.init (ident snapVar) (mono .int) .nondet .empty)] else []
  return { b with cfg := { entry, blocks := (entry, { cmds := init ++ ins, transfer := .goto b.cfg.entry }) :: blocks } }

def collectBoxTys (p : Program) : List LMonoTy :=
  p.composites.foldl (fun acc c => c.fields.foldl (fun acc fd => match fd.ty with
    | .forAll [] t => if acc.any (· == t) then acc else acc ++ [t]
    | _ => acc) acc) []

def mkDatatype (name : String) (ctors : List (LConstr Unit)) (dflt : String) : LDatatype Unit :=
  let cs := if ctors.isEmpty then [{ name := ⟨dflt, ()⟩, args := [] }] else ctors
  have h : cs.length != 0 := by simp only [cs]; split <;> simp_all
  { name, typeArgs := [], constrs := cs, constrs_ne := h }

def heapInit (mapTy : LMonoTy → LMonoTy → LMonoTy) : List (Cmd Core.Expression) :=
  let dataTy := mapTy .int (mapTy (tcon fieldTy) (tcon boxTy))
  [.init (ident "$heapData$init") (mono dataTy) .nondet .empty,
   .init (ident heapVar) (mono (tcon heapTy)) (.det (mkCall heapCtor [mkFvar "$heapData$init", intLit 0])) .empty]

def run (m : Module) : Except String Module := do
  let p := m.program
  let fields : List FieldRef := p.composites.flatMap fun c => c.fields.map fun f => { owner := c.name, field := f.name }
  let fieldDt := mkDatatype fieldTy (fields.map fun f => { name := ⟨fieldCtor f, ()⟩, args := [] }) "$NoField"
  let boxTys := collectBoxTys p
  let boxDt := mkDatatype boxTy (boxTys.map fun t => { name := ⟨boxCtor t, ()⟩, args := [(⟨boxField t, ()⟩, t)] }) "$NoBox"
  let mapTy := fun (k v : LMonoTy) => LMonoTy.tcons "Map" [k, v]
  let heapArgs : List (Core.Expression.Ident × LMonoTy) :=
    [(⟨"data", ()⟩, mapTy .int (mapTy (tcon fieldTy) (tcon boxTy))), (⟨"nextReference", ()⟩, .int)]
  let heapC : LConstr Unit := { name := ⟨heapCtor, ()⟩, args := heapArgs }
  let heapDt := mkDatatype heapTy [heapC] heapCtor
  let outs : Std.HashMap String (List Bool) := p.procedures.foldl (fun s pr =>
    s.insert pr.name (pr.outputs.map fun (_, t) => match t with
      | .forAll [] mt => isComposite mt
      | _ => false)) {}
  let writers := heapWriters p
  let procs ← p.procedures.mapM fun pr => do
    let body ← match pr.body with
      | some b => some <$> lowerBody p outs writers pr.inputs b
      | none => pure none
    return { pr with body }
  let decls := m.decls ++ [.type (.data [fieldDt]) .empty, .type (.data [boxDt]) .empty, .type (.data [heapDt]) .empty]
  return { program := { p with procedures := procs, composites := [],
                                globals := p.globals ++ [(ident heapVar, mono (tcon heapTy))],
                                globalInit := p.globalInit ++ heapInit mapTy },
           decls }

def pass : Pass := { name := "LowerHeap", run }

end

end Cortex.LowerHeap
