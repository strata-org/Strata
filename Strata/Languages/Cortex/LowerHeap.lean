/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Cortex.LowerComposites
public import Strata.Languages.Cortex.LowerDynamic

namespace Cortex.LowerHeap

open Imperative Lambda
open Cortex.LowerComposites (compositeTy compositeCtor refOf tagOf)
open Cortex.LowerDynamic (dynamicTy toDynamic fromDynamic mkDatatype)

public section

def heapVar : String := "$heap"
def heapTy : String := "$Heap"
def heapCtor : String := "$MkHeap"
def fieldTy : String := "$Field"
def heapData (h : Expr) : Expr := mkCall "$Heap..data!" [h]
def heapNext (h : Expr) : Expr := mkCall "$Heap..nextReference!" [h]
def heap : Expr := mkFvar heapVar
def snapVar : String := "$heapNextSnap"

def ident (n : String) : Core.Expression.Ident := ⟨n, ()⟩

def fieldCtor (f : FieldRef) : String := s!"$field${f.owner}.{f.field}"

/-- Whether `t` is a reference: `$Composite`, a composite, or a constrained type over one.
`LowerCTE` has not yet replaced the constrained types when this pass runs. -/
def isComposite (p : UnorderedProgram) : LMonoTy → Bool
  | .tcons n [] =>
    let isRef := fun (m : String) => m == compositeTy || p.composites.any (·.name == m)
    isRef n || match baseOf p.constrained n with
      | some (.tcons b []) => isRef b
      | _ => false
  | _ => false

def freshAssume (e : Expr) (md : MD) : IRCmd :=
  .cmd (.assume "allocated" (mkCall "Int.Lt" [refOf e, heapNext heap]) md)

def directWriter (pr : Procedure) : Bool :=
  match pr.body with
  | none => true
  | some b => b.cfg.blocks.any fun (_, blk) => blk.cmds.any fun
    | .new .. | .writeField .. => true
    | _ => false

def callees (p : UnorderedProgram) (pr : Procedure) : List String :=
  match pr.body with
  | none => []
  | some b => b.cfg.blocks.flatMap fun (_, blk) => blk.cmds.flatMap (IRCmd.callees p)

def heapWriters (p : UnorderedProgram) : Std.HashSet String := Id.run do
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

def lowerCmd (p : UnorderedProgram) (outs : Std.HashMap String (List Bool)) (writers : Std.HashSet String)
    (tmp : String) : IRCmd → Except String (List IRCmd)
  | .new x c md => .ok
    [.cmd (.set x (.det (mkCall compositeCtor [heapNext heap, tagOf c])) md),
     .cmd (.set (ident heapVar) (.det (mkCall heapCtor [heapData heap, mkCall "Int.Add" [heapNext heap, intLit 1]])) md)]
  | .readField x o f md => do
    let t ← fieldMono p f
    let row := mkCall "select" [heapData heap, refOf o]
    let v := fromDynamic t (mkCall "select" [row, mkOp (fieldCtor f)])
    return [IRCmd.cast x (mangle t) v .assume md] ++ (if isComposite p t then [freshAssume (mkFvar x.name) md] else [])
  | .writeField o f v md => do
    let t ← fieldMono p f
    let r := refOf o
    let row := mkCall "select" [heapData heap, r]
    let row' := mkCall "update" [row, mkOp (fieldCtor f), toDynamic t (mkFvar tmp)]
    let data' := mkCall "update" [heapData heap, r, row']
    return [.cmd (.set (ident tmp) (.det v) md),
            .cmd (.set (ident heapVar) (.det (mkCall heapCtor [data', heapNext heap])) md)]
  | c@(.call lhs q _ md) =>
    let flags := (outs.get? q).getD []
    let post := (lhs.zip flags).filterMap fun (x, comp) => if comp then some (freshAssume (mkFvar x.name) md) else none
    if writers.contains q then
      .ok ([.cmd (.set (ident snapVar) (.det (heapNext heap)) md), c,
            .cmd (.assume "heapMonotone" (mkCall "Int.Le" [mkFvar snapVar, heapNext heap]) md)] ++ post)
    else .ok (c :: post)
  | .virtualCall .. => .error "Cortex `virtualCall` must be lowered by LowerDispatch before LowerHeap"
  | c => .ok [c]

def lowerBody (p : UnorderedProgram) (outs : Std.HashMap String (List Bool)) (writers : Std.HashSet String) (inputs : List (Core.Expression.Ident × LTy))
    (b : Body) : Except String Body := do
  let mut n := 0
  let mut tmps : List (String × LMonoTy) := []
  let mut blocks : List (Label × LBlock) := []
  for (l, blk) in b.cfg.blocks do
    let mut cmds : List IRCmd := []
    for c in blk.cmds do
      let tmp := fieldValueVar n
      n := n + 1
      if let .writeField _ f _ _ := c then
        tmps := tmps ++ [(tmp, ← fieldMono p f)]
      cmds := cmds ++ (← lowerCmd p outs writers tmp c)
    let blk' : LBlock := { blk with cmds }
    blocks := blocks ++ [(l, blk')]
  let ins : List IRCmd := inputs.filterMap fun (x, t) => match t with
    | .forAll [] m => if isComposite p m then some (freshAssume (mkFvar x.name) .empty) else none
    | _ => none
  let entry := "$heapEntry"
  let usesSnap := blocks.any fun (_, blk) => blk.cmds.any fun
    | .cmd (.set x _ _) => x.name == snapVar
    | _ => false
  let init : List IRCmd := if usesSnap then [.cmd (.init (ident snapVar) (mono .int) .nondet .empty)] else []
  let init := init ++ tmps.map fun (x, t) => .cmd (.init (ident x) (mono t) .nondet .empty)
  return { b with cfg := { entry, blocks := (entry, { cmds := init ++ ins, transfer := .goto b.cfg.entry }) :: blocks } }

def heapInit (mapTy : LMonoTy → LMonoTy → LMonoTy) : List (Cmd Core.Expression) :=
  let dataTy := mapTy .int (mapTy (tcon fieldTy) (tcon dynamicTy))
  [.init (ident "$heapData$init") (mono dataTy) .nondet .empty,
   .init (ident heapVar) (mono (tcon heapTy)) (.det (mkCall heapCtor [mkFvar "$heapData$init", intLit 0])) .empty]

def run (p : UnorderedProgram) : Except String UnorderedProgram := do
  let fields : List FieldRef := p.composites.flatMap fun c => c.fields.map fun f => { owner := c.name, field := f.name }
  let fieldDt := mkDatatype fieldTy (fields.map fun f => { name := ⟨fieldCtor f, ()⟩, args := [] }) "$NoField"
  let mapTy := fun (k v : LMonoTy) => LMonoTy.tcons "Map" [k, v]
  let heapArgs : List (Core.Expression.Ident × LMonoTy) :=
    [(⟨"data", ()⟩, mapTy .int (mapTy (tcon fieldTy) (tcon dynamicTy))), (⟨"nextReference", ()⟩, .int)]
  let heapC : LConstr Unit := { name := ⟨heapCtor, ()⟩, args := heapArgs }
  let heapDt := mkDatatype heapTy [heapC] heapCtor
  let outs : Std.HashMap String (List Bool) := p.procedures.foldl (fun s pr =>
    s.insert pr.name (pr.outputs.map fun (_, t) => match t with
      | .forAll [] mt => isComposite p mt
      | _ => false)) {}
  let writers := heapWriters p
  let procs ← p.procedures.mapM fun pr => do
    let body ← match pr.body with
      | some b => some <$> lowerBody p outs writers pr.inputs b
      | none => pure none
    return { pr with body }
  return { p with procedures := procs, composites := [],
                  globals := p.globals ++ [(ident heapVar, mono (tcon heapTy))],
                  globalInit := p.globalInit ++ heapInit mapTy,
                  datatypes := p.datatypes ++ [fieldDt, heapDt] }

def pass : Pass := Pass.onUnordered "LowerHeap" run

end

end Cortex.LowerHeap
