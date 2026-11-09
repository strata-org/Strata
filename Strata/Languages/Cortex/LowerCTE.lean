/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Cortex.Module

namespace Cortex.LowerCTE

open Imperative Lambda

public section

def ident (n : String) : Core.Expression.Ident := ⟨n, ()⟩

def conTyName? (t : LTy) : Option String :=
  match t with
  | .forAll [] (.tcons n []) => some n
  | _ => none

def atomsFuel (cs : List ConstrainedDecl) (name : String) (e : Expr) :
    Nat → List (Bool × Expr)
  | 0 => []
  | fuel + 1 =>
    match cs.find? (·.name == name) with
    | none => []
    | some c =>
      let here := (c.free, substFvars [(c.binder.name, e)] c.constraint)
      ((conTyName? c.base).map fun b => atomsFuel cs b e fuel).getD [] ++ [here]

def conjoin : List Expr → Option Expr
  | [] => none
  | e :: es => some (es.foldl (fun acc x => mkCall "Bool.And" [acc, x]) e)

def pred (cs : List ConstrainedDecl) (name : String) (e : Expr)
    (checkedOnly : Bool := false) : Option Expr :=
  conjoin ((atomsFuel cs name e (cs.length + 1)).filter (fun a => !checkedOnly || !a.1) |>.map (·.2))

partial def baseOf (cs : List ConstrainedDecl) (name : String) (fuel : Nat := 32) : Option LMonoTy :=
  match fuel, cs.find? (·.name == name) with
  | 0, _ => none
  | _, none => none
  | fuel + 1, some c =>
    match c.base with
    | .forAll _ (.tcons b []) => (baseOf cs b fuel).orElse fun _ => some (.tcons b [])
    | .forAll _ t => some t

def summaryMd (md : MD) (_t : String) : MD := md

structure Ctx where
  cs : List ConstrainedDecl
  witnessHavoc : Bool := false
  vars : Std.HashMap String String
  procs : Std.HashMap String (List (Option String) × List (Option String))
  fieldTy : FieldRef → Option String

def checkOf (ctx : Ctx) (assert : Bool) (t : String) (e : Expr) (md : MD) : List IRCmd :=
  match pred ctx.cs t e (checkedOnly := assert) with
  | none => []
  | some p =>
    if assert then [.cmd (.assert s!"constraint_{t}" p (summaryMd md t))]
    else [.cmd (.assume s!"constraint_{t}" p md)]

def checkVar (ctx : Ctx) (assert : Bool) (x : String) (md : MD) : List IRCmd :=
  match ctx.vars.get? x with
  | some t => checkOf ctx assert t (mkFvar x) md
  | none => []

def callChecks (ctx : Ctx) (c : IRCmd) (lhs : List Core.Expression.Ident) (p : ProcName)
    (args : List Expr) (md : MD) : List IRCmd :=
  let (ins, outs) := (ctx.procs.get? p).getD ([], [])
  let pre := (ins.zip args).flatMap fun (t?, a) => match t? with
    | some t => checkOf ctx true t a md
    | none => []
  let post := (outs.zip lhs).flatMap fun (t?, x) =>
    (match t? with
      | some t => checkOf ctx false t (mkFvar x.name) md
      | none => []) ++
    (if ctx.vars.get? x.name == t? then [] else checkVar ctx true x.name md)
  let thrown := "$callThrown"
  let guard : IRCmd → IRCmd := fun
    | .cmd (.assert l e md) => .cmd (.assert l (mkCall "Bool.Or" [mkFvar thrown, e]) md)
    | .cmd (.assume l e md) => .cmd (.assume l (mkCall "Bool.Or" [mkFvar thrown, e]) md)
    | c => c
  let post := if lhs.any (·.name == thrown) then post.map guard else post
  pre ++ [c] ++ post

def lowerCmd (ctx : Ctx) : IRCmd → List IRCmd
  | c@(.instanceOf x o t md) =>
    match pred ctx.cs t o with
    | some test => .cmd (.set x (.det test) md) :: checkVar ctx true x.name md
    | none => [c]
  | c@(.cmd (.init x _ (.det _) md)) | c@(.cmd (.set x (.det _) md)) => c :: checkVar ctx true x.name md
  | c@(.cmd (.init x _ .nondet md)) | c@(.cmd (.set x .nondet md)) =>
    match ctx.vars.get? x.name >>= fun t => ctx.cs.find? (·.name == t) >>= (·.witness) with
    | some w => if ctx.witnessHavoc then [c, .cmd (.set x (.det w) md)] else c :: checkVar ctx false x.name md
    | none => c :: checkVar ctx false x.name md
  | c@(.call lhs p args md) => callChecks ctx c lhs p args md
  | c@(.virtualCall lhs o meth args md) => callChecks ctx c lhs (implName o meth) args md
  | c@(.readField x _ f md) =>
    let fromField := match ctx.fieldTy f with
      | some t => checkOf ctx false t (mkFvar x.name) md
      | none => []
    let toVar := if ctx.vars.get? x.name == ctx.fieldTy f then [] else checkVar ctx true x.name md
    c :: (fromField ++ toVar)
  | c@(.writeField _ f v md) =>
    (match ctx.fieldTy f with
      | some t => checkOf ctx true t v md
      | none => []) ++ [c]
  | c => [c]

def varTypes (cs : List ConstrainedDecl) (p : Procedure) : Std.HashMap String String :=
  let isCon := fun (t : LTy) => (conTyName? t).filter fun n => cs.any (·.name == n)
  let params := (p.inputs ++ p.outputs).foldl (fun m (x, t) =>
    match isCon t with | some n => m.insert x.name n | none => m) {}
  match p.body with
  | none => params
  | some b => b.cfg.blocks.foldl (fun m (_, blk) => blk.cmds.foldl (fun m c =>
      match c with
      | .cmd (.init x t _ _) => match isCon t with | some n => m.insert x.name n | none => m
      | _ => m) m) params

def numberLabels (blocks : List (Label × LBlock)) : List (Label × LBlock) :=
  let step := fun (n : Nat) (c : IRCmd) => match c with
    | .cmd (.assert l e md) => if l.startsWith "constraint_" then (n + 1, .cmd (.assert s!"{l}_{n}" e md)) else (n, c)
    | .cmd (.assume l e md) => if l.startsWith "constraint_" then (n + 1, .cmd (.assume s!"{l}_{n}" e md)) else (n, c)
    | c => (n, c)
  let (_, out) := blocks.foldl (fun (n, acc) (l, blk) =>
    let (n', cmds) := blk.cmds.foldl (fun (n, cs) c => let (n', c') := step n c; (n', cs ++ [c'])) (n, [])
    (n', acc ++ [(l, { blk with cmds })])) (0, [])
  out

def lowerProcedure (witnessHavoc : Bool) (cs : List ConstrainedDecl)
    (procs : Std.HashMap String (List (Option String) × List (Option String)))
    (fieldTy : FieldRef → Option String) (p : Procedure) : Procedure :=
  let outNames := p.outputs.map (·.1.name)
  let allVars := varTypes cs p
  let ctx : Ctx := { cs, witnessHavoc, vars := allVars.filter fun x _ => !outNames.contains x, procs, fieldTy }
  let outCtx : Ctx := { ctx with vars := allVars }
  let body := p.body.map fun b =>
    let b := mapBody (lowerCmd ctx) id b
    let thrown := p.outputs.any (·.1.name == "$thrown")
    let guardThrown : IRCmd → IRCmd := fun
      | .cmd (.assert l e md) => .cmd (.assert l (mkCall "Bool.Or" [mkFvar "$thrown", e]) md)
      | c => c
    let outChecks : List IRCmd := p.outputs.flatMap fun (x, _) =>
      (checkVar outCtx true x.name p.md).map fun c => if thrown then guardThrown c else c
    let blocks := b.cfg.blocks.map fun (l, blk) =>
      match blk.transfer with
      | .finish _ => (l, { blk with cmds := blk.cmds ++ outChecks })
      | _ => (l, blk)
    let inChecks : List IRCmd := p.inputs.flatMap fun (x, _) => checkVar ctx false x.name p.md
    let entry := "$cteEntry"
    let blocks := (entry, ({ cmds := inChecks, transfer := .goto b.cfg.entry } : LBlock)) :: blocks
    { b with cfg := { entry, blocks := numberLabels blocks } }
  { p with body }

def runWith (witnessHavoc : Bool) (m : Module) : Except String Module :=
  let p := m.program
  let cs := p.constrained
  if cs.isEmpty then .ok m else
  let isCon := fun (t : LTy) => (conTyName? t).filter fun n => cs.any (·.name == n)
  let procs : Std.HashMap String (List (Option String) × List (Option String)) :=
    p.procedures.foldl (fun s pr => s.insert pr.name (pr.inputs.map (isCon ·.2), pr.outputs.map (isCon ·.2))) {}
  let fieldTy := fun (f : FieldRef) => (p.findField? f) >>= fun fd => isCon fd.ty
  let m := m.mapProcedures (lowerProcedure witnessHavoc cs procs fieldTy)
  let names : Std.HashSet String := cs.foldl (fun s c => s.insert c.name) {}
  let m := m.mapTys fun n => if names.contains n then baseOf cs n else none
  .ok { m with program := { m.program with constrained := [] } }

def run (m : Module) : Except String Module := runWith false m

def pass : Pass := { name := "LowerCTE", run }

end

end Cortex.LowerCTE
