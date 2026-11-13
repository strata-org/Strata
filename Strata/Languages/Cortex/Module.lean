/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Cortex.AST
public import Strata.Languages.Core.Program

namespace Cortex

public section

open Imperative Lambda

abbrev LBlock := DetBlock Label IRCmd Core.Expression
abbrev LCFG := DetCFG Core.Expression IRCmd

structure Pass where
  name : String
  run : Program → Except String Program

def Pass.onUnordered (name : String) (run : UnorderedProgram → Except String UnorderedProgram) : Pass where
  name
  run
    | .unordered p => .unordered <$> run p
    | .ordered _ => .error s!"Internal error: pass '{name}' cannot run on an ordered Cortex program"

def mkFvar (n : String) : Expr := .fvar () ⟨n, ()⟩ none
def mkOp (n : String) : Expr := .op () ⟨n, ()⟩ none
def mkApp (f : Expr) (args : List Expr) : Expr := args.foldl (fun acc a => .app () acc a) f
def mkCall (n : String) (args : List Expr) : Expr := mkApp (mkOp n) args
def tt : Expr := .const () (.boolConst true)
def ff : Expr := .const () (.boolConst false)
def intLit (i : Int) : Expr := .const () (.intConst i)
def mono (t : LMonoTy) : LTy := .forAll [] t
def tcon (n : String) : LMonoTy := .tcons n []

partial def mangle : LMonoTy → String
  | .tcons n [] => n
  | .tcons n args => n ++ "$" ++ String.intercalate "$" (args.map mangle)
  | .bitvec n => s!"bv{n}"
  | .ftvar n => n

def freshLabel (base : String) (used : List String) : String :=
  if !used.contains base then base else
  let rec go (i : Nat) (fuel : Nat) : String :=
    match fuel with
    | 0 => s!"{base}{i}"
    | fuel + 1 => if used.contains s!"{base}{i}" then go (i + 1) fuel else s!"{base}{i}"
  go 1 (used.length + 1)

def conTyName? (t : LTy) : Option String :=
  match t with
  | .forAll [] (.tcons n []) => some n
  | _ => none

partial def baseOf (cs : List ConstrainedDecl) (name : String) (fuel : Nat := 32) : Option LMonoTy :=
  match fuel, cs.find? (·.name == name) with
  | 0, _ => none
  | _, none => none
  | fuel + 1, some c =>
    match c.base with
    | .forAll _ (.tcons b []) => (baseOf cs b fuel).orElse fun _ => some (.tcons b [])
    | .forAll _ t => some t

/-- The temporary that holds the value a field or element write stores, so the value is
checked against the field's or element's type as an assignment before it reaches the heap. -/
def fieldValueVar (n : Nat) : String := s!"$fieldValue{n}"

/-- The declared type of field `f`, which Cortex fields have monomorphic. -/
def fieldMono (p : UnorderedProgram) (f : FieldRef) : Except String LMonoTy :=
  match p.findField? f with
  | some fd => match fd.ty with
    | .forAll [] t => .ok t
    | _ => .error s!"polymorphic field {f.owner}.{f.field}"
  | none => .error s!"unknown field {f.owner}.{f.field}"

/-- The element type that an element read or write states, which is monomorphic. -/
def elemMono (ty : Core.Expression.Ty) : Except String LMonoTy :=
  match (ty : LTy) with
  | .forAll [] t => .ok t
  | _ => .error "polymorphic array element type"

partial def mapMonoTy (f : String → Option LMonoTy) : LMonoTy → LMonoTy
  | .tcons n [] => (f n).getD (.tcons n [])
  | .tcons n args => .tcons n (args.map (mapMonoTy f))
  | t => t

def mapLTy (f : String → Option LMonoTy) : LTy → LTy
  | .forAll vs t => .forAll vs (mapMonoTy f t)

partial def mapExprTys (f : String → Option LMonoTy) : Expr → Expr
  | .op m o ty => .op m o (ty.map (mapMonoTy f))
  | .fvar m n ty => .fvar m n (ty.map (mapMonoTy f))
  | .abs m n ty e => .abs m n (ty.map (mapMonoTy f)) (mapExprTys f e)
  | .quant m k n ty tr e => .quant m k n (ty.map (mapMonoTy f)) (mapExprTys f tr) (mapExprTys f e)
  | .app m a b => .app m (mapExprTys f a) (mapExprTys f b)
  | .ite m c t e => .ite m (mapExprTys f c) (mapExprTys f t) (mapExprTys f e)
  | .eq m a b => .eq m (mapExprTys f a) (mapExprTys f b)
  | e => e

partial def mapExpr (f : Expr → Option Expr) (e : Expr) : Expr :=
  match f e with
  | some e' => e'
  | none =>
    match e with
    | .abs m n ty b => .abs m n ty (mapExpr f b)
    | .quant m k n ty tr b => .quant m k n ty (mapExpr f tr) (mapExpr f b)
    | .app m a b => .app m (mapExpr f a) (mapExpr f b)
    | .ite m c t e => .ite m (mapExpr f c) (mapExpr f t) (mapExpr f e)
    | .eq m a b => .eq m (mapExpr f a) (mapExpr f b)
    | e => e

def substFvars (σ : List (String × Expr)) (e : Expr) : Expr :=
  mapExpr (fun
    | .fvar _ n _ => σ.lookup n.name
    | _ => none) e

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

def mapExprOrNondet (g : Expr → Expr) : ExprOrNondet Core.Expression → ExprOrNondet Core.Expression
  | .det e => .det (g e)
  | .nondet => .nondet

def mapBaseCmd (g : Expr → Expr) (t : LTy → LTy) : Cmd Core.Expression → Cmd Core.Expression
  | .init x ty e md => .init x (t ty) (mapExprOrNondet g e) md
  | .set x e md => .set x (mapExprOrNondet g e) md
  | .assert l b md => .assert l (g b) md
  | .assume l b md => .assume l (g b) md
  | .cover l b md => .cover l (g b) md

def mapCmdExprs (g : Expr → Expr) (t : LTy → LTy) : IRCmd → IRCmd
  | .cmd c => .cmd (mapBaseCmd g t c)
  | .cast x ty e m md => .cast x ty (g e) m md
  | .new x ty md => .new x ty md
  | .readField x o f md => .readField x (g o) f md
  | .writeField o f v md => .writeField (g o) f (g v) md
  | .instanceOf x o ty md => .instanceOf x (g o) ty md
  | .newArray x ty len md => .newArray x ty (g len) md
  | .readElem x a i ty md => .readElem x (g a) (g i) (t ty) md
  | .writeElem a i v ty md => .writeElem (g a) (g i) (g v) (t ty) md
  | .arrayLength x a md => .arrayLength x (g a) md
  | .call lhs p args md => .call lhs p (args.map g) md
  | .virtualCall lhs o meth args md => .virtualCall lhs o meth (args.map g) md
  | .throw e md => .throw (g e) md

def mapTransfer (g : Expr → Expr) : DetTransferCmd Label Core.Expression → DetTransferCmd Label Core.Expression
  | .condGoto c lt lf md => .condGoto (g c) lt lf md
  | .finish md => .finish md

def mapBlock (h : IRCmd → List IRCmd) (g : Expr → Expr) (b : LBlock) : LBlock :=
  { cmds := b.cmds.flatMap h, transfer := mapTransfer g b.transfer }

def mapBody (h : IRCmd → List IRCmd) (g : Expr → Expr) (b : Body) : Body :=
  { b with cfg := { b.cfg with blocks := b.cfg.blocks.map fun (l, blk) => (l, mapBlock h g blk) } }

def mapProgramTys (f : String → Option LMonoTy) (p : UnorderedProgram) : UnorderedProgram :=
  let t := mapLTy f
  let g := mapExprTys f
  let params := fun (ps : List (Core.Expression.Ident × LTy)) => ps.map fun (x, ty) => (x, t ty)
  { p with
    composites := p.composites.map fun c =>
      { c with fields := c.fields.map fun fd => { fd with ty := t fd.ty }, elem := c.elem.map t }
    constrained := p.constrained.map fun c => { c with base := t c.base, constraint := g c.constraint }
    globals := params p.globals
    globalInit := p.globalInit.map (mapBaseCmd g t)
    procedures := p.procedures.map fun pr =>
      { pr with
        inputs := params pr.inputs
        outputs := params pr.outputs
        body := pr.body.map (mapBody (fun c => [mapCmdExprs g t c]) g) } }

def mapConstrTys (f : String → Option LMonoTy) (c : LConstr Unit) : LConstr Unit :=
  { c with args := c.args.map fun (n, ty) => (n, mapMonoTy f ty) }

def mapDatatypeTys (f : String → Option LMonoTy) (dt : LDatatype Unit) : LDatatype Unit where
  name := dt.name
  typeArgs := dt.typeArgs
  constrs := dt.constrs.map (mapConstrTys f)
  constrs_ne := by have := dt.constrs_ne; simpa using this

def UnorderedProgram.mapTys (f : String → Option LMonoTy) (p : UnorderedProgram) : UnorderedProgram :=
  { mapProgramTys f p with datatypes := p.datatypes.map (mapDatatypeTys f) }

def UnorderedProgram.mapProcedures (f : Procedure → Procedure) (p : UnorderedProgram) : UnorderedProgram :=
  { p with procedures := p.procedures.map f }

def UnorderedProgram.refuseVirtualCalls (p : UnorderedProgram) (pass : String) : Except String Unit :=
  if p.hasVirtualCall then .error s!"Cortex `virtualCall` must be lowered by LowerDispatch before {pass}"
  else .ok ()

def Body.refuseHandlers (b : Body) (stage : String) : Except String Unit :=
  if b.handlers.isEmpty then .ok ()
  else .error s!"exception handlers must be lowered before {stage}"

/-- The variables that a command declares or assigns. -/
def assignedNames : IRCmd → List String
  | .cmd (.init x ..) | .cmd (.set x ..) | .cast x .. => [x.name]
  | .call lhs .. | .virtualCall lhs .. => lhs.map (·.name)
  | .new x .. | .readField x .. | .instanceOf x .. => [x.name]
  | .newArray x .. | .readElem x .. | .arrayLength x .. => [x.name]
  | _ => []

/-- The variables that the commands of `b` declare or assign. -/
def Body.assignedNames (b : Body) : List String :=
  b.cfg.blocks.flatMap fun (_, blk) => blk.cmds.flatMap Cortex.assignedNames

def Body.maxFresh (b : Body) : Nat := b.cfg.blocks.length

end

end Cortex
