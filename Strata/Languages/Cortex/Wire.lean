/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Cortex.Module
public import Strata.Util.FileRange
public import Strata.Util.Provenance
import Strata.Util.IonDeserializer

/-!
# Cortex wire format

A serializable form of a Cortex program, for frontends that emit Cortex
directly. Its Ion encoding is the one `getIonSerializer%` gives the Java side.

Expressions name Core functions by their factory names (`Int.Add`,
`Bool.And`, …); Core's type checker resolves them. Types are primitives or
the names of composites and constrained types the program declares. Every
local, a handler's binder included, is declared by an `init` before it is
assigned.
-/

namespace Cortex.Wire

public section

open Imperative Lambda

inductive Ty where
  | int
  | bool
  | string
  | real
  | bv (width : Nat)
  | named (name : String)
  deriving Repr, Inhabited

inductive Expr where
  | var (name : String)
  | int (value : Int)
  | bool (value : Bool)
  | str (value : String)
  | bv (width : Nat) (value : Int)
  | op (name : String) (args : List Expr)
  | ite (cond thenExpr elseExpr : Expr)
  | eq (lhs rhs : Expr)
  deriving Repr, Inhabited

inductive Cmd where
  | init (name : String) (ty : Ty) (value : Option Expr) (source : Strata.FileRange)
  | set (name : String) (value : Option Expr) (source : Strata.FileRange)
  | assert (label : String) (cond : Expr) (summary : Option String) (source : Strata.FileRange)
  | assume (label : String) (cond : Expr) (source : Strata.FileRange)
  | new (lhs : String) (ty : String) (source : Strata.FileRange)
  | readField (lhs : String) (obj : Expr) (owner field : String) (source : Strata.FileRange)
  | writeField (obj : Expr) (owner field : String) (rhs : Expr) (source : Strata.FileRange)
  | instanceOf (lhs : String) (obj : Expr) (ty : String) (source : Strata.FileRange)
  | call (lhs : List String) (proc : String) (args : List Expr) (source : Strata.FileRange)
  | virtualCall (lhs : List String) (owner method : String) (args : List Expr) (source : Strata.FileRange)
  | throw (exn : Expr) (summary : Option String) (source : Strata.FileRange)
  deriving Repr, Inhabited

inductive Transfer where
  | goto (target : String) (source : Strata.FileRange)
  | condGoto (cond : Expr) (thenTarget elseTarget : String) (source : Strata.FileRange)
  | finish (source : Strata.FileRange)
  deriving Repr, Inhabited

structure Block where
  label : String
  cmds : List Cmd
  transfer : Transfer
  deriving Repr, Inhabited

structure Handler where
  covered : List String
  catchType : Option String
  binder : String
  target : String
  source : Strata.FileRange
  deriving Repr, Inhabited

structure Body where
  entry : String
  blocks : List Block
  handlers : List Handler
  deriving Repr, Inhabited

structure Param where
  name : String
  ty : Ty
  deriving Repr, Inhabited

/-- A precondition over the procedure's inputs, checked at each call with the
call's location and `summary`. -/
structure Precondition where
  cond : Expr
  summary : Option String
  deriving Repr, Inhabited

structure Procedure where
  name : String
  inputs : List Param
  outputs : List Param
  throws : Option String
  requires : List Precondition
  body : Option Body
  entry : Bool
  source : Strata.FileRange
  deriving Repr, Inhabited

structure Field where
  name : String
  ty : Ty
  deriving Repr, Inhabited

structure Composite where
  name : String
  extending : List String
  fields : List Field
  deriving Repr, Inhabited

structure Constrained where
  name : String
  base : Ty
  binder : String
  constraint : Expr
  witness : Option Expr
  deriving Repr, Inhabited

structure Program where
  composites : List Composite
  constrained : List Constrained
  procedures : List Procedure
  /-- Preludes whose procedures the program calls, such as `"java"`; see
  `Cortex.Preludes`. -/
  preludes : List String := []
  deriving Repr, Inhabited

def Ty.toMono : Ty → LMonoTy
  | .int => .int
  | .bool => .bool
  | .string => .string
  | .real => .real
  | .bv w => .bitvec w
  | .named n => .tcons n []

def Ty.toLTy (t : Ty) : LTy := .forAll [] t.toMono

partial def Expr.toCore : Expr → Cortex.Expr
  | .var n => mkFvar n
  | .int i => intLit i
  | .bool b => if b then tt else ff
  | .str s => .const () (.strConst s)
  | .bv w v => .const () (.bitvecConst w (BitVec.ofInt w v))
  | .op n [] => mkOp n
  | .op n args => mkCall n (args.map Expr.toCore)
  | .ite c t e => .ite () c.toCore t.toCore e.toCore
  | .eq a b => .eq () a.toCore b.toCore

/-- A range whose file path is empty stands for no location. -/
def mdOf (source : Strata.FileRange) : Cortex.MD :=
  match source.file with
  | .file "" => .empty
  | _ => MetaData.ofProvenance (Strata.Provenance.ofSourceRange source.file source.range)

def ident (n : String) : Core.Expression.Ident := ⟨n, ()⟩

def Cmd.toCortex : Cmd → IRCmd
  | .init x ty v src => .cmd (.init (ident x) ty.toLTy (v.elim .nondet (.det ·.toCore)) (mdOf src))
  | .set x v src => .cmd (.set (ident x) (v.elim .nondet (.det ·.toCore)) (mdOf src))
  | .assert l c summary src =>
    let md := mdOf src
    let md := match summary with
      | some s => md.pushElem MetaData.propertySummary (.msg s)
      | none => md
    .cmd (.assert l c.toCore md)
  | .assume l c src => .cmd (.assume l c.toCore (mdOf src))
  | .new x ty src => .new (ident x) ty (mdOf src)
  | .readField x o owner f src => .readField (ident x) o.toCore { owner, field := f } (mdOf src)
  | .writeField o owner f v src => .writeField o.toCore { owner, field := f } v.toCore (mdOf src)
  | .instanceOf x o ty src => .instanceOf (ident x) o.toCore ty (mdOf src)
  | .call lhs p args src => .call (lhs.map ident) p (args.map Expr.toCore) (mdOf src)
  | .virtualCall lhs o m args src => .virtualCall (lhs.map ident) o m (args.map Expr.toCore) (mdOf src)
  | .throw e summary src =>
    let md := mdOf src
    .throw e.toCore (match summary with
      | some s => md.pushElem MetaData.propertySummary (.msg s)
      | none => md)

def Transfer.toCortex : Transfer → DetTransferCmd Cortex.Label Core.Expression
  | .goto l src => .goto l (mdOf src)
  | .condGoto c lt lf src => .condGoto c.toCore lt lf (mdOf src)
  | .finish src => .finish (mdOf src)

def Transfer.targets : Transfer → List String
  | .goto l _ => [l]
  | .condGoto _ lt lf _ => [lt, lf]
  | .finish _ => []

def checkUnique (what : String) (names : List String) : Except String Unit := do
  let mut seen : Std.HashSet String := {}
  for n in names do
    if seen.contains n then throw s!"duplicate {what} '{n}'"
    seen := seen.insert n

def Body.toCortex (proc : String) (b : Body) : Except String Cortex.Body := do
  checkUnique s!"block label in '{proc}'" (b.blocks.map (·.label))
  let labels := b.blocks.map (·.label)
  unless labels.contains b.entry do throw s!"'{proc}': entry block '{b.entry}' is not a block"
  for blk in b.blocks do
    for t in blk.transfer.targets do
      unless labels.contains t do throw s!"'{proc}': block '{blk.label}' jumps to unknown block '{t}'"
  let blocks := b.blocks.map fun blk =>
    (blk.label, ({ cmds := blk.cmds.map Cmd.toCortex, transfer := blk.transfer.toCortex } : LBlock))
  let handlers := b.handlers.map fun h =>
    ({ covered := h.covered, catchType := h.catchType, binder := ident h.binder, target := h.target,
       md := mdOf h.source } : Cortex.Handler)
  return { cfg := { entry := b.entry, blocks }, handlers }

def Procedure.toCortex (p : Procedure) : Except String Cortex.Procedure := do
  let params := fun (ps : List Param) => ps.map fun q => (ident q.name, q.ty.toLTy)
  checkUnique s!"parameter of '{p.name}'" ((p.inputs ++ p.outputs).map (·.name))
  let body ← p.body.mapM (Body.toCortex p.name)
  let md := mdOf p.source
  let md := if p.entry then md.pushElem MetaData.interpretEntry (.switch true) else md
  let requires := p.requires.map fun pre =>
    ({ cond := pre.cond.toCore,
       md := match pre.summary with
         | some s => (MetaData.empty : Cortex.MD).pushElem MetaData.propertySummary (.msg s)
         | none => .empty } : Cortex.Precondition)
  return { name := p.name, inputs := params p.inputs, outputs := params p.outputs, throws := p.throws,
           body, md, requires }

def Program.checkCallArities (p : Program) : Except String Unit := do
  let arities : Std.HashMap String (Nat × Nat) :=
    p.procedures.foldl (fun m q => m.insert q.name (q.inputs.length, q.outputs.length)) {}
  let check := fun (caller callee : String) (args results : Nat) => do
    match arities[callee]? with
    | none => pure ()
    | some (ins, outs) =>
      unless args == ins do
        throw s!"'{caller}': call to '{callee}' passes {args} arguments, but it takes {ins}"
      unless results == outs do
        throw s!"'{caller}': call to '{callee}' assigns {results} results, but it returns {outs}"
  for q in p.procedures do
    for b in q.body.toList do
      for blk in b.blocks do
        for c in blk.cmds do
          match c with
          | .call lhs proc args _ => check q.name proc args.length lhs.length
          | .virtualCall lhs owner method args _ =>
            check q.name (Cortex.implName owner method) args.length lhs.length
          | _ => pure ()

def Program.toCortex (p : Program) : Except String Cortex.UnorderedProgram := do
  checkUnique "composite" (p.composites.map (·.name))
  checkUnique "constrained type" (p.constrained.map (·.name))
  checkUnique "procedure" (p.procedures.map (·.name))
  let composites := p.composites.map fun c =>
    ({ name := c.name, extending := c.extending,
       fields := c.fields.map fun f => { name := f.name, ty := f.ty.toLTy } } : Cortex.CompositeDecl)
  for c in composites do
    for parent in c.extending do
      unless composites.any (·.name == parent) do
        throw s!"composite '{c.name}' extends unknown composite '{parent}'"
  let constrained := p.constrained.map fun c =>
    ({ name := c.name, base := c.base.toLTy, binder := ident c.binder, constraint := c.constraint.toCore,
       witness := c.witness.map Expr.toCore } : Cortex.ConstrainedDecl)
  let procedures ← p.procedures.mapM Procedure.toCortex
  p.checkCallArities
  let program : Cortex.UnorderedProgram := { composites, constrained, procedures }
  program.checkHandlers
  return program

private partial def deserializeProgram : ByteArray → Except Std.Format Program :=
  getIonDeserializer% Program

def readProgram (bytes : ByteArray) : Except String Program :=
  match deserializeProgram bytes with
  | .ok p => .ok p
  | .error e => .error s!"Failed to deserialize Cortex program: {e}"

end

end Cortex.Wire
