/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.Procedure
public import Strata.Languages.Core.Expressions
public import Strata.DL.Lambda.TypeConstructor
public import Strata.DL.Lambda.TypeFactory

namespace Cortex

public section

open Imperative

abbrev TypeName := String
abbrev FieldName := String
abbrev ProcName := String
abbrev Label := String

abbrev Expr := Core.Expression.Expr
abbrev MD := MetaData Core.Expression

structure FieldDecl where
  name : FieldName
  ty : Core.Expression.Ty

/-- A reference type. With `elem`, it is an array type whose objects hold elements of that
type, and it declares no fields. -/
structure CompositeDecl where
  name : TypeName
  extending : List TypeName
  fields : List FieldDecl
  elem : Option Core.Expression.Ty := none

structure ConstrainedDecl where
  name : TypeName
  base : Core.Expression.Ty
  binder : Core.Expression.Ident
  constraint : Expr
  free : Bool := false
  witness : Option Expr := none

structure FieldRef where
  owner : TypeName
  field : FieldName
  deriving DecidableEq, Repr, Inhabited

inductive CastMode where
  | check
  | assume
  deriving DecidableEq, Repr, Inhabited

inductive IRCmd where
  | cmd (c : Cmd Core.Expression)
  | cast (lhs : Core.Expression.Ident) (ty : TypeName) (e : Expr) (mode : CastMode) (md : MD)
  | new (lhs : Core.Expression.Ident) (ty : TypeName) (md : MD)
  | readField (lhs : Core.Expression.Ident) (obj : Expr) (field : FieldRef) (md : MD)
  | writeField (obj : Expr) (field : FieldRef) (rhs : Expr) (md : MD)
  | instanceOf (lhs : Core.Expression.Ident) (obj : Expr) (ty : TypeName) (md : MD)
  /-- Allocates an array of the declared array type `ty` with `len` elements, each the default
  value of the element type. A negative `len` is a stuck state. -/
  | newArray (lhs : Core.Expression.Ident) (ty : TypeName) (len : Expr) (md : MD)
  /-- Reads the element at `index`, an `int`. `elemTy` is the element type of the array that
  `arr` refers to. An index outside the array is a stuck state. -/
  | readElem (lhs : Core.Expression.Ident) (arr : Expr) (index : Expr) (elemTy : Core.Expression.Ty) (md : MD)
  /-- Writes the element at `index`, with the conventions of `readElem`. -/
  | writeElem (arr : Expr) (index : Expr) (rhs : Expr) (elemTy : Core.Expression.Ty) (md : MD)
  /-- Reads the number of elements, an `int` that is fixed when the array is allocated. -/
  | arrayLength (lhs : Core.Expression.Ident) (arr : Expr) (md : MD)
  | call (lhs : List Core.Expression.Ident) (proc : ProcName) (args : List Expr) (md : MD)
  | virtualCall (lhs : List Core.Expression.Ident) (owner : TypeName) (method : String) (args : List Expr)
      (md : MD)
  | throw (exn : Expr) (md : MD)

structure Handler where
  covered : List Label
  catchType : Option TypeName
  binder : Core.Expression.Ident
  target : Label
  md : MD

abbrev ExnTable := List Handler

structure Body where
  cfg : DetCFG Core.Expression IRCmd
  handlers : ExnTable

/-- A precondition over a procedure's inputs: checked at each call, with the
call's location and this precondition's property summary, and assumed by the
body. -/
structure Precondition where
  cond : Expr
  md : MD := .empty

structure Procedure where
  name : ProcName
  inputs : List (Core.Expression.Ident × Core.Expression.Ty)
  outputs : List (Core.Expression.Ident × Core.Expression.Ty)
  throws : Option TypeName
  body : Option Body
  md : MD := .empty
  requires : List Precondition := []

structure UnorderedProgram where
  composites : List CompositeDecl
  constrained : List ConstrainedDecl := []
  globals : List (Core.Expression.Ident × Core.Expression.Ty) := []
  globalInit : List (Cmd Core.Expression) := []
  datatypes : List (Lambda.LDatatype Unit) := []
  opaqueTypes : List TypeConstructor := []
  procedures : List Procedure

inductive OrderedDecl where
  | datatypes (ds : List (Lambda.LDatatype Unit))
  | opaqueType (tc : TypeConstructor)
  | procedure (p : Procedure)

structure OrderedProgram where
  decls : List OrderedDecl

inductive Program where
  | unordered (p : UnorderedProgram)
  | ordered (p : OrderedProgram)

@[expose] def UnorderedProgram.findComposite? (p : UnorderedProgram) (n : TypeName) : Option CompositeDecl :=
  p.composites.find? (·.name == n)

/-- The element type of array type `n`. -/
@[expose] def UnorderedProgram.arrayElem? (p : UnorderedProgram) (n : TypeName) : Option Core.Expression.Ty :=
  (p.findComposite? n).bind (·.elem)

@[expose] def UnorderedProgram.findProcedure? (p : UnorderedProgram) (n : ProcName) : Option Procedure :=
  p.procedures.find? (·.name == n)

@[expose] def UnorderedProgram.findField? (p : UnorderedProgram) (f : FieldRef) : Option FieldDecl :=
  (p.findComposite? f.owner).bind fun c => c.fields.find? (·.name == f.field)

@[expose] def UnorderedProgram.parents (p : UnorderedProgram) (n : TypeName) : List TypeName :=
  ((p.findComposite? n).map (·.extending)).getD []

@[expose] def UnorderedProgram.isSubtype (p : UnorderedProgram) (sub sup : TypeName) : Bool :=
  go (p.composites.length + 1) [sub]
where
  go : Nat → List TypeName → Bool
    | 0, _ => false
    | _, [] => false
    | fuel + 1, frontier => frontier.contains sup || go fuel (frontier.flatMap p.parents).eraseDups

@[expose] def implName (c : TypeName) (method : String) : ProcName := s!"{c}${method}"

@[expose] def UnorderedProgram.ancestors (p : UnorderedProgram) (n : TypeName) : List TypeName :=
  go (p.composites.length + 1) (p.parents n).eraseDups []
where
  go : Nat → List TypeName → List TypeName → List TypeName
    | 0, _, seen => seen
    | _, [], seen => seen
    | fuel + 1, frontier, seen =>
      let seen := seen ++ frontier.filter (!seen.contains ·)
      go fuel ((frontier.flatMap p.parents).eraseDups.filter (!seen.contains ·)) seen

@[expose] def UnorderedProgram.overriders (p : UnorderedProgram) (owner : TypeName) (method : String) : List TypeName :=
  let ds := p.composites.filter fun c =>
    c.name != owner && (p.ancestors c.name).contains owner &&
      (p.findProcedure? (implName c.name method)).isSome
  (ds.map (·.name)).mergeSort fun a b => (p.ancestors a).length ≥ (p.ancestors b).length

@[expose] def UnorderedProgram.dispatch (p : UnorderedProgram) (owner : TypeName) (method : String) (dyn : TypeName) :
    ProcName :=
  match (p.overriders owner method).find? (p.isSubtype dyn ·) with
  | some d => implName d method
  | none => implName owner method

@[expose] def UnorderedProgram.virtualTargets (p : UnorderedProgram) (owner : TypeName) (method : String) :
    List ProcName :=
  implName owner method :: (p.overriders owner method).map (implName · method)

@[expose] def IRCmd.callees (p : UnorderedProgram) : IRCmd → List ProcName
  | .call _ q _ _ => [q]
  | .virtualCall _ o m _ _ => p.virtualTargets o m
  | _ => []

@[expose] def IRCmd.isVirtualCall : IRCmd → Bool
  | .virtualCall .. => true
  | _ => false

@[expose] def UnorderedProgram.hasVirtualCall (p : UnorderedProgram) : Bool :=
  p.procedures.any fun pr => match pr.body with
    | some b => b.cfg.blocks.any fun (_, blk) => blk.cmds.any IRCmd.isVirtualCall
    | none => false

@[expose] def Handler.catches (p : UnorderedProgram) (h : Handler) (ty : TypeName) : Bool :=
  match h.catchType with
  | none => true
  | some c => p.isSubtype ty c

@[expose] def Body.handlerFor? (p : UnorderedProgram) (b : Body) (l : Label) (ty : TypeName) :
    Option Handler :=
  b.handlers.find? fun h => h.covered.contains l && h.catches p ty

@[expose] def Body.checkHandlers (p : UnorderedProgram) (b : Body) : Except String Unit := do
  let labels := b.cfg.labels
  for h in b.handlers do
    unless labels.contains h.target do
      throw s!"exception handler target '{h.target}' is not a block"
    for l in h.covered do
      unless labels.contains l do
        throw s!"exception handler covers unknown block '{l}'"
    if let some t := h.catchType then
      unless (p.findComposite? t).isSome do
        throw s!"exception handler catches unknown type '{t}'"

@[expose] def UnorderedProgram.checkHandlers (p : UnorderedProgram) : Except String Unit :=
  p.procedures.forM fun proc => match proc.body with
    | some b => b.checkHandlers p
    | none => pure ()

end

end Cortex
