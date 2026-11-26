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

structure CompositeDecl where
  name : TypeName
  extending : List TypeName
  fields : List FieldDecl

/-- The type `Array elem` of the arrays whose elements have type `elem`. It is built in: a
program uses it for any element type, an array type included, without declaring it. The
element type identifies the array type: for constrained types `a` and `b` over one base type,
`Array a`, `Array b` and the array type of the base type are three different types. -/
@[expose] def arrayTy (elem : Lambda.LMonoTy) : Lambda.LMonoTy := .tcons "Array" [elem]

/-- The element type of an array type. -/
@[expose] def arrayElem? : Lambda.LMonoTy → Option Lambda.LMonoTy
  | .tcons "Array" [elem] => some elem
  | _ => none

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
  /-- Sets `lhs` to whether the type of the object that `obj` refers to is a subtype of `ty`,
  a composite or an array type. -/
  | instanceOf (lhs : Core.Expression.Ident) (obj : Expr) (ty : Core.Expression.Ty) (md : MD)
  /-- Allocates an array of type `Array elemTy` with `len` elements, each the default value of
  `elemTy`, or of its base type when `elemTy` is a constrained type. A negative `len` is a
  stuck state. -/
  | newArray (lhs : Core.Expression.Ident) (elemTy : Core.Expression.Ty) (len : Expr) (md : MD)
  /-- Reads the element at `index`, an `int`. `elemTy` is the element type that the command
  reads the array at: the type of the array that `arr` refers to is a subtype of
  `Array elemTy`, and any other array is a stuck state. An index outside the array is a stuck
  state. -/
  | readElem (lhs : Core.Expression.Ident) (arr : Expr) (index : Expr) (elemTy : Core.Expression.Ty) (md : MD)
  /-- Writes the element at `index`, with the conventions of `readElem`. -/
  | writeElem (arr : Expr) (index : Expr) (rhs : Expr) (elemTy : Core.Expression.Ty) (md : MD)
  /-- Reads the number of elements, an `int` that is fixed when the array is allocated. -/
  | arrayLength (lhs : Core.Expression.Ident) (arr : Expr) (md : MD)
  /-- Sets `lhs` to whether the type of the object that `obj` refers to is a subtype of the
  element type of the array that `arr` refers to. The element type is that of the array's own
  type, whatever the type of the variable that holds the array. An array whose element type
  is not a reference type is a stuck state. -/
  | instanceOfComponent (lhs : Core.Expression.Ident) (obj : Expr) (arr : Expr) (md : MD)
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

/-- A postcondition, checked when its procedure returns normally, with this
postcondition's location and property summary. Its condition reads the outputs and
the globals at return, an input that is not an output at entry, and `old x` (the
variable `CoreIdent.mkOld x`) at entry for a global or an input and output `x`. -/
structure Postcondition where
  label : String
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
  /-- Whether the procedure models code that Strata does not see, such as a library method:
  its contract is a model of that code. The lowering to Core marks every call to it
  (`Core.externalAssumePrefix`), so a counterexample through the call is not reported as a
  failure. A procedure that is not external, such as a primitive of the API, means exactly its
  contract, with or without a body. -/
  external : Bool := false
  ensures : List Postcondition := []

structure UnorderedProgram where
  composites : List CompositeDecl
  /-- Whether `Array S` is a subtype of `Array T` for a reference type `S` that is a subtype
  of another one `T`. -/
  covariantArrays : Bool := false
  /-- The composites that every array type is a subtype of. -/
  arrayParents : List TypeName := []
  constrained : List ConstrainedDecl := []
  globals : List (Core.Expression.Ident × Core.Expression.Ty) := []
  globalInit : List (Cmd Core.Expression) := []
  datatypes : List (Lambda.LDatatype Unit) := []
  opaqueTypes : List TypeConstructor := []
  functions : List (Lambda.LFunc Core.CoreLParams) := []
  procedures : List Procedure

inductive OrderedDecl where
  | datatypes (ds : List (Lambda.LDatatype Unit))
  | opaqueType (tc : TypeConstructor)
  | function (f : Lambda.LFunc Core.CoreLParams)
  | procedure (p : Procedure)

structure OrderedProgram where
  decls : List OrderedDecl

inductive Program where
  | unordered (p : UnorderedProgram)
  | ordered (p : OrderedProgram)

@[expose] def UnorderedProgram.findComposite? (p : UnorderedProgram) (n : TypeName) : Option CompositeDecl :=
  p.composites.find? (·.name == n)

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

/-- Whether an object of type `sub` is one of type `sup`. A composite is a subtype of the
composites it extends, and every array type of `arrayParents` and of what they extend. An
array type is a subtype of itself and, with `covariantArrays`, `Array S` is one of `Array T`
when `S` is one of `T`. Only reference types have a subtype other than themselves, so an array
of any other element type is a subtype of no other array type. -/
@[expose] def UnorderedProgram.isSubtypeTy (p : UnorderedProgram) : Lambda.LMonoTy → Lambda.LMonoTy → Bool
  | .tcons "Array" [s], .tcons "Array" [t] => s == t || (p.covariantArrays && p.isSubtypeTy s t)
  | .tcons "Array" [_], .tcons c [] => p.arrayParents.any (p.isSubtype · c)
  | .tcons s [], .tcons t [] => p.isSubtype s t
  | _, _ => false

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

@[expose] def UnorderedProgram.dispatch (p : UnorderedProgram) (owner : TypeName) (method : String)
    (dyn : Lambda.LMonoTy) : ProcName :=
  match (p.overriders owner method).find? fun d => p.isSubtypeTy dyn (.tcons d []) with
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

@[expose] def IRCmd.md : IRCmd → MD
  | .cmd (.init _ _ _ md) | .cmd (.set _ _ md) | .cmd (.assert _ _ md) | .cmd (.assume _ _ md)
  | .cmd (.cover _ _ md) => md
  | .cast _ _ _ _ md | .new _ _ md | .readField _ _ _ md | .writeField _ _ _ md | .instanceOf _ _ _ md
  | .call _ _ _ md | .virtualCall _ _ _ _ md | .throw _ md => md
  | .newArray _ _ _ md | .readElem _ _ _ _ md | .writeElem _ _ _ _ md | .arrayLength _ _ md
  | .instanceOfComponent _ _ _ md => md

@[expose] def UnorderedProgram.hasVirtualCall (p : UnorderedProgram) : Bool :=
  p.procedures.any fun pr => match pr.body with
    | some b => b.cfg.blocks.any fun (_, blk) => blk.cmds.any IRCmd.isVirtualCall
    | none => false

/-- Whether `h` catches a thrown object of type `ty`. -/
@[expose] def Handler.catches (p : UnorderedProgram) (h : Handler) (ty : Lambda.LMonoTy) : Bool :=
  match h.catchType with
  | none => true
  | some c => p.isSubtypeTy ty (.tcons c [])

@[expose] def Body.handlerFor? (p : UnorderedProgram) (b : Body) (l : Label) (ty : Lambda.LMonoTy) :
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
