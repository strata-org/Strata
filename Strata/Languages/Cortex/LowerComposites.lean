/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Cortex.Module

namespace Cortex.LowerComposites

open Imperative Lambda

public section

def compositeTy : String := "$Composite"
def compositeCtor : String := "$MkComposite"
def typeTagTy : String := "$TypeTag"
def refAccessor : String := "$Composite..ref!"
def tagAccessor : String := "$Composite..typeTag!"
def tagCtor (c : TypeName) : String := s!"{c}$TypeTag"

def tagOf (c : TypeName) : Expr := mkOp (tagCtor c)
def refOf (e : Expr) : Expr := mkCall refAccessor [e]
def typeTagOf (e : Expr) : Expr := mkCall tagAccessor [e]

partial def arrayTysIn (t : LMonoTy) : List LMonoTy :=
  match t with
  | .tcons _ args => (if (arrayElem? t).isSome then [t] else []) ++ args.flatMap arrayTysIn
  | _ => []

def arrayTypes (p : UnorderedProgram) : List LMonoTy :=
  let ty := fun (t : LTy) => match t with | .forAll _ m => arrayTysIn m
  let elem := fun (t : LTy) => match t with | .forAll _ m => arrayTy m :: arrayTysIn m
  let params := fun (ps : List (Core.Expression.Ident × LTy)) => ps.flatMap (ty ·.2)
  let base : Imperative.Cmd Core.Expression → List LMonoTy := fun
    | .init _ t _ _ => ty t
    | _ => []
  let cmd : IRCmd → List LMonoTy := fun
    | .cmd c => base c
    | .instanceOf _ _ t _ => ty t
    | .newArray _ t _ _ | .readElem _ _ _ t _ | .writeElem _ _ _ t _ => elem t
    | _ => []
  (p.composites.flatMap (·.fields.flatMap (ty ·.ty)) ++ p.constrained.flatMap (ty ·.base)
    ++ p.datatypes.flatMap (·.constrs.flatMap (·.args.flatMap (arrayTysIn ·.2)))
    ++ params p.globals ++ p.globalInit.flatMap base
    ++ p.procedures.flatMap fun pr =>
      params pr.inputs ++ params pr.outputs
        ++ (pr.body.map (·.cfg.blocks.flatMap (·.2.cmds.flatMap cmd))).getD []).eraseDups

def arrayTag (t : LMonoTy) : TypeName := mangle t

def descendants (p : UnorderedProgram) (arrays : List LMonoTy) (t : TypeName) : List TypeName :=
  (p.composites.filter fun c => p.isSubtype c.name t).map (·.name) ++
    (arrays.filter fun a => p.isSubtypeTy a (tcon t)).map arrayTag

def compositeBinder : String := "$composite"

def tagConstraint (p : UnorderedProgram) (arrays : List LMonoTy) (c : TypeName) : Expr :=
  let tag := typeTagOf (mkFvar compositeBinder)
  match (descendants p arrays c).map (fun d => (Lambda.LExpr.eq Core.coreLoc tag (tagOf d) : Expr)) with
  | [] => ff
  | e :: es => es.foldl (fun acc x => mkCall "Bool.Or" [acc, x]) e

def compositeConstraint (p : UnorderedProgram) (arrays : List LMonoTy) (c : CompositeDecl) : ConstrainedDecl :=
  { name := c.name, base := mono (tcon compositeTy), binder := ⟨compositeBinder, ()⟩,
    constraint := tagConstraint p arrays c.name, free := true }

def typeTagDt (p : UnorderedProgram) (arrays : List LMonoTy) : LDatatype Unit :=
  let ctors : List (LConstr Unit) :=
    (p.composites.map (·.name) ++ arrays.map arrayTag).map fun n => { name := ⟨tagCtor n, ()⟩, args := [] }
  let ctors := if ctors.isEmpty then [{ name := ⟨"$MkTypeTag", ()⟩, args := [] }] else ctors
  have h : ctors.length != 0 := by
    simp only [ctors]; split <;> simp_all
  { name := typeTagTy, typeArgs := [], constrs := ctors, constrs_ne := h }

def compositeCtorDef : LConstr Unit :=
  { name := ⟨compositeCtor, ()⟩, args := [(⟨"ref", ()⟩, .int), (⟨"typeTag", ()⟩, tcon typeTagTy)] }

def compositeDt : LDatatype Unit :=
  { name := compositeTy, typeArgs := [], constrs := [compositeCtorDef], constrs_ne := by simp }

def run (p : UnorderedProgram) : Except String UnorderedProgram :=
  let q := p.mapTys fun n => if n.startsWith "$Any" then some (tcon compositeTy) else none
  let arrays := arrayTypes q
  .ok { q with
    constrained := p.composites.map (compositeConstraint p arrays) ++ q.constrained
    datatypes := [typeTagDt p arrays, compositeDt] ++ q.datatypes }

def pass : Pass := Pass.onUnordered "LowerComposites" run

end

end Cortex.LowerComposites
