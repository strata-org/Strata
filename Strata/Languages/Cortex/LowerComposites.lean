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

def descendants (p : Program) (t : TypeName) : List TypeName :=
  (p.composites.filter fun c => p.isSubtype c.name t).map (·.name)

def compositeBinder : String := "$composite"

def tagConstraint (p : Program) (c : TypeName) : Expr :=
  let tag := typeTagOf (mkFvar compositeBinder)
  match (descendants p c).map (fun d => (Lambda.LExpr.eq () tag (tagOf d) : Expr)) with
  | [] => ff
  | e :: es => es.foldl (fun acc x => mkCall "Bool.Or" [acc, x]) e

def compositeConstraint (p : Program) (c : CompositeDecl) : ConstrainedDecl :=
  { name := c.name, base := mono (tcon compositeTy), binder := ⟨compositeBinder, ()⟩,
    constraint := tagConstraint p c.name, free := true }

def typeTagDecl (p : Program) : Core.Decl :=
  let ctors : List (LConstr Unit) := p.composites.map fun c => { name := ⟨tagCtor c.name, ()⟩, args := [] }
  let ctors := if ctors.isEmpty then [{ name := ⟨"$MkTypeTag", ()⟩, args := [] }] else ctors
  have h : ctors.length != 0 := by
    simp only [ctors]; split <;> simp_all
  .type (.data [{ name := typeTagTy, typeArgs := [], constrs := ctors, constrs_ne := h }]) .empty

def compositeCtorDef : LConstr Unit :=
  { name := ⟨compositeCtor, ()⟩, args := [(⟨"ref", ()⟩, .int), (⟨"typeTag", ()⟩, tcon typeTagTy)] }

def compositeDt : LDatatype Unit :=
  { name := compositeTy, typeArgs := [], constrs := [compositeCtorDef], constrs_ne := by simp }

def compositeDecl : Core.Decl := .type (.data [compositeDt]) .empty

def run (m : Module) : Except String Module :=
  let p := m.program
  let m := m.mapTys fun n => if n.startsWith "$Any" then some (tcon compositeTy) else none
  let m := { m with program := { m.program with
    constrained := p.composites.map (compositeConstraint p) ++ m.program.constrained } }
  .ok { m with decls := [typeTagDecl p, compositeDecl] ++ m.decls }

def pass : Pass := { name := "LowerComposites", run }

end

end Cortex.LowerComposites
