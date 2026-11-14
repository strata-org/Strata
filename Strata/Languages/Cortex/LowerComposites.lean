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

def descendants (p : UnorderedProgram) (t : TypeName) : List TypeName :=
  (p.composites.filter fun c => p.isSubtype c.name t).map (·.name)

def compositeBinder : String := "$composite"

def tagConstraint (p : UnorderedProgram) (c : TypeName) : Expr :=
  let tag := typeTagOf (mkFvar compositeBinder)
  match (descendants p c).map (fun d => (Lambda.LExpr.eq Core.coreLoc tag (tagOf d) : Expr)) with
  | [] => ff
  | e :: es => es.foldl (fun acc x => mkCall "Bool.Or" [acc, x]) e

def compositeConstraint (p : UnorderedProgram) (c : CompositeDecl) : ConstrainedDecl :=
  { name := c.name, base := mono (tcon compositeTy), binder := ⟨compositeBinder, ()⟩,
    constraint := tagConstraint p c.name, free := true }

def typeTagDt (p : UnorderedProgram) : LDatatype Unit :=
  let ctors : List (LConstr Unit) := p.composites.map fun c => { name := ⟨tagCtor c.name, ()⟩, args := [] }
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
  .ok { q with
    constrained := p.composites.map (compositeConstraint p) ++ q.constrained
    datatypes := [typeTagDt p, compositeDt] ++ q.datatypes }

def pass : Pass := Pass.onUnordered "LowerComposites" run

end

end Cortex.LowerComposites
