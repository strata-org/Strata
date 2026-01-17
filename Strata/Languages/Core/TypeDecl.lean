/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/



import Strata.Languages.Core.Statement

---------------------------------------------------------------------

namespace Core

open Std (ToFormat Format format)
open Lambda

/-! # Strata Core Type Declarations -/

inductive Boundedness where
  | Finite
  | Infinite -- Default
  deriving Repr

structure TypeConstructor where
  -- (TODO) Add SMT support for Boogie's Finite types.
  bound    : Boundedness := .Infinite
  name     : String
  -- Boogie treats
  -- `type Foo a a;` // or type Foo _ _;
  -- the same as
  -- `type Foo a b;`
  -- That is, the exact identifier is irrelevant. As such, we only
  -- record the number of arguments in a type constructor here.
  numargs  : Nat
  deriving Repr

instance : ToFormat TypeConstructor where
  format t :=
    let args := (List.replicate t.numargs "_").toString
    f!"type {repr t.bound} {t.name} {args}"

def TypeConstructor.toType (t : TypeConstructor) : LTy :=
  let typeargs := List.replicate t.numargs "_ty"
  let ids := typeargs.mapIdx (fun i elem => (elem ++ toString i))
  let args := typeargs.mapIdx (fun i elem => LMonoTy.ftvar (elem ++ toString i))
  .forAll ids (.tcons t.name args)

open Lambda.LTy.Syntax in
/-- info: ∀[_ty0, _ty1, _ty2]. (Foo _ty0 _ty1 _ty2) -/
#guard_msgs in
#eval format $ TypeConstructor.toType { name := "Foo", numargs := 3 }

/-! # Strata Core Type Synonyms -/

structure TypeSynonym where
  name     : String
  -- Unlike in `TypeConstructor` above, the arguments are relevant
  -- here. E.g., for a type declared like so:
  -- `type Foo _ _;`
  -- the type synonym
  -- `type Bar x y = Foo x x;`
  -- is legal, where `y` is ignored.
  -- Note also that the `typeArgs` may not contain duplicates.
  typeArgs : List TyIdentifier
  type     : LMonoTy
  deriving Repr

instance : ToFormat TypeSynonym where
  format t :=
    let args := if t.typeArgs.isEmpty then f!"" else f!" {Std.Format.joinSep t.typeArgs " "}"
    f!"type {t.name}{args} := {t.type}"

def TypeSynonym.toLHSLMonoTy (t : TypeSynonym) : LMonoTy :=
  let args := t.typeArgs.map (fun elem => LMonoTy.ftvar elem)
  (.tcons t.name args)

def TypeSynonym.toLHSLTy (t : TypeSynonym) : LTy :=
  .forAll t.typeArgs t.toLHSLMonoTy

def TypeSynonym.toRHSLTy (t : TypeSynonym) : LTy :=
  .forAll t.typeArgs t.type

/-! # Strata Core Type Declarations -/

inductive TypeDecl where
  | con : TypeConstructor → TypeDecl
  | syn : TypeSynonym → TypeDecl
  | data : List (LDatatype Visibility) → TypeDecl
  deriving Repr

instance : ToFormat TypeDecl where
  format d :=
    match d with
    | .con tc => f!"{tc}"
    | .syn ts => f!"{ts}"
    | .data [] => f!"<empty mutual block>"
    | .data [td] => f!"{td}"
    | .data tds => f!"mutual {Std.Format.joinSep (tds.map format) Format.line} end"

/-- Get all names from a TypeDecl. -/
def TypeDecl.names (d : TypeDecl) : List Expression.Ident :=
  match d with
  | .con tc => [tc.name]
  | .syn ts => [ts.name]
  | .data tds => tds.map (·.name)

/-- Get the primary name of a TypeDecl (first name for mutual blocks). -/
def TypeDecl.name (d : TypeDecl) : Expression.Ident :=
  match d with
  | .con tc => tc.name
  | .syn ts => ts.name
  | .data [] => ""
  | .data (td :: _) => td.name

---------------------------------------------------------------------
