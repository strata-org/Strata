/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module


public import Strata.DL.Lambda.TypeConstructor
public import Strata.DL.Lambda.LTyWF
public import Strata.Languages.Core.Expressions

---------------------------------------------------------------------

namespace Core
public section

open Std (ToFormat Format format)
open Lambda
open Strata (Message)

/-! # Strata Core Type Declarations -/

---------------------------------------------------------------------

structure TypeSynonym where
  name     : String
  typeArgs : List TyIdentifier
  type     : LMonoTy
  deriving Repr, DecidableEq

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

/-- `ts` with the body of the newest alias of `aliases`, if any. -/
def TypeSynonym.withStoredBody (ts : TypeSynonym) : List TypeAlias → TypeSynonym
  | al :: _ => { ts with type := al.type }
  | [] => ts

/-- Check a type synonym and register it as a type alias, returning the synonym with the
    alias-resolved body the alias stores. -/
def TypeSynonym.typeCheck (ts : TypeSynonym) (C : Expression.TyContext)
    (Env : Expression.TyEnv) : Except Format (TypeSynonym × Expression.TyEnv) := do
  let Env' ← Lambda.TEnv.addTypeAlias
    { typeArgs := ts.typeArgs, name := ts.name, type := ts.type } C Env
  return (ts.withStoredBody Env'.context.aliases, Env')

/-- Where an opaque type declaration was written. -/
inductive TypeConstructor.Site where
  /-- A declaration among a program's top-level declarations. -/
  | program
  /-- A declaration inside a procedure or function body, carrying the program-level
      declaration names it may not reuse. -/
  | bodyLocal (programNames : List Expression.Ident)

/-- The program-level declaration names a declaration at this site may not
    reuse. -/
def TypeConstructor.Site.programNames :
    TypeConstructor.Site → List Expression.Ident
  | .program => []
  | .bodyLocal ns => ns

/-- Whether the site is inside a procedure or function body. -/
def TypeConstructor.Site.isBodyLocal : TypeConstructor.Site → Bool
  | .program => false
  | .bodyLocal _ => true

/-- The word a reported message uses for a declaration at this site. -/
def TypeConstructor.Site.what : TypeConstructor.Site → Format
  | .program => f!"Type"
  | .bodyLocal _ => f!"Local type"

/-- Check an opaque type declaration and register it as a known type. Its name is not a
    forbidden program-level name, a known type at any arity, or, inside a body, a type
    synonym. -/
def TypeConstructor.typeCheck (tc : TypeConstructor) (site : TypeConstructor.Site)
    (C : Expression.TyContext) (Env : Expression.TyEnv) : Except Message Expression.TyContext := do
  if site.programNames.any (fun n => n.name == tc.name) then
    throw <| Message.fromFormat f!"Type '{tc.name}' is already declared at the program level"
  if site.isBodyLocal && Env.context.aliases.any (fun al => al.name == tc.name) then
    throw <| Message.fromFormat f!"{site.what} '{tc.name}' is already a type synonym"
  C.addKnownTypeWithError { name := tc.name, metadata := tc.numargs }
    (Message.fromFormat f!"Type '{tc.name}' is already declared")

/-- Check a mutual datatype block and register its alias-resolved form. -/
def MutualDatatype.typeCheck (block : Lambda.MutualDatatype Unit)
    (C : Expression.TyContext) (Env : Expression.TyEnv) :
    Except Message
      (Lambda.MutualDatatype Unit × Expression.TyContext × Expression.TyEnv) := do
  let (resolved, Env') ← Lambda.MutualDatatype.resolveAliases block Env
    |>.mapError Message.fromFormat
  let C' ← C.addMutualBlock resolved
  .ok (resolved, C', Env')

/-! # Strata Core Type Declarations -/

inductive TypeDecl where
  | con : TypeConstructor → TypeDecl
  | syn : TypeSynonym → TypeDecl
  | data : List (LDatatype Unit) → TypeDecl
  deriving Repr, DecidableEq

instance : ToFormat TypeDecl where
  format d :=
    match d with
    | .con tc => f!"{tc}"
    | .syn ts => f!"{ts}"
    | .data [] => f!"<empty mutual block>"
    | .data [td] => f!"{td}"
    | .data tds => f!"mutual {Std.Format.joinSep (tds.map format) Format.line} end"

/-- Erase the constructor argument types of a datatype; names and type parameters are kept. -/
def LDatatype.eraseAnnots (d : LDatatype Unit) : LDatatype Unit :=
  let constrs := d.constrs.map fun c =>
    { c with args := c.args.map fun (n, _) => (n, LMonoTy.erased) }
  have hne : constrs.length != 0 := by
    simpa only [constrs, List.length_map] using d.constrs_ne
  { d with constrs := constrs, constrs_ne := hne }

/-- Erase the types a declaration mentions: the body of a synonym and the constructor
argument types of a datatype. Type parameters are kept. -/
def TypeDecl.eraseAnnots : TypeDecl → TypeDecl
  | .con tc => .con tc
  | .syn ts => .syn { ts with type := LMonoTy.erased }
  | .data ds => .data (ds.map LDatatype.eraseAnnots)

/-- Get all names from a TypeDecl. -/
@[expose] def TypeDecl.names (d : TypeDecl) : List Expression.Ident :=
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

end
---------------------------------------------------------------------
