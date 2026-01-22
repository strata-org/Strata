/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/



import Strata.DL.Imperative.HasVars
import Strata.Languages.Core.Statement

---------------------------------------------------------------------

namespace Core

open Std (ToFormat Format format)
open Lambda

-- Type class instances to enable deriving for structures containing Expression.Expr
instance : DecidableEq ExpressionMetadata :=
  show DecidableEq Unit from inferInstance

instance : Repr ExpressionMetadata :=
  show Repr Unit from inferInstance

instance : DecidableEq (⟨⟨ExpressionMetadata, CoreIdent⟩, LMonoTy⟩ : LExprParamsT).base.Metadata :=
  show DecidableEq ExpressionMetadata from inferInstance

instance : DecidableEq (⟨⟨ExpressionMetadata, CoreIdent⟩, LMonoTy⟩ : LExprParamsT).base.IDMeta :=
  show DecidableEq CoreIdent from inferInstance

instance : DecidableEq (⟨⟨ExpressionMetadata, CoreIdent⟩, LMonoTy⟩ : LExprParamsT).TypeType :=
  show DecidableEq LMonoTy from inferInstance

instance : Repr (⟨⟨ExpressionMetadata, CoreIdent⟩, LMonoTy⟩ : LExprParamsT).base.Metadata :=
  show Repr ExpressionMetadata from inferInstance

instance : Repr (⟨⟨ExpressionMetadata, CoreIdent⟩, LMonoTy⟩ : LExprParamsT).base.IDMeta :=
  show Repr CoreIdent from inferInstance

instance : Repr (⟨⟨ExpressionMetadata, CoreIdent⟩, LMonoTy⟩ : LExprParamsT).TypeType :=
  show Repr LMonoTy from inferInstance

instance : Repr Expression.Expr :=
  show Repr Expression.Expr from inferInstance

/-! # Strata Core Procedures -/

structure Procedure.Header where
  name     : CoreIdent
  typeArgs : List TyIdentifier
  inputs   : @LMonoTySignature Visibility
  outputs  : @LMonoTySignature Visibility
  deriving Repr, DecidableEq, Inhabited

instance : ToFormat Procedure.Header where
  format p :=
    let typeArgs := if p.typeArgs.isEmpty then f!"" else f!"∀{Format.joinSep p.typeArgs " "}."
    f!"procedure {p.name} : {typeArgs} ({Signature.format p.inputs}) → \
      ({Signature.format p.outputs})"

inductive Procedure.CheckAttr where
  /-
  From Section 8.1, Caller and callee traces: Motivation, This is Boogie 2:
  "A free precondition is assumed by the implementation, but not checked at call sites, and
   a free postcondition is assumed upon return from calls, but is not checked on exit from
   implementations."
  -/
  | Free
  | Default
  deriving Repr, DecidableEq

instance : Std.ToFormat Procedure.CheckAttr where
  format a :=
    match a with
    | .Default => f!""
    | _ => f!" (Attribute: {repr a})"

structure Procedure.Check where
  expr : Expression.Expr
  attr : CheckAttr := .Default
  md : Imperative.MetaData Expression := #[]
  deriving Repr, DecidableEq

instance : Inhabited Procedure.Check where
  default := { expr := Inhabited.default }

instance : ToFormat Procedure.Check where
  format c := f!"{c.expr}{c.attr}"

def Procedure.Check.eraseTypes (c : Procedure.Check) : Procedure.Check :=
  { c with expr := c.expr.eraseTypes }

structure Procedure.Spec where
  modifies       : List Expression.Ident
  preconditions  : ListMap CoreLabel Procedure.Check
  postconditions : ListMap CoreLabel Procedure.Check
  deriving Inhabited, Repr

instance : ToFormat Procedure.Spec where
  format p :=
    f!"modifies: {format p.modifies}\n\
       preconditions: {format p.preconditions}\n\
       postconditions: {format p.postconditions}"

def Procedure.Spec.preconditionNames (s : Procedure.Spec) : List CoreLabel :=
  s.preconditions.keys

def Procedure.Spec.postconditionNames (s : Procedure.Spec) : List CoreLabel :=
  s.postconditions.keys

def Procedure.Spec.eraseTypes (s : Procedure.Spec) : Procedure.Spec :=
  { s with
    preconditions := s.preconditions.map (fun (l, c) => (l, c.eraseTypes)),
    postconditions := s.postconditions.map (fun (l, c) => (l, c.eraseTypes))
  }

def Procedure.Spec.getCheckExprs (conds : ListMap CoreLabel Procedure.Check) :
  List Expression.Expr :=
  let checks := conds.values
  checks.map (fun c => c.expr)

def Procedure.Spec.updateCheckExprs
  (es : List Expression.Expr) (conds : ListMap CoreLabel Procedure.Check) :
  ListMap CoreLabel Procedure.Check :=
  let checks := go es conds.values
  conds.keys.zip checks
  where go (es : List Expression.Expr) (checks : List Procedure.Check) :=
  match es, checks with
  | [], [] | [], _ | _, [] => checks
  | e :: erest, c :: crest =>
    { c with expr := e } :: go erest crest

structure Procedure where
  header : Procedure.Header
  spec   : Procedure.Spec
  body   : List Statement
  deriving Inhabited

instance : ToFormat Procedure where
  format p :=
    f!"({p.header})\n\
       {p.spec}\n\
       body: {p.body}\n"

---------------------------------------------------------------------

open Imperative

def Procedure.definedVars (_ : Procedure) : List Expression.Ident := []
def Procedure.modifiedVars (p : Procedure) : List Expression.Ident :=
  p.spec.modifies

def Procedure.getVars (p : Procedure) : List Expression.Ident :=
  (p.spec.postconditions.values.map Procedure.Check.expr).flatMap HasVarsPure.getVars ++
  (p.spec.preconditions.values.map Procedure.Check.expr).flatMap HasVarsPure.getVars ++
  p.body.flatMap HasVarsPure.getVars |> List.filter (not $ Membership.mem p.header.inputs.keys ·)

instance : HasVarsPure Expression Procedure where
  getVars := Procedure.getVars

instance : HasVarsImp Expression Procedure where
  definedVars := Procedure.definedVars
  modifiedVars := Procedure.modifiedVars

def Procedure.eraseTypes (p : Procedure) : Procedure :=
  { p with body := Statements.eraseTypes p.body, spec := p.spec }

/-- Transitive variable lookup for procedures.
    This is a version that looks into the body,
    but does not transitively search all variables occuring in the body.
    Transitively searching procedure bodies being called is possible,
    but the termination argument needs to be provided.
    One possible implementation is to store _a list of procedures_ in each procedure structure,
    and use the decreasing list size as a termination metric,
    as one traverses through recursively called procedure bodies.
-/
def Procedure.modifiedVarsTrans
  (_ : String → Option Procedure)
  (p: Procedure) : List Expression.Ident :=
  HasVarsImp.modifiedVars p ++
  HasVarsImp.modifiedVars p.body

/-- As `Procedure.modifiedVarsTrans`,
    this function is also non-transitive in terms of nested procedure calls.
    But it should be possible to implement one that is transtiive.
-/
def Procedure.getVarsTrans
  (_ : String → Option Procedure)
  (p: Procedure) : List Expression.Ident :=
  HasVarsPure.getVars p ++
  HasVarsPure.getVars p.body

instance : HasVarsProcTrans Expression Procedure where
  modifiedVarsTrans := Procedure.modifiedVarsTrans
  getVarsTrans := Procedure.getVarsTrans
  definedVarsTrans := λ _ _ ↦ [] -- procedures cannot define global variables
  touchedVarsTrans := Procedure.modifiedVarsTrans
  allVarsTrans :=
    λ π p ↦ Procedure.getVarsTrans π p ++ Procedure.modifiedVarsTrans π p

-- NOTE : simply discarding the procedure lookup function for now
instance : HasVarsTrans Expression Statement Procedure where
  modifiedVarsTrans := Statement.modifiedVarsTrans
  getVarsTrans := Statement.getVarsTrans
  definedVarsTrans := Statement.definedVarsTrans
  touchedVarsTrans := Statement.touchedVarsTrans
  allVarsTrans := Statement.allVarsTrans

instance : HasVarsTrans Expression (List Statement) Procedure where
  modifiedVarsTrans := Statements.modifiedVarsTrans
  getVarsTrans := Statements.getVarsTrans
  definedVarsTrans := Statements.definedVarsTrans
  touchedVarsTrans := Statements.touchedVarsTrans
  allVarsTrans := Statements.allVarsTrans


end Core
