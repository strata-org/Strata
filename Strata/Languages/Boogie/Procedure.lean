/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/



import Strata.DL.Imperative.HasVars
import Strata.Languages.Boogie.Statement

---------------------------------------------------------------------

namespace Boogie

open Std (ToFormat Format format)
open Lambda

/-! # Boogie Procedures -/

structure Procedure.Header where
  name     : BoogieIdent
  typeArgs : List TyIdentifier
  inputs   : @LMonoTySignature BoogieIdent
  outputs  : @LMonoTySignature BoogieIdent
  deriving Repr, DecidableEq

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
  deriving Repr, DecidableEq

instance : ToFormat Procedure.Check where
  format c := f!"{c.expr}{c.attr}"

structure Procedure.Spec where
  modifies       : List Expression.Ident
  preconditions  : Map BoogieLabel Procedure.Check
  postconditions : Map BoogieLabel Procedure.Check
  deriving Repr, DecidableEq

instance : ToFormat Procedure.Spec where
  format p :=
    f!"modifies: {format p.modifies}\n\
       preconditions: {format p.preconditions}\n\
       postconditions: {format p.postconditions}"

def Procedure.Spec.getCheckExprs (conds : Map BoogieLabel Procedure.Check) :
  List Expression.Expr :=
  let checks := conds.values
  checks.map (fun c => c.expr)

def Procedure.Spec.updateCheckExprs
  (es : List Expression.Expr) (conds : Map BoogieLabel Procedure.Check) :
  Map BoogieLabel Procedure.Check :=
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


end Boogie
