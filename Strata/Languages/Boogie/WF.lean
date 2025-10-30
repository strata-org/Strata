/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Util.ListUtils
import Strata.Languages.Boogie.Program
import Strata.Languages.Boogie.OldExpressions

/-! # Well-Formedness of Boogie Programs
 This file contains well-formedness definitions of Boogie `Program`s Note that
 the substructures such as `WFStatementProp` also carry a `Program` instance, and
 this allows us to state more expressive well-formedness conditions than a
 typical inductive relation.

 Although arguably these well-formedness properties can also be formulated using
 an inductive relation, this design choice provides more structure in
 formulating the properties in that it quite strictly mirrors the actual program
 structures themselves and can be extended in a straight-forward manner to suit
 specific needs.

 For example, one can easily add a new Prop to `WFProgramProp` stating that the
 set of all variable names, procedure names, and function names do not contain
 duplicates.  (Currently we only assert that the individual sets themselves do
 not contain duplicates)

 Theorems producing the well-formedness 'proofs' are located in files *WF.lean.
 These theorems typically state that if the type checker returns no error, then
 the structure is well-formed.

 A main theorem is `Program.typeCheckWF`, which states that if a program
 successfully type checks, then it is also well-formed. These properties are
 can serve as a baseline for proving semantic preservations.
 -/


namespace Boogie
namespace WF

open Imperative

/- Statement Wellformedness -/

structure WFcmdProp (p : Program) (c : Imperative.Cmd Expression) : Prop where

structure WFargProp (p : Program) (arg : Expression.Expr) : Prop where
  glarg : Forall (BoogieIdent.isGlobOrLocl ·) (HasVarsPure.getVars (P:=Expression) arg)

structure WFcallProp (p : Program) (lhs : List Expression.Ident) (procName : String) (args : List Expression.Expr) : Prop where
  defined : (Program.Procedure.find? p (.unres procName)).isSome
  arglen : (Program.Procedure.find? p (.unres procName) = some proc) →
          proc.header.inputs.length = args.length
  outlen : (Program.Procedure.find? p (.unres procName) = some proc) →
          proc.header.outputs.length = lhs.length
  lhsDisj : (Program.Procedure.find? p (.unres procName) = some proc) →
          lhs.Disjoint (proc.spec.modifies ++ ListMap.keys proc.header.inputs ++ ListMap.keys proc.header.outputs)
  lhsWF : lhs.Nodup ∧ Forall (BoogieIdent.isLocl ·) lhs
  wfargs : Forall (WFargProp p) args

def WFCmdExtProp (p : Program) (c : CmdExt Expression) : Prop := match c with
  | .cmd c => WFcmdProp p c
  | .call (lhs : List Expression.Ident) (procName : String) (args : List Expression.Expr) _ => WFcallProp p lhs procName args

structure WFblockProp (Cmd : Type) (p : Program) (label : String) (b : Block Expression Cmd) : Prop where

structure WFifProp    (Cmd : Type) (p : Program) (cond : Expression.Expr)  (thenb : Block Expression Cmd) (elseb : Block Expression Cmd) : Prop where

structure WFloopProp    (Cmd : Type) (p : Program) (guard : Expression.Expr) (measure : Option Expression.Expr) (invariant : Option Expression.Expr) (b : Block Expression Cmd) : Prop where

structure WFgotoProp  (p : Program) (label : String) : Prop where

@[simp]
def WFStatementProp (p : Program) (stmt : Statement) : Prop := match stmt with
  | .cmd   cmd => WFCmdExtProp p cmd
  | .block (label : String) (b : Block Expression (CmdExt Expression)) _ => WFblockProp (CmdExt Expression) p label b
  | .ite   (cond : Expression.Expr) (thenb : Block Expression (CmdExt Expression)) (elseb : Block Expression (CmdExt Expression)) _ =>
     WFifProp (CmdExt Expression) p cond thenb elseb
  | .loop  (guard : Expression.Expr) (measure : Option Expression.Expr) (invariant : Option Expression.Expr) (body : Block Expression (CmdExt Expression)) _ =>
     WFloopProp (CmdExt Expression) p guard measure invariant body
  | .goto (label : String) _ => WFgotoProp p label

abbrev WFStatementsProp (p : Program) := Forall (WFStatementProp p)

instance (p : Program) : ListP (WFStatementProp p) (WFStatementsProp p) where
  split := by intros as a wfs
              have H := ((List.Forall_cons (WFStatementProp p) a as).mp wfs)
              exact ⟨H.1, H.2⟩

/- Spec Wellformedness -/

structure WFPrePostProp (p : Program) (d : Procedure) (pp : BoogieLabel × Procedure.Check)
  : Prop where
  glvars : Forall (BoogieIdent.isGlobOrLocl ·) (HasVarsPure.getVars (P:=Expression) pp.2.expr)
  lvars : Forall (fun x =>
            (BoogieIdent.isLocl x) →
            (x ∈ (ListMap.keys d.header.inputs) ++ (ListMap.keys d.header.outputs)))
          (HasVarsPure.getVars (P:=Expression) pp.2.expr)

structure WFPreProp (p : Program) (d : Procedure) (pp : BoogieLabel × Procedure.Check)
  : Prop extends WFPrePostProp p d pp
  where
  nold : ¬ OldExpressions.containsOldExpr pp.2.expr

structure WFPostProp (p : Program) (d : Procedure) (pp : BoogieLabel × Procedure.Check)
  : Prop extends WFPrePostProp p d pp
  where
  oldexprs : OldExpressions.ValidExpression pp.2.expr

structure WFModProp (p : Program) (d : Procedure) (mod : Expression.Ident) : Prop where
  defined : (Program.find? p .var mod).isSome

@[simp]
abbrev WFPresProp (p : Program) (d : Procedure) := Forall (WFPreProp p d)

@[simp]
abbrev WFPostsProp (p : Program) (d : Procedure) := Forall (WFPostProp p d)

@[simp]
abbrev WFModsProp (p : Program) (d : Procedure) := Forall (WFModProp p d)

structure WFSpecProp (p : Program) (spec : Procedure.Spec) (d : Procedure): Prop where
  wfpre : WFPresProp p d spec.preconditions
  wfpost : WFPostsProp p d spec.postconditions
  wfmod : WFModsProp p d spec.modifies

/- Procedure Wellformedness -/

structure WFVarProp (p : Program) (name : Expression.Ident) (ty : Expression.Ty) (e : Expression.Expr) : Prop where
  glob : BoogieIdent.isGlob name

structure WFTypeDeclarationProp (p : Program) (f : TypeDecl) : Prop where

structure WFAxiomDeclarationProp (p : Program) (f : Axiom) : Prop where

structure WFDistinctDeclarationProp (p : Program) (l : Expression.Ident) (es : List (Expression.Expr)) : Prop where

structure WFProcedureProp (p : Program) (d : Procedure) : Prop where
  wfstmts : WFStatementsProp p d.body
  wfloclnd : (HasVarsImp.definedVars (P:=Expression) d.body).Nodup
  ioDisjoint : (ListMap.keys d.header.inputs).Disjoint (ListMap.keys d.header.outputs)
  inputsNodup : (ListMap.keys d.header.inputs).Nodup
  outputsNodup : (ListMap.keys d.header.outputs).Nodup
  modNodup : d.spec.modifies.Nodup
  inputsLocl : Forall (BoogieIdent.isLocl ·) (ListMap.keys d.header.inputs)
  outputsLocl : Forall (BoogieIdent.isLocl ·) (ListMap.keys d.header.outputs)
  wfspec : WFSpecProp p d.spec d
structure WFFunctionProp (p : Program) (f : Function) : Prop where

@[simp]
def WFDeclProp (p : Program) (decl : Decl) : Prop := match decl with
  | .var name ty e _ => WFVarProp p name ty e
  | .type t _ => WFTypeDeclarationProp p t
  | .ax a _ => WFAxiomDeclarationProp p a
  | .distinct l es _ => WFDistinctDeclarationProp p l es
  | .proc d _ => WFProcedureProp p d
  | .func f _ => WFFunctionProp p f

abbrev WFDeclsProp (p : Program) := Forall (WFDeclProp p)

instance (p : Program) : ListP (WFDeclProp p) (WFDeclsProp p) where
  split := by intros as a wfs
              have H := ((List.Forall_cons (WFDeclProp p) a as).mp wfs)
              exact ⟨H.1, H.2⟩

structure WFProgramProp (p : Program) where
  varNodup : (p.getNames .var).Nodup
  procNodup : (p.getNames .proc).Nodup
  funcNodup : (p.getNames .func).Nodup
  wfdecls : WFDeclsProp p p.decls

structure WFProcedure (p : Program) extends (Wrapper Procedure) where
  prop: WFProcedureProp p self

structure WFProgram extends (Wrapper Program) where
  prop: WFProgramProp self

end WF
end Boogie
