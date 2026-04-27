/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Util.ListUtils
import all Strata.DL.Util.ListUtils
public import Strata.Languages.Core.Program

public section

/-! # Well-Formedness of Strata Core Programs
 This file contains well-formedness definitions of Strata Core `Program`s Note that
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


namespace Core
namespace WF

open Imperative

/- Statement Wellformedness -/

structure WFcmdProp (p : Program) (c : Imperative.Cmd Expression) : Prop where

structure WFargProp (p : Program) (arg : Expression.Expr) : Prop where

structure WFcallProp (p : Program) (procName : String) (callArgs : List (CallArg Expression)) : Prop where
  defined : (Program.Procedure.find? p procName).isSome
  arglen : (Program.Procedure.find? p procName = some proc) →
          proc.header.inputs.length = (CallArg.getInputExprs callArgs).length
  outlen : (Program.Procedure.find? p procName = some proc) →
          proc.header.outputs.length = (CallArg.getLhs callArgs).length
  lhsWF : (CallArg.getLhs callArgs).Nodup
  wfargs : Forall (WFargProp p) (CallArg.getInputExprs callArgs)

@[expose] def WFCmdExtProp (p : Program) (c : CmdExt Expression) : Prop := match c with
  | .cmd c => WFcmdProp p c
  | .call procName callArgs _ => WFcallProp p procName callArgs

structure WFblockProp (Cmd : Type) (p : Program) (label : String) (b : Block) : Prop where

structure WFifProp    (Cmd : Type) (p : Program) (cond : ExprOrNondet Expression)  (thenb : Block) (elseb : Block) : Prop where

structure WFloopProp    (Cmd : Type) (p : Program) (guard : ExprOrNondet Expression) (measure : Option Expression.Expr) (invariant : List Expression.Expr) (b : Block) : Prop where

structure WFexitProp  (p : Program) (label : Option String) : Prop where

/-- Well-formedness for local function declarations.
    Checks that function parameter names are unique.

    This is kept separate from `FuncWF` (from `Strata.DL.Util.Func`) because:
    1. `FuncWF` requires function parameters (`getName`, `getVarNames`) that add complexity
    2. `FuncWF.concreteEval_argmatch` is not decidable, making it harder to use in proofs
    3. For statement-level WF, only `arg_nodup` is needed; the additional `FuncWF`
       properties (`body_freevars`, `concreteEval_argmatch`) are for factory functions

    Note: `WFfuncDeclProp` checks uniqueness of full `CoreIdent` (including visibility),
    while `FuncWF.arg_nodup` checks uniqueness of just the string names. -/
structure WFfuncDeclProp (p : Program) (decl : Imperative.PureFunc Expression) : Prop where
  arg_nodup : decl.inputs.keys.Nodup

@[simp, expose]
def WFStatementProp (p : Program) (stmt : Statement) : Prop := match stmt with
  | .cmd   cmd => WFCmdExtProp p cmd
  | .block (label : String) (b : Block) _ => WFblockProp (CmdExt Expression) p label b
  | .ite   (cond : ExprOrNondet Expression) (thenb : Block) (elseb : Block) _ =>
     WFifProp (CmdExt Expression) p cond thenb elseb
  | .loop  (guard : ExprOrNondet Expression) (measure : Option Expression.Expr) (invariant : List Expression.Expr) (body : Block) _ =>
     WFloopProp (CmdExt Expression) p guard measure invariant body
  | .exit (label : Option String) _ => WFexitProp p label
  | .funcDecl decl _ => WFfuncDeclProp p decl
  | .typeDecl _ _ => True  -- Type declarations are always well-formed

@[expose] abbrev WFStatementsProp (p : Program) := Forall (WFStatementProp p)

instance (p : Program) : ListP (WFStatementProp p) (WFStatementsProp p) where
  split := by intros as a wfs
              have H := ((List.Forall_cons (WFStatementProp p) a as).mp wfs)
              exact ⟨H.1, H.2⟩

/- Spec Wellformedness -/

structure WFPrePostProp (p : Program) (d : Procedure) (pp : CoreLabel × Procedure.Check)
  : Prop where

structure WFPreProp (p : Program) (d : Procedure) (pp : CoreLabel × Procedure.Check)
  : Prop extends WFPrePostProp p d pp where

structure WFPostProp (p : Program) (d : Procedure) (pp : CoreLabel × Procedure.Check)
  : Prop extends WFPrePostProp p d pp where
  oldOnlyInout : ∀ id ∈ Imperative.HasVarsPure.getVars (P := Expression) pp.2.expr,
    CoreIdent.isOldIdent id → id ∈ ListMap.keys (d.header.getInoutParams.map
      (fun (x, ty) => (CoreIdent.mkOld x.name, ty)))

@[simp]
abbrev WFPresProp (p : Program) (d : Procedure) := Forall (WFPreProp p d)

@[simp]
abbrev WFPostsProp (p : Program) (d : Procedure) := Forall (WFPostProp p d)

structure WFSpecProp (p : Program) (spec : Procedure.Spec) (d : Procedure): Prop where
  wfpre : WFPresProp p d spec.preconditions
  wfpost : WFPostsProp p d spec.postconditions

/- Procedure Wellformedness -/

structure WFTypeDeclarationProp (p : Program) (f : TypeDecl) : Prop where

structure WFAxiomDeclarationProp (p : Program) (f : Axiom) : Prop where

structure WFDistinctDeclarationProp (p : Program) (l : Expression.Ident) (es : List (Expression.Expr)) : Prop where

structure WFProcedureProp (p : Program) (d : Procedure) : Prop where
  wfstmts : WFStatementsProp p d.body
  wfloclnd : (HasVarsImp.definedVars (P:=Expression) d.body).Nodup
  inputsNodup : (ListMap.keys d.header.inputs).Nodup
  outputsNodup : (ListMap.keys d.header.outputs).Nodup
  ioNotOld : ∀ id ∈ ListMap.keys d.header.inputs ++ ListMap.keys d.header.outputs,
      ∀ x, id ≠ CoreIdent.mkOld x
  wfspec : WFSpecProp p d.spec d
  -- There is no exit statement that cannot be caught by any block in the procedure.
  bodyExitsCovered : Stmt.exitsCoveredByBlocks.Block.exitsCoveredByBlocks [] d.body
structure WFFunctionProp (p : Program) (f : Function) : Prop where

structure WFRecFuncBlockProp (p : Program) (fs : List Function) : Prop where
  nonempty : fs ≠ []
  namesDistinct : (fs.map (·.name)).Nodup
  noInline : ∀ f ∈ fs, ¬ f.attr.any (· == .inline)
  wfFuncs : ∀ f ∈ fs, WFFunctionProp p f

@[simp, expose, grind]
def WFDeclProp (p : Program) (decl : Decl) : Prop := match decl with
  | .type t _ => WFTypeDeclarationProp p t
  | .ax a _ => WFAxiomDeclarationProp p a
  | .distinct l es _ => WFDistinctDeclarationProp p l es
  | .proc d _ => WFProcedureProp p d
  | .func f _ => WFFunctionProp p f
  | .recFuncBlock fs _ => WFRecFuncBlockProp p fs

@[expose, simp] abbrev WFDeclsProp (p : Program) := Forall (WFDeclProp p)

instance (p : Program) : ListP (WFDeclProp p) (WFDeclsProp p) where
  split := by intros as a wfs
              have H := ((List.Forall_cons (WFDeclProp p) a as).mp wfs)
              exact ⟨H.1, H.2⟩

structure WFProgramProp (p : Program) where
  namesNodup : (p.getNames).Nodup
  wfdecls : WFDeclsProp p p.decls

structure WFProcedure (p : Program) extends (Wrapper Procedure) where
  prop: WFProcedureProp p self

structure WFProgram extends (Wrapper Program) where
  prop: WFProgramProp self

end WF

end Core

end -- public section
