/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core
import Strata.Languages.Core.ProgramProps
import StrataTest.Languages.Core.Tests.Logic.HoareUtils
import StrataDDM.Integration.Lean.HashCommands

/-! # The functions of a datatype in a procedure's visible factory

`Program.factoryBeforeProcedure` is the factory a procedure's contract triple is stated
over (`Procedure.contractTriple`) and its body runs with. It holds the constructors,
testers and destructors of the datatypes declared before the procedure, so a body or a
contract that mentions them evaluates. A datatype declared after the procedure adds
nothing to it.

## Key results

- `after_factory_has_datatype_functions`: the functions of `IntList` are in the factory
  of a procedure declared after it.
- `before_factory_eq_core`: the factory of a procedure declared before `IntList` is
  Core's own.
- `headOfCons_meets_contract`: `HeadOfCons` sets `r` to `IntList..hd(Cons(1, Nil()))`
  and ensures `r == 1`. The contract holds in every model of its factory, because a model
  agrees with the concrete evaluator of each function in the factory, here the
  destructor's (`opInterp_of_concreteEval`). A model of a factory without the destructor
  may give it any value.
-/

open StrataDDM (Program)

namespace Strata.HoareDatatypesTest

open Strata.HoareUtils

private def listPgm : Program :=
#strata
program Core;

procedure Before(out r : int)
spec {
  ensures r == 0;
}
{
  r := 0;
};

datatype IntList { Nil(), Cons(hd: int, tl: IntList) };

procedure After(xs : IntList, out r : bool)
spec {
  ensures r == IntList..isNil(xs);
}
{
  r := IntList..isNil(xs);
};

procedure HeadOfCons(out r : int)
spec {
  ensures r == 1;
}
{
  r := IntList..hd(Cons(1, Nil()));
};
#end

/-- The type-checked program, whose operators carry their instantiated types. -/
private def listAST : Core.Program := typeCheckedAST listPgm

/-- The constructors, testers and destructors of `IntList`. -/
private def intListFunctions : List String :=
  ["Nil", "Cons", "IntList..isNil", "IntList..isCons", "IntList..hd", "IntList..tl"]

/-- None of them is one of Core's built-in functions. -/
private theorem intListFunctions_new :
    (intListFunctions.all fun n => (Core.Factory[n]?).isNone) = true := by
  native_decide

/-- **The functions of a datatype are visible to a procedure declared after it.** -/
theorem after_factory_has_datatype_functions :
    (intListFunctions.all fun n =>
      ((listAST.factoryBeforeProcedure "After")[n]?).isSome) = true := by
  native_decide

/-- **A datatype declared after a procedure adds nothing to its factory.** -/
theorem before_factory_eq_core :
    listAST.factoryBeforeProcedure "Before" = Core.Factory :=
  Core.Program.factoryBeforeProcedure_eq_core_of_noFunctions (by native_decide)

/-! ## A contract that rests on the datatype's functions

`HeadOfCons` reads the head of `Cons(1, Nil())`. Its contract holds because the destructor
`IntList..hd` is in the procedure's factory, with the concrete evaluator that returns a
constructor's field: every model agrees with it. -/

section HeadOfCons

open Lambda

private abbrev listTy : LMonoTy := .tcons "IntList" []

/-- `Cons(1, Nil())`, with the types the type checker gives its operators. -/
private abbrev consE : Core.Expression.Expr :=
  .app Core.valueLoc
    (.app Core.valueLoc
      (.op Core.valueLoc ⟨"Cons", ()⟩
        (some (.tcons "arrow" [intMono, .tcons "arrow" [listTy, listTy]])))
      (.intConst Core.valueLoc 1))
    (.op Core.valueLoc ⟨"Nil", ()⟩ (some listTy))

/-- The destructor `IntList..hd` at `IntList → int`. -/
private abbrev hdOp : Core.Expression.Expr :=
  .op Core.valueLoc ⟨"IntList..hd", ()⟩ (some (.tcons "arrow" [listTy, intMono]))

/-- `IntList..hd(Cons(1, Nil()))`. -/
private abbrev hdE : Core.Expression.Expr := .app Core.valueLoc hdOp consE

private abbrev hdFactory : Lambda.Factory Core.CoreLParams :=
  listAST.factoryBeforeProcedure "HeadOfCons"

private def hdFn : LFunc Core.CoreLParams := (hdFactory["IntList..hd"]?).get!

private theorem hdFn_lookup : hdFactory["IntList..hd"]? = some hdFn := by
  have hs : (hdFactory["IntList..hd"]?).isSome = true := by native_decide
  unfold hdFn
  cases h : hdFactory["IntList..hd"]? with
  | none => rw [h] at hs; cases hs
  | some _ => rfl

private theorem hdFn_name : hdFn.name.name = "IntList..hd" := by native_decide

private theorem hdFn_inputs :
    (hdFn.inputs.map Prod.snd).map (LMonoTy.subst Subst.empty) = [listTy] := by
  native_decide

private theorem hdFn_output : hdFn.output.subst Subst.empty = intMono := by native_decide

/-- The destructor's concrete evaluator returns the first field of `Cons(1, Nil())`. -/
private theorem hdFn_eval :
    hdFn.concreteEval.bind (fun ce => ce Core.coreLoc (some (hdFn.instTy Subst.empty)) [consE]) =
      some (.intConst Core.valueLoc 1) := by
  native_decide

private theorem consE_ty : LExpr.HasTypeA (T := Core.CoreLParams) [] consE listTy :=
  .app (.app .op (.const rfl)) .op

private theorem hdE_ty : LExpr.HasTypeA (T := Core.CoreLParams) [] hdE intMono :=
  .app .op consE_ty

/-- In every model of the factory, `IntList..hd(Cons(1, Nil()))` denotes `1`. -/
private theorem hdE_denote (model : Lambda.Interp hdFactory)
    (fv : FreeVarVal Core.CoreLParams model.tcInterp) (vt : TyVarVal)
    (h : LExpr.HasTypeA (T := Core.CoreLParams) [] hdE intMono) :
    LExpr.denote model.tcInterp model.opInterp fv vt .nil hdE intMono h = (1 : Int) := by
  have hop : LExpr.HasTypeA (T := Core.CoreLParams) [] hdOp (.arrow listTy intMono) := .op
  rw [denote_app .nil hop consE_ty h, denote_op]
  have key := Core.opInterp_of_concreteEval model hdFn_lookup hdFn_name hdFn_eval vt fv
  rw [hdFn_inputs, hdFn_output] at key
  exact (key (.cons consE_ty .nil) (.const rfl)).symm.trans (denote_intConst _ _ _ _ _ _)

/-- On every runtime factory over the procedure's factory, `IntList..hd(Cons(1, Nil()))`
    evaluates to `1`. -/
private theorem hdE_eval (F : Core.Expression.Factory) (hF : F.factory = hdFactory)
    (σ : Core.CoreStore) :
    Core.Expression.eval F σ hdE = some (SemValue.ofInt F.model.tcInterp 1) := by
  obtain ⟨Fl, model, tv⟩ := F
  obtain rfl : Fl = hdFactory := hF
  have hd : ValStore.Defines (T := Core.CoreLParams) σ model.tcInterp hdE :=
    fun _ hx => by cases hx
  refine (LExpr.denoteEval_of_hasTypeA (M := ⟨hdFactory, model, tv⟩) hd hdE_ty rfl).trans ?_
  refine congrArg some ?_
  letI := model.allInhabited
  show (⟨model.tcInterp, intMono.substTyVars tv,
      LExpr.denote model.tcInterp model.opInterp (ValStore.fvarVal model.tcInterp σ) tv .nil
        hdE intMono hdE_ty⟩ : SemValue) = ⟨model.tcInterp, .int, (1 : Int)⟩
  rw [hdE_denote]
  rfl

private abbrev rId : Core.Expression.Ident := ⟨"r", ()⟩

private def hdMd : Imperative.MetaData Core.Expression :=
  match bodyOf listAST "HeadOfCons" with
  | [.cmd (.cmd (.set _ _ md))] => md
  | _ => #[]

/-- `HeadOfCons` consists of the single assignment `r := IntList..hd(Cons(1, Nil()))`. -/
private theorem hd_body_shape :
    (procOf listAST "HeadOfCons").body = .structured [Core.Statement.set rId hdE hdMd] false := by
  native_decide

/-- Its postcondition is `r == 1`. -/
private theorem hd_post_shape :
    ∀ lc ∈ (procOf listAST "HeadOfCons").spec.postconditions.toList, lc.2.expr = eqInt rId 1 := by
  native_decide

/-- **`HeadOfCons` meets its contract**: the head of `Cons(1, Nil())` is `1`. -/
theorem headOfCons_meets_contract :
    Core.Logic.Hoare.Procedure.contractTriple listAST testParams "HeadOfCons" := by
  let command : Core.Command :=
    Imperative.CmdExt.cmd (Imperative.Cmd.set rId (.det hdE) hdMd)
  refine Core.Logic.Hoare.Procedure.contractTriple_singleton_cmd (hmono := by native_decide)
    (opq := false) listAST testParams "HeadOfCons" (procOf listAST "HeadOfCons") (by native_decide) command ?_
    (by native_decide) ?_ ?_
  · simpa [command] using hd_body_shape
  · intro ρ₀ σ' emitted hpre _hwf hstep
    obtain ⟨-, hfac, -⟩ := hpre
    dsimp [command] at hstep
    cases hstep with
    | cmd_sem hcmd =>
      cases hcmd with
      | eval_set heval hupdate _ _ =>
        have hv := Option.some.inj (heval.symm.trans (hdE_eval ρ₀.factory hfac ρ₀.store))
        cases hupdate with
        | update _ hnew _ =>
          rw [hv] at hnew
          refine ⟨True.intro, fun _ label check hmem _ _ => .inl ⟨hfac, ?_⟩⟩
          change Core.Expression.eval ρ₀.factory σ' check.expr =
            some (Imperative.HasBool.ttVal ρ₀.factory)
          rw [hd_post_shape _ hmem]
          exact Core.eval_eq_true _ (Core.eval_fvar_int _ hnew) (Core.eval_intConst _ _ 1)
  · exact Imperative.Logic.Hoare.postWF_of_definedVars_nil _ (by
      simp [command, Imperative.Block.definedVars, Imperative.Stmt.definedVars,
        Imperative.HasVarsImp.definedVars, Imperative.CmdExt.definedVars,
        Imperative.Cmd.definedVars])

end HeadOfCons

end Strata.HoareDatatypesTest
