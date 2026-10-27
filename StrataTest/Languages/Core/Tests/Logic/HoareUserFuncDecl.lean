/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core
import Strata.Languages.Core.IntEvalProps
import Strata.Languages.Core.Logic.ContractToHoareTripleProps
import StrataTest.Languages.Core.Tests.Logic.HoareTestSupport
import StrataDDM.Integration.Lean.HashCommands

/-! # Hoare contracts with user-defined function declarations

A procedure's contract is interpreted in the factory formed from the functions
declared before that procedure. The example below gives `f` an arithmetic body,
uses it in the procedure body, and checks that a later function is not visible.

## Key results

- `compute_meets_contract` — `Compute` satisfies its arithmetic contract in the
  factory containing the preceding inline definition of `f`.
- `checkProduct_meets_contract` — a bodyless procedure satisfies an analogous
  contract using the non-inline `fSpec` only in its specification.
- `bodyExpr_eval` — an inline call to `f` evaluates to `(x + y) * (x - y)`.
-/

open StrataDDM (Program)

namespace Strata

private def cstToAST (p : Program) : Core.Program :=
  (TransM.run Inhabited.default (translateProgram p)).fst

private def userFuncPgm : Program :=
#strata
program Core;

inline function f(x : int, y : int) : int {
  int.mul(int.add(x, y), int.sub(x, y))
}

procedure Compute(x : int, y : int, out z : int)
spec {
  requires int.gt(x, y);
  requires int.gt(int.add(x, y), 0);
  ensures int.gt(z, 0);
}
{
  z := f(x, y);
};

function Later() : bool {
  true
}
#end

private def userFuncAST : Core.Program := cstToAST userFuncPgm
private abbrev computeProc : Core.Procedure :=
  (userFuncAST.findProcByString? "Compute").get!
private abbrev fDef : Core.Function :=
  (Core.Program.Function.find? userFuncAST ⟨"f", ()⟩).get!
private abbrev visibleFactory : Core.Expression.Factory :=
  userFuncAST.factoryBeforeProcedure "Compute"

private abbrev xId : Core.Expression.Ident := ⟨"x", ()⟩
private abbrev yId : Core.Expression.Ident := ⟨"y", ()⟩
private abbrev zId : Core.Expression.Ident := ⟨"z", ()⟩
private abbrev intTy : Option Lambda.LMonoTy := some .int

private def fBody : Core.Expression.Expr :=
  Lambda.LExpr.mkApp () Core.intMulOp [
    Lambda.LExpr.mkApp () Core.intAddOp [.fvar () xId intTy, .fvar () yId intTy],
    Lambda.LExpr.mkApp () Core.intSubOp [.fvar () xId intTy, .fvar () yId intTy]]

/-- The translated declaration of `f` has two integer parameters, the
    arithmetic body, and the inline attribute. -/
private theorem fDef_shape : fDef = {
    name := ⟨"f", ()⟩
    inputs := [(xId, .int), (yId, .int)]
    output := .int
    body := some fBody
    attr := #[.inline] } := by
  native_decide

private def bodyExpr : Core.Expression.Expr :=
  match computeProc.body with
  | .structured [Imperative.Stmt.cmd
      (Imperative.CmdExt.cmd (Imperative.Cmd.set _ (.det e) _))] => e
  | _ => Imperative.HasBool.ff

private def bodyMd : Imperative.MetaData Core.Expression :=
  match computeProc.body with
  | .structured [Imperative.Stmt.cmd
      (Imperative.CmdExt.cmd (Imperative.Cmd.set _ _ md))] => md
  | _ => #[]

/-- The expression assigned by `Compute` is `f(x, y)`. -/
private theorem bodyExpr_shape :
    bodyExpr = Lambda.LExpr.mkApp () fDef.opExpr
      [.fvar () xId intTy, .fvar () yId intTy] := by
  native_decide

/-- `Compute` consists of the single assignment `z := bodyExpr`. -/
private theorem compute_body_shape :
    computeProc.body = .structured [Core.Statement.set zId bodyExpr bodyMd] := by
  native_decide

private abbrev fDecl : Core.Decl := userFuncAST.decls.head!
private abbrev fMetadata : Imperative.MetaData Core.Expression := fDecl.metadata

/-- The only declaration preceding `Compute` is the declaration of `f`. -/
private theorem prefix_shape :
    userFuncAST.declsBeforeProcedure "Compute" = [fDecl] := by
  native_decide

/-- The declaration preceding `Compute` is the function declaration `fDef`. -/
private theorem fDecl_shape : fDecl = .func fDef fMetadata := by
  native_decide

/-- The factory visible before `Compute` is `Core.Factory` extended with `f`. -/
private theorem visibleFactory_shape :
    visibleFactory = Core.Factory.pushIfNew fDef.toLFunc := by
  rw [visibleFactory, Core.Program.factoryBeforeProcedure, prefix_shape, fDecl_shape]
  rfl

/-- Every name other than `f` resolves in `visibleFactory` as it does in
    `Core.Factory`. -/
private theorem visibleFactory_get?_of_ne_f
    {name : String} {fn : Lambda.LFunc Core.CoreLParams}
    (hne : name ≠ "f") (hcore : Core.Factory[name]? = some fn) :
    visibleFactory[name]? = some fn := by
  rw [visibleFactory_shape]
  have hfname : fDef.toLFunc.name.name = "f" := by native_decide
  have hnew : fDef.toLFunc.name.name ∉ Core.Factory := by
    rw [hfname]
    native_decide
  simp only [Lambda.Factory.pushIfNew, hnew, ↓reduceDIte]
  rw [CoreHoareTestSupport.factory_push_get?]
  rw [ite_eq_right (fun h => hne (h.trans hfname))]
  exact hcore

/-- The name `f` resolves to the user-defined function in `visibleFactory`. -/
private theorem visibleFactory_f : visibleFactory["f"]? = some fDef.toLFunc := by
  rw [visibleFactory_shape]
  have hfname : fDef.toLFunc.name.name = "f" := by native_decide
  have hnew : fDef.toLFunc.name.name ∉ Core.Factory := by
    rw [hfname]
    native_decide
  simp only [Lambda.Factory.pushIfNew, hnew, ↓reduceDIte]
  rw [CoreHoareTestSupport.factory_push_get?]
  have hname : "f" = fDef.toLFunc.name.name := hfname.symm
  simp only [hname, ↓reduceIte]

/-- `Int.Add` retains its Core factory entry in `visibleFactory`. -/
private theorem visibleFactory_intAdd :
    visibleFactory["Int.Add"]? = some (Lambda.intAddFunc (T := Core.CoreLParams)).func :=
  visibleFactory_get?_of_ne_f (by decide) Core.coreFactory_intAdd
/-- `Int.Sub` retains its Core factory entry in `visibleFactory`. -/
private theorem visibleFactory_intSub :
    visibleFactory["Int.Sub"]? = some (Lambda.intSubFunc (T := Core.CoreLParams)).func :=
  visibleFactory_get?_of_ne_f (by decide) Core.coreFactory_intSub
/-- `Int.Mul` retains its Core factory entry in `visibleFactory`. -/
private theorem visibleFactory_intMul :
    visibleFactory["Int.Mul"]? = some (Lambda.intMulFunc (T := Core.CoreLParams)).func :=
  visibleFactory_get?_of_ne_f (by decide) Core.coreFactory_intMul
/-- `Int.Gt` retains its Core factory entry in `visibleFactory`. -/
private theorem visibleFactory_intGt :
    visibleFactory["Int.Gt"]? = some (Lambda.intGtFunc (T := Core.CoreLParams)).func :=
  visibleFactory_get?_of_ne_f (by decide) Core.coreFactory_intGt

set_option maxRecDepth 8000 in
/-- If `x` and `y` contain `a` and `b`, evaluating `f(x, y)` yields
    `(a + b) * (a - b)`. -/
private theorem bodyExpr_eval (σ : Core.CoreStore) (a b : Int)
    (hx : σ xId = some (Lambda.LExpr.intConst () a))
    (hy : σ yId = some (Lambda.LExpr.intConst () b)) :
    Core.Expression.eval visibleFactory σ bodyExpr =
      some (Lambda.LExpr.intConst () ((a + b) * (a - b))) := by
  rw [bodyExpr_shape]
  let ca : Core.Expression.Expr := Lambda.LExpr.intConst () a
  let cb : Core.Expression.Expr := Lambda.LExpr.intConst () b
  let addAB : Core.Expression.Expr :=
    .app () (.app () (Lambda.intAddFunc (T := Core.CoreLParams)).opExpr ca) cb
  let subAB : Core.Expression.Expr :=
    .app () (.app () (Lambda.intSubFunc (T := Core.CoreLParams)).opExpr ca) cb
  have hca (n : Nat) : Lambda.LExpr.eval n visibleFactory σ ca = (ca, .value true) :=
    CoreHoareTestSupport.eval_value_identity n visibleFactory σ ca
      (Lambda.isValue_const_true visibleFactory () (.intConst a))
  have hcb (n : Nat) : Lambda.LExpr.eval n visibleFactory σ cb = (cb, .value true) :=
    CoreHoareTestSupport.eval_value_identity n visibleFactory σ cb
      (Lambda.isValue_const_true visibleFactory () (.intConst b))
  have hadd : Lambda.LExpr.eval 18 visibleFactory σ addAB =
      (Lambda.LExpr.intConst () (a + b), .value true) :=
    Core.eval_intAdd_value_of_numerals visibleFactory σ ca cb
      17 a b visibleFactory_intAdd (hca 17) (hcb 17)
  have hsub : Lambda.LExpr.eval 18 visibleFactory σ subAB =
      (Lambda.LExpr.intConst () (a - b), .value true) :=
    Core.eval_intSub_value_of_numerals visibleFactory σ ca cb
      17 a b visibleFactory_intSub (hca 17) (hcb 17)
  have hmul : Lambda.LExpr.eval 19 visibleFactory σ
      (.app () (.app () (Lambda.intMulFunc (T := Core.CoreLParams)).opExpr addAB) subAB) =
      (Lambda.LExpr.intConst () ((a + b) * (a - b)), .value true) :=
    Core.eval_intMul_value_of_numerals visibleFactory σ addAB subAB
      18 (a + b) (a - b) visibleFactory_intMul hadd hsub
  have hargx : Lambda.LExpr.eval 19 visibleFactory σ (.fvar () xId intTy) =
      (ca, .value true) :=
    CoreHoareTestSupport.eval_fvar_of_value 18 visibleFactory σ () xId intTy ca hx
      (Lambda.isValue_const_true visibleFactory () (.intConst a))
  have hargy : Lambda.LExpr.eval 19 visibleFactory σ (.fvar () yId intTy) =
      (cb, .value true) :=
    CoreHoareTestSupport.eval_fvar_of_value 18 visibleFactory σ () yId intTy cb hy
      (Lambda.isValue_const_true visibleFactory () (.intConst b))
  have hflookup : visibleFactory[fDef.toLFunc.name.name]? = some fDef.toLFunc := by
    rw [show fDef.toLFunc.name.name = "f" by native_decide]
    exact visibleFactory_f
  have hcall : Lambda.Factory.callOfLFunc visibleFactory
      (Lambda.LExpr.mkApp () fDef.opExpr [.fvar () xId intTy, .fvar () yId intTy]) =
      some (fDef.opExpr, [.fvar () xId intTy, .fvar () yId intTy], fDef.toLFunc) :=
    CoreHoareTestSupport.factory_call_mkApp visibleFactory fDef.toLFunc _ hflookup
      (by rw [fDef_shape]; rfl)
  have hcallPartial : Lambda.Factory.callOfLFunc visibleFactory
      (.app () (.app () fDef.opExpr (.fvar () xId intTy)) (.fvar () yId intTy)) true =
      some (fDef.opExpr, [.fvar () xId intTy, .fvar () yId intTy], fDef.toLFunc) :=
    CoreHoareTestSupport.factory_call_mkApp visibleFactory fDef.toLFunc
      [.fvar () xId intTy, .fvar () yId intTy] hflookup
      (by rw [fDef_shape]; rfl) true
  have hnotvalue : Lambda.LExpr.isValue visibleFactory
      (Lambda.LExpr.mkApp () fDef.opExpr [.fvar () xId intTy, .fvar () yId intTy]) = false := by
    change Lambda.LExpr.isValue visibleFactory
      (.app () (.app () fDef.opExpr (.fvar () xId intTy)) (.fvar () yId intTy)) = false
    apply CoreHoareTestSupport.isValue_binary_call_false visibleFactory fDef.toLFunc
      () fDef.opExpr (.fvar () xId intTy) (.fvar () yId intTy) hcallPartial
    · rw [fDef_shape]; rfl
    · rw [fDef_shape]; rfl
  have hshort : Lambda.LExpr.shortCircuitCall? fDef.toLFunc
      [.fvar () xId intTy, .fvar () yId intTy] = none := by rw [fDef_shape]; rfl
  have hbodySome : fDef.toLFunc.body.isSome = true := by rw [fDef_shape]; rfl
  have hbodyGet (h : fDef.toLFunc.body.isSome = true) :
      fDef.toLFunc.body.get h = fBody := by
    have hb : fDef.toLFunc.body = some fBody := by rw [fDef_shape]; rfl
    exact Option.get_of_eq_some h hb
  have hkeys : fDef.toLFunc.inputs.keys = [xId, yId] := by rw [fDef_shape]; rfl
  have hzip : [xId, yId].zip [ca, cb] = [(xId, ca), (yId, cb)] := rfl
  have hattrInline : fDef.toLFunc.attr.contains .inline = true := by native_decide
  have htypes : fDef.toLFunc.computeTypeSubst fDef.opExpr [ca, cb] =
      some Lambda.Subst.empty := by rw [fDef_shape]; rfl
  have hsubst : (fBody.applyTypeSubst Lambda.Subst.empty).substFvarsLifting
      [(xId, ca), (yId, cb)] =
      (.app () (.app () (Lambda.intMulFunc (T := Core.CoreLParams)).opExpr addAB) subAB) := rfl
  apply CoreHoareTestSupport.evalFully_of_value_true visibleFactory σ _ 20
  rw [Lambda.LExpr.eval.eq_def (TBase := Core.CoreLParams)]
  simp only [hnotvalue, Bool.false_eq_true, ↓reduceIte, hcall, hshort,
    hargx, hargy, List.map_cons, List.map_nil,
    Lambda.LExpr.EvalResult.isValueTrue, List.all_cons, List.all_nil, Bool.and_true]
  simp only [hbodySome, hbodyGet, hkeys, hzip, hattrInline, Bool.true_or,
    Bool.and_true, ↓reduceDIte, htypes, hsubst, hmul,
    Lambda.LExpr.combineEvalResValueFlag, Lambda.LExpr.EvalResult.combineValueFlag]


/-- The function visible to the procedure retains its arithmetic body in the
    prefix factory. -/
example :
    (((userFuncAST.factoryBeforeProcedure "Compute").get? "f").bind
      (fun fn => fn.body)).isSome = true := by
  native_decide

private def fBodyOpNames : List String :=
  ((((userFuncAST.factoryBeforeProcedure "Compute").get? "f").bind
      (fun fn => fn.body)).map fun body => body.getOps.map (·.name)).getD []

/-- The retained body computes `(x + y) * (x - y)`. -/
example :
    (["Int.Add", "Int.Sub", "Int.Mul"].all fBodyOpNames.contains) = true := by
  native_decide

/-- Functions declared after the procedure are absent from its prefix factory. -/
example :
    ((userFuncAST.factoryBeforeProcedure "Compute").get? "Later").isSome = false := by
  native_decide

private def assignedFunctionName? : Option String :=
  match computeProc.body with
  | .structured [Imperative.Stmt.cmd
      (Imperative.CmdExt.cmd (Imperative.Cmd.set z (.det e) _))] =>
    if z.name != "z" then none
    else
      match (Lambda.getLFuncCall e).1 with
      | .op _ name _ => some name.name
      | _ => none
  | _ => none

/-- The procedure body assigns `z` from a call to `f`. -/
example : assignedFunctionName? = some "f" := by
  native_decide

private def intArrowTy : Lambda.LMonoTy := .arrow .int (.arrow .int .int)
private abbrev gtOp : Core.Expression.Expr := Core.intGtOp
private abbrev addOp : Core.Expression.Expr := Core.intAddOp
private def xExpr : Core.Expression.Expr := .fvar () xId intTy
private def yExpr : Core.Expression.Expr := .fvar () yId intTy
private def zExpr : Core.Expression.Expr := .fvar () zId intTy
private def zeroExpr : Core.Expression.Expr := .const () (.intConst 0)
/-- `LExpr.intConst` is the Core integer-literal constructor. -/
private theorem intConst_eq (i : Int) :
    (Lambda.LExpr.intConst () i : Core.Expression.Expr) = .const () (.intConst i) := rfl
private def addXY : Core.Expression.Expr := .app () (.app () addOp xExpr) yExpr
private def reqXY : Core.Expression.Expr := .app () (.app () gtOp xExpr) yExpr
private def reqSum : Core.Expression.Expr := .app () (.app () gtOp addXY) zeroExpr
private def ensZ : Core.Expression.Expr := .app () (.app () gtOp zExpr) zeroExpr

/-- The first precondition of `Compute` is `int.gt(x, y)`. -/
private theorem reqXY_mem : ∃ label check,
    (label, check) ∈ computeProc.spec.preconditions.toList ∧ check.expr = reqXY :=
  ⟨(computeProc.spec.preconditions.toList[0]!).1,
    (computeProc.spec.preconditions.toList[0]!).2, by native_decide, by native_decide⟩
/-- The second precondition of `Compute` is `int.gt(x + y, 0)`. -/
private theorem reqSum_mem : ∃ label check,
    (label, check) ∈ computeProc.spec.preconditions.toList ∧ check.expr = reqSum :=
  ⟨(computeProc.spec.preconditions.toList[1]!).1,
    (computeProc.spec.preconditions.toList[1]!).2, by native_decide, by native_decide⟩
/-- Every checked postcondition of `Compute` is `int.gt(z, 0)`. -/
private theorem ensures_shape : ∀ label check,
    (label, check) ∈ computeProc.spec.postconditions.toList →
    check.attr = Core.Procedure.CheckAttr.Default → check.expr = ensZ := by
  intro label check hmem _
  have hlist : computeProc.spec.postconditions.toList =
      [computeProc.spec.postconditions.toList.head!] := by native_decide
  rw [hlist] at hmem
  have hp : (label, check) = computeProc.spec.postconditions.toList.head! :=
    List.mem_singleton.mp hmem
  have hl := congrArg Prod.fst hp
  have hc := congrArg Prod.snd hp
  change label = _ at hl
  change check = _ at hc
  subst label
  subst check
  native_decide

/-- If `Compute`'s `x > y` precondition holds with `x = a` and `y = b`,
    then `a > b`. -/
private theorem check_reqXY_implies {factory : Core.Expression.Factory}
    (model : Lambda.Interp factory)
    (hgtLookup : factory["Int.Gt"]? =
      some (Lambda.intGtFunc (T := Core.CoreLParams)).func)
    (ρ : Imperative.Env Core.Expression) (label : Core.CoreLabel)
    (check : Core.Procedure.Check) (a b : Int)
    (hfac : ρ.factory = factory)
    (hx : ρ.store xId = some (Lambda.LExpr.intConst () a))
    (hy : ρ.store yId = some (Lambda.LExpr.intConst () b))
    (hexpr : check.expr = reqXY)
    (hcheck : Core.Logic.Hoare.Procedure.checkAsPredicate model ρ label check) : a > b := by
  let world := CoreHoareTestSupport.someValuation model
  rcases hcheck world with ⟨_, hden⟩ | ⟨hne, _⟩
  · have hgtClosed : Lambda.LExpr.substFvarsFromEnv ρ.store gtOp = gtOp := by
      apply Lambda.LExpr.substFvarsFromEnv_closed_identity
      rfl
    have hcap : Core.Logic.capturedExpr
        { factory := ρ.factory, store := ρ.store, label := label,
          expr := check.expr, metadata := check.md } =
        (.app () (.app () gtOp (.const () (.intConst a))) (.const () (.intConst b))) := by
      rw [hexpr]
      simp [Core.Logic.capturedExpr, reqXY, xExpr, yExpr,
        Lambda.LExpr.substFvarsFromEnv, Lambda.Env.mk, hgtClosed, intConst_eq, hx, hy]
    rw [hcap] at hden
    obtain ⟨hty, hval⟩ := hden
    rw [Core.denote_intGt_of_lookup model hgtLookup world.freeVarVal world.tyVarVal .nil hty
      .const .const (Lambda.denote_intConst _ _ _ _ _ _)
      (Lambda.denote_intConst _ _ _ _ _ _)] at hval
    exact of_decide_eq_true hval
  · exact absurd hfac hne

/-- If `Compute`'s `x + y > 0` precondition holds with `x = a` and
    `y = b`, then `a + b > 0`. -/
private theorem check_reqSum_implies {factory : Core.Expression.Factory}
    (model : Lambda.Interp factory)
    (haddLookup : factory["Int.Add"]? =
      some (Lambda.intAddFunc (T := Core.CoreLParams)).func)
    (hgtLookup : factory["Int.Gt"]? =
      some (Lambda.intGtFunc (T := Core.CoreLParams)).func)
    (ρ : Imperative.Env Core.Expression) (label : Core.CoreLabel)
    (check : Core.Procedure.Check) (a b : Int)
    (hfac : ρ.factory = factory)
    (hx : ρ.store xId = some (Lambda.LExpr.intConst () a))
    (hy : ρ.store yId = some (Lambda.LExpr.intConst () b))
    (hexpr : check.expr = reqSum)
    (hcheck : Core.Logic.Hoare.Procedure.checkAsPredicate model ρ label check) : a + b > 0 := by
  let world := CoreHoareTestSupport.someValuation model
  rcases hcheck world with ⟨_, hden⟩ | ⟨hne, _⟩
  · have hgtClosed : Lambda.LExpr.substFvarsFromEnv ρ.store gtOp = gtOp := by
      apply Lambda.LExpr.substFvarsFromEnv_closed_identity
      rfl
    have haddClosed : Lambda.LExpr.substFvarsFromEnv ρ.store addOp = addOp := by
      apply Lambda.LExpr.substFvarsFromEnv_closed_identity
      rfl
    have hcap : Core.Logic.capturedExpr
        { factory := ρ.factory, store := ρ.store, label := label,
          expr := check.expr, metadata := check.md } =
        (.app () (.app () gtOp
          (.app () (.app () addOp (.const () (.intConst a))) (.const () (.intConst b))))
          (.const () (.intConst 0))) := by
      rw [hexpr]
      simp [Core.Logic.capturedExpr, reqSum, addXY, xExpr, yExpr, zeroExpr,
        Lambda.LExpr.substFvarsFromEnv, Lambda.Env.mk, hgtClosed, haddClosed,
        intConst_eq, hx, hy]
    rw [hcap] at hden
    obtain ⟨hty, hval⟩ := hden
    have haddTy : Lambda.LExpr.HasTypeA (T := Core.CoreLParams) []
        (.app () (.app () addOp (.const () (.intConst a))) (.const () (.intConst b))) .int :=
      .app (.app .op .const) .const
    rw [Core.denote_intGt_of_lookup model hgtLookup world.freeVarVal world.tyVarVal .nil hty
      haddTy .const
      (Core.denote_intAdd_of_lookup model haddLookup world.freeVarVal world.tyVarVal .nil
        haddTy .const .const (Lambda.denote_intConst _ _ _ _ _ _)
        (Lambda.denote_intConst _ _ _ _ _ _))
      (Lambda.denote_intConst _ _ _ _ _ _)] at hval
    exact of_decide_eq_true hval
  · exact absurd hfac hne

/-- If `z` contains a positive integer, `Compute`'s semantic postcondition
    holds in every world of `model`. -/
private theorem post_holds {factory : Core.Expression.Factory}
    (model : Lambda.Interp factory)
    (hgtLookup : factory["Int.Gt"]? =
      some (Lambda.intGtFunc (T := Core.CoreLParams)).func)
    (ρ : Imperative.Env Core.Expression) (r : Int)
    (hfac : ρ.factory = factory)
    (hz : ρ.store zId = some (Lambda.LExpr.intConst () r))
    (hr : r > 0) :
    Core.Logic.Hoare.Procedure.contractPost model computeProc ρ := by
  intro label check hmem hattr world
  have hexpr := ensures_shape label check hmem hattr
  refine .inl ⟨hfac, ?_⟩
  have hgtClosed : Lambda.LExpr.substFvarsFromEnv ρ.store gtOp = gtOp := by
    apply Lambda.LExpr.substFvarsFromEnv_closed_identity
    rfl
  have hcap : Core.Logic.capturedExpr
      { factory := ρ.factory, store := ρ.store, label := label,
        expr := check.expr, metadata := check.md } =
      (.app () (.app () gtOp (.const () (.intConst r))) (.const () (.intConst 0))) := by
    rw [hexpr]
    simp [Core.Logic.capturedExpr, ensZ, zExpr, zeroExpr,
      Lambda.LExpr.substFvarsFromEnv, Lambda.Env.mk, hgtClosed, intConst_eq, hz]
  rw [hcap]
  have hty : Lambda.LExpr.HasTypeA (T := Core.CoreLParams) []
      (.app () (.app () gtOp (.const () (.intConst r))) (.const () (.intConst 0))) .bool :=
    .app (.app (.op) (.const)) (.const)
  refine ⟨hty, ?_⟩
  rw [Core.denote_intGt_of_lookup model hgtLookup world.freeVarVal world.tyVarVal .nil hty
    .const .const (Lambda.denote_intConst _ _ _ _ _ _) (Lambda.denote_intConst _ _ _ _ _ _)]
  exact decide_eq_true hr

/-- If `x > y` and `x + y > 0`, then `(x + y) * (x - y) > 0`. -/
private theorem result_positive (x y : Int)
    (hxy : x > y) (hsum : x + y > 0) :
    (x + y) * (x - y) > 0 := by
  have hdiff : x - y > 0 := by omega
  exact Int.mul_pos hsum hdiff

/-- `Compute` meets its arithmetic contract in the factory visible before
    its declaration. -/
theorem compute_meets_contract :
    Core.Logic.Hoare.Procedure.contractTriple userFuncAST testParams "Compute" := by
  let command : Core.Command :=
    Imperative.CmdExt.cmd (Imperative.Cmd.set zId (.det bodyExpr) bodyMd)
  refine Core.Logic.Hoare.Procedure.contractTriple_singleton_cmd
    userFuncAST testParams "Compute" computeProc (by native_decide) command ?_ (by native_decide)
      ?_ ?_
  · simpa [command] using compute_body_shape
  · intro model ρ₀ σ' emitted hpre _hwf hstep
    obtain ⟨hchecks, hfac, _hold, htyped⟩ := hpre
    obtain ⟨vx, hx, hvx⟩ := htyped xId .int (by native_decide)
    obtain ⟨vy, hy, hvy⟩ := htyped yId .int (by native_decide)
    change ∃ a : Int, vx = Lambda.LExpr.intConst () a at hvx
    change ∃ b : Int, vy = Lambda.LExpr.intConst () b at hvy
    obtain ⟨a, rfl⟩ := hvx
    obtain ⟨b, rfl⟩ := hvy
    obtain ⟨labelXY, checkXY, hmemXY, hexprXY⟩ := reqXY_mem
    obtain ⟨labelSum, checkSum, hmemSum, hexprSum⟩ := reqSum_mem
    have hxy : a > b := check_reqXY_implies model visibleFactory_intGt ρ₀ labelXY checkXY a b
      hfac hx hy hexprXY (hchecks labelXY checkXY hmemXY)
    have hsum : a + b > 0 := check_reqSum_implies model visibleFactory_intAdd visibleFactory_intGt ρ₀ labelSum checkSum a b
      hfac hx hy hexprSum (hchecks labelSum checkSum hmemSum)
    have hpos := result_positive a b hxy hsum
    dsimp [command] at hstep
    cases hstep with
    | cmd_sem hcmd =>
      cases hcmd with
      | eval_set heval hupdate _ _ =>
        have hbody := bodyExpr_eval ρ₀.store a b hx hy
        have heval' := heval
        rw [hfac] at heval'
        have hv : _ = (Lambda.LExpr.intConst () ((a + b) * (a - b)) : Core.Expression.Expr) :=
          Option.some.inj (heval'.symm.trans hbody)
        cases hupdate with
        | update _ hnew _ =>
          rw [hv] at hnew
          exact ⟨True.intro, fun _ =>
            post_holds model visibleFactory_intGt { ρ₀ with store := σ' } ((a + b) * (a - b))
              hfac hnew hpos⟩
  · intro model
    exact Imperative.Logic.Hoare.postWF_of_definedVars_nil _ (by
      simp [command, Imperative.Block.definedVars, Imperative.Stmt.definedVars,
        Imperative.HasVarsImp.definedVars, Imperative.CmdExt.definedVars,
        Imperative.Cmd.definedVars])

private def contractOpNames : List String :=
  (computeProc.spec.preconditions.values ++ computeProc.spec.postconditions.values).flatMap
    (fun check => check.expr.getOps.map (·.name))

/-- The translated contract contains both strict comparisons and the positive-sum
    premise needed to conclude that `f(x, y)` is positive. -/
example :
    (["Int.Gt", "Int.Add"].all contractOpNames.contains) = true := by
  native_decide

/-- The translated procedure retains both preconditions and its postcondition. -/
example :
    computeProc.spec.preconditions.toList.length = 2 ∧
    computeProc.spec.postconditions.toList.length = 1 := by
  native_decide

/-! ## Specification-only use of a non-inline function -/

private def specOnlyPgm : Program :=
#strata
program Core;

function fSpec(x : int, y : int) : int {
  int.mul(int.add(x, y), int.sub(x, y))
}

procedure CheckProduct(x : int, y : int)
spec {
  requires int.gt(x, y);
  requires int.gt(int.add(x, y), 0);
  ensures int.gt(fSpec(x, y), 0);
}
{
};
#end

private def specOnlyAST : Core.Program := cstToAST specOnlyPgm
private abbrev checkProductProc : Core.Procedure :=
  (specOnlyAST.findProcByString? "CheckProduct").get!
private abbrev fSpecDef : Core.Function :=
  (Core.Program.Function.find? specOnlyAST ⟨"fSpec", ()⟩).get!
private abbrev specFactory : Core.Expression.Factory :=
  specOnlyAST.factoryBeforeProcedure "CheckProduct"

/-- The specification-only function has the same arithmetic body as `f` but
    does not carry the inline attribute. -/
private theorem fSpecDef_shape : fSpecDef = {
    name := ⟨"fSpec", ()⟩
    inputs := [(xId, .int), (yId, .int)]
    output := .int
    body := some fBody } := by
  native_decide

private abbrev fSpecDecl : Core.Decl := specOnlyAST.decls.head!
private abbrev fSpecMetadata : Imperative.MetaData Core.Expression := fSpecDecl.metadata

/-- The only declaration preceding `CheckProduct` is `fSpec`. -/
private theorem specPrefix_shape :
    specOnlyAST.declsBeforeProcedure "CheckProduct" = [fSpecDecl] := by
  native_decide

/-- The prefix declaration is the definition `fSpecDef`. -/
private theorem fSpecDecl_shape : fSpecDecl = .func fSpecDef fSpecMetadata := by
  native_decide

/-- The factory visible before `CheckProduct` is `Core.Factory` extended with
    the non-inline function `fSpec`. -/
private theorem specFactory_shape :
    specFactory = Core.Factory.pushIfNew fSpecDef.toLFunc := by
  rw [specFactory, Core.Program.factoryBeforeProcedure, specPrefix_shape,
    fSpecDecl_shape]
  rfl

/-- `fSpec` resolves to its definition in `specFactory`. -/
private theorem specFactory_fSpec :
    specFactory["fSpec"]? = some fSpecDef.toLFunc := by
  rw [specFactory_shape]
  have hname : fSpecDef.toLFunc.name.name = "fSpec" := by native_decide
  have hnew : fSpecDef.toLFunc.name.name ∉ Core.Factory := by
    rw [hname]
    native_decide
  simp only [Lambda.Factory.pushIfNew, hnew, ↓reduceDIte]
  rw [CoreHoareTestSupport.factory_push_get?]
  have : "fSpec" = fSpecDef.toLFunc.name.name := hname.symm
  simp only [this, ↓reduceIte]

/-- Names other than `fSpec` retain their Core factory lookup. -/
private theorem specFactory_get?_of_ne_fSpec
    {name : String} {fn : Lambda.LFunc Core.CoreLParams}
    (hne : name ≠ "fSpec") (hcore : Core.Factory[name]? = some fn) :
    specFactory[name]? = some fn := by
  rw [specFactory_shape]
  have hname : fSpecDef.toLFunc.name.name = "fSpec" := by native_decide
  have hnew : fSpecDef.toLFunc.name.name ∉ Core.Factory := by
    rw [hname]
    native_decide
  simp only [Lambda.Factory.pushIfNew, hnew, ↓reduceDIte]
  rw [CoreHoareTestSupport.factory_push_get?]
  rw [ite_eq_right (fun h => hne (h.trans hname))]
  exact hcore

/-- `Int.Add` retains its Core entry in `specFactory`. -/
private theorem specFactory_intAdd :
    specFactory["Int.Add"]? = some (Lambda.intAddFunc (T := Core.CoreLParams)).func :=
  specFactory_get?_of_ne_fSpec (by decide) Core.coreFactory_intAdd
/-- `Int.Sub` retains its Core entry in `specFactory`. -/
private theorem specFactory_intSub :
    specFactory["Int.Sub"]? = some (Lambda.intSubFunc (T := Core.CoreLParams)).func :=
  specFactory_get?_of_ne_fSpec (by decide) Core.coreFactory_intSub
/-- `Int.Mul` retains its Core entry in `specFactory`. -/
private theorem specFactory_intMul :
    specFactory["Int.Mul"]? = some (Lambda.intMulFunc (T := Core.CoreLParams)).func :=
  specFactory_get?_of_ne_fSpec (by decide) Core.coreFactory_intMul
/-- `Int.Gt` retains its Core entry in `specFactory`. -/
private theorem specFactory_intGt :
    specFactory["Int.Gt"]? = some (Lambda.intGtFunc (T := Core.CoreLParams)).func :=
  specFactory_get?_of_ne_fSpec (by decide) Core.coreFactory_intGt

private def fSpecOp : Core.Expression.Expr :=
  .op () ⟨"fSpec", ()⟩ (some intArrowTy)
private def fSpecCall : Core.Expression.Expr :=
  .app () (.app () fSpecOp xExpr) yExpr
private def specEns : Core.Expression.Expr := .app () (.app () gtOp fSpecCall) zeroExpr

/-- `CheckProduct` has an empty body. -/
private theorem checkProduct_body : checkProductProc.body = .structured [] := by
  native_decide

/-- The first precondition of `CheckProduct` is `x > y`. -/
private theorem specReqXY_mem : ∃ label check,
    (label, check) ∈ checkProductProc.spec.preconditions.toList ∧ check.expr = reqXY :=
  ⟨(checkProductProc.spec.preconditions.toList[0]!).1,
    (checkProductProc.spec.preconditions.toList[0]!).2,
    by native_decide, by native_decide⟩

/-- The second precondition of `CheckProduct` is `x + y > 0`. -/
private theorem specReqSum_mem : ∃ label check,
    (label, check) ∈ checkProductProc.spec.preconditions.toList ∧ check.expr = reqSum :=
  ⟨(checkProductProc.spec.preconditions.toList[1]!).1,
    (checkProductProc.spec.preconditions.toList[1]!).2,
    by native_decide, by native_decide⟩

/-- Every checked postcondition of `CheckProduct` is `fSpec(x, y) > 0`. -/
private theorem specEnsures_shape : ∀ label check,
    (label, check) ∈ checkProductProc.spec.postconditions.toList →
    check.attr = Core.Procedure.CheckAttr.Default → check.expr = specEns := by
  intro label check hmem _
  have hlist : checkProductProc.spec.postconditions.toList =
      [checkProductProc.spec.postconditions.toList.head!] := by native_decide
  rw [hlist] at hmem
  have hp : (label, check) = checkProductProc.spec.postconditions.toList.head! :=
    List.mem_singleton.mp hmem
  have hl := congrArg Prod.fst hp
  have hc := congrArg Prod.snd hp
  change label = _ at hl
  change check = _ at hc
  subst label
  subst check
  native_decide

/-- In a model where the Core integer operators retain their entries, the body
    `(x + y) * (x - y)` denotes that arithmetic expression when `x = a` and
    `y = b`. -/
private theorem denote_fBody {factory : Core.Expression.Factory}
    (model : Lambda.Interp factory)
    (haddLookup : factory["Int.Add"]? =
      some (Lambda.intAddFunc (T := Core.CoreLParams)).func)
    (hsubLookup : factory["Int.Sub"]? =
      some (Lambda.intSubFunc (T := Core.CoreLParams)).func)
    (hmulLookup : factory["Int.Mul"]? =
      some (Lambda.intMulFunc (T := Core.CoreLParams)).func)
    (fv : Lambda.FreeVarVal Core.CoreLParams model.tcInterp)
    (vt : Lambda.TyVarVal) (a b : Int)
    (hfx : fv xId (Lambda.LMonoTy.int.substTyVars vt) = a)
    (hfy : fv yId (Lambda.LMonoTy.int.substTyVars vt) = b)
    (h : Lambda.LExpr.HasTypeA (T := Core.CoreLParams) [] fBody .int) :
    Lambda.LExpr.denote model.tcInterp model.opInterp fv vt .nil fBody .int h =
      (a + b) * (a - b) := by
  let xe : Core.Expression.Expr := .fvar () xId intTy
  let ye : Core.Expression.Expr := .fvar () yId intTy
  let ae : Core.Expression.Expr := .app () (.app () Core.intAddOp xe) ye
  let se : Core.Expression.Expr := .app () (.app () Core.intSubOp xe) ye
  have hxTy : Lambda.LExpr.HasTypeA (T := Core.CoreLParams) [] xe .int := .fvar
  have hyTy : Lambda.LExpr.HasTypeA (T := Core.CoreLParams) [] ye .int := .fvar
  have hdx : Lambda.LExpr.denote model.tcInterp model.opInterp fv vt .nil xe .int hxTy = a := by
    change fv xId (Lambda.LMonoTy.int.substTyVars vt) = a
    exact hfx
  have hdy : Lambda.LExpr.denote model.tcInterp model.opInterp fv vt .nil ye .int hyTy = b := by
    change fv yId (Lambda.LMonoTy.int.substTyVars vt) = b
    exact hfy
  have hadd : Lambda.LExpr.HasTypeA (T := Core.CoreLParams) [] ae .int :=
    .app (.app .op hxTy) hyTy
  have hsub : Lambda.LExpr.HasTypeA (T := Core.CoreLParams) [] se .int :=
    .app (.app .op hxTy) hyTy
  exact Core.denote_intMul_of_lookup model hmulLookup fv vt .nil h hadd hsub
    (Core.denote_intAdd_of_lookup model haddLookup fv vt .nil hadd hxTy hyTy hdx hdy)
    (Core.denote_intSub_of_lookup model hsubLookup fv vt .nil hsub hxTy hyTy hdx hdy)


/-- In every model of `specFactory`, the interpretation of `fSpec`
    applied to `a` and `b` is `(a + b) * (a - b)`. -/
private theorem fSpec_opInterp (model : Lambda.Interp specFactory)
    (fv : Lambda.FreeVarVal Core.CoreLParams model.tcInterp)
    (vt : Lambda.TyVarVal) (a b : Int) :
    (model.opInterp "fSpec" (Lambda.LSort.mkArrow .int [.int, .int]) a b : Int) =
      (a + b) * (a - b) := by
  have hmem : "fSpec" ∈ specFactory :=
    CoreHoareTestSupport.factory_mem_of_get? specFactory_fSpec
  have hget : specFactory["fSpec"]'hmem = fSpecDef.toLFunc :=
    CoreHoareTestSupport.factory_get_of_get? specFactory_fSpec
  have hbody : (specFactory["fSpec"]'hmem).body = some fBody := by
    rw [hget, fSpecDef_shape]
    rfl
  have hconsistent := model.interpConsistent.1 "fSpec" hmem fBody hbody
  have hconsistent' : Lambda.LFunc.InterpConsistentBody
      model.tcInterp model.opInterp fSpecDef.toLFunc fBody := by
    rw [← hget]
    exact hconsistent
  rw [fSpecDef_shape] at hconsistent'
  simp only [Lambda.LFuncDefined.toLFunc] at hconsistent'
  have hbodyTy : Lambda.LExpr.HasTypeA (T := Core.CoreLParams) [] fBody .int :=
    Lambda.LExpr.typeCheck_to_HasTypeA (by native_decide)
  let argVal := CoreHoareTestSupport.withTwoIntArgs fv xId yId a b
  have heq := hconsistent' vt fv hbodyTy (.cons a (.cons b .nil))
  change (model.opInterp "fSpec" (Lambda.LSort.mkArrow .int [.int, .int]) a b : Int) =
    Lambda.LExpr.denote model.tcInterp model.opInterp argVal vt .nil fBody .int hbodyTy at heq
  have hfx : argVal xId Lambda.LSort.int = a :=
    CoreHoareTestSupport.withTwoIntArgs_left fv xId yId a b
  have hfy : argVal yId Lambda.LSort.int = b :=
    CoreHoareTestSupport.withTwoIntArgs_right fv xId yId a b (by decide)
  have hbodyDenote := denote_fBody model specFactory_intAdd specFactory_intSub
    specFactory_intMul argVal vt a b hfx hfy hbodyTy
  exact heq.trans hbodyDenote

/-- Applying `fSpec` to integer literals denotes `(a + b) * (a - b)` without
    requiring the function to be inline. -/
private theorem denote_fSpecCall (model : Lambda.Interp specFactory)
    (fv : Lambda.FreeVarVal Core.CoreLParams model.tcInterp)
    (vt : Lambda.TyVarVal) (a b : Int)
    (h : Lambda.LExpr.HasTypeA (T := Core.CoreLParams) []
      (Lambda.LExpr.app ()
        (Lambda.LExpr.app () fSpecOp (.const () (.intConst a)))
        (.const () (.intConst b))) .int) :
    Lambda.LExpr.denote model.tcInterp model.opInterp fv vt .nil
      (Lambda.LExpr.app ()
        (Lambda.LExpr.app () fSpecOp (.const () (.intConst a)))
        (.const () (.intConst b))) .int h =
      (a + b) * (a - b) := by
  have hop : Lambda.LExpr.HasTypeA (T := Core.CoreLParams) [] fSpecOp
      (.arrow .int (.arrow .int .int)) := .op
  have ha : Lambda.LExpr.HasTypeA (T := Core.CoreLParams) []
      (.const () (.intConst a)) .int := .const
  have hb : Lambda.LExpr.HasTypeA (T := Core.CoreLParams) []
      (.const () (.intConst b)) .int := .const
  have happ : Lambda.LExpr.HasTypeA (T := Core.CoreLParams) []
      (.app () fSpecOp (.const () (.intConst a))) (.arrow .int .int) :=
    .app hop ha
  change Lambda.LExpr.denote model.tcInterp model.opInterp fv vt .nil
      (.app () (.app () fSpecOp (.const () (.intConst a)))
        (.const () (.intConst b))) .int h = _
  rw [Lambda.denote_app .nil happ hb h, Lambda.denote_app .nil hop ha happ]
  have hic : ∀ (i : Int) (hh : Lambda.LExpr.HasTypeA (T := Core.CoreLParams) []
      (.const () (.intConst i)) .int),
      Lambda.LExpr.denote model.tcInterp model.opInterp fv vt .nil
        (.const () (.intConst i)) .int hh = i :=
    fun i hh => Lambda.denote_intConst _ _ _ _ _ hh
  simp only [hic]
  simp only [fSpecOp] at hop ⊢
  rw [Lambda.denote_op]
  exact fSpec_opInterp model fv vt a b

/-- In every model of `specFactory`, `fSpec(a, b) > 0` denotes the
    positivity of `(a + b) * (a - b)`. -/
private theorem denote_fSpec_gt_zero (model : Lambda.Interp specFactory)
    (fv : Lambda.FreeVarVal Core.CoreLParams model.tcInterp)
    (vt : Lambda.TyVarVal) (a b : Int)
    (h : Lambda.LExpr.HasTypeA (T := Core.CoreLParams) []
      (.app () (.app () gtOp
        (Lambda.LExpr.app ()
          (Lambda.LExpr.app () fSpecOp (.const () (.intConst a)))
          (.const () (.intConst b))))
        (.const () (.intConst 0))) .bool) :
    (Lambda.LExpr.denote model.tcInterp model.opInterp fv vt .nil
      (.app () (.app () gtOp
        (Lambda.LExpr.app ()
          (Lambda.LExpr.app () fSpecOp (.const () (.intConst a)))
          (.const () (.intConst b))))
        (.const () (.intConst 0))) .bool h : Bool) =
      decide ((a + b) * (a - b) > 0) := by
  have hfTy : Lambda.LExpr.HasTypeA (T := Core.CoreLParams) []
      (Lambda.LExpr.app ()
        (Lambda.LExpr.app () fSpecOp (.const () (.intConst a)))
        (.const () (.intConst b))) .int :=
    .app (.app (.op) (.const)) (.const)
  exact Core.denote_intGt_of_lookup model specFactory_intGt fv vt .nil h hfTy .const
    (denote_fSpecCall model fv vt a b hfTy) (Lambda.denote_intConst _ _ _ _ _ _)

/-- If `x = a`, `y = b`, and their product expression is positive, then
    `CheckProduct`'s semantic postcondition holds without evaluating `fSpec`. -/
private theorem specPost_holds (model : Lambda.Interp specFactory)
    (ρ : Imperative.Env Core.Expression) (a b : Int)
    (hfac : ρ.factory = specFactory)
    (hx : ρ.store xId = some (Lambda.LExpr.intConst () a))
    (hy : ρ.store yId = some (Lambda.LExpr.intConst () b))
    (hpos : (a + b) * (a - b) > 0) :
    Core.Logic.Hoare.Procedure.contractPost model checkProductProc ρ := by
  intro label check hmem hattr world
  have hexpr := specEnsures_shape label check hmem hattr
  refine .inl ⟨hfac, ?_⟩
  have hgtClosed : Lambda.LExpr.substFvarsFromEnv ρ.store gtOp = gtOp := by
    apply Lambda.LExpr.substFvarsFromEnv_closed_identity
    rfl
  have hfClosed : Lambda.LExpr.substFvarsFromEnv ρ.store fSpecOp = fSpecOp := by
    apply Lambda.LExpr.substFvarsFromEnv_closed_identity
    rfl
  have hfCall : Lambda.LExpr.substFvarsFromEnv ρ.store fSpecCall =
      Lambda.LExpr.app ()
        (Lambda.LExpr.app () fSpecOp (.const () (.intConst a)))
        (.const () (.intConst b)) := by
    simp [fSpecCall, xExpr, yExpr, Lambda.LExpr.substFvarsFromEnv,
      hfClosed, intConst_eq, hx, hy]
  have hcap : Core.Logic.capturedExpr
      { factory := ρ.factory, store := ρ.store, label := label,
        expr := check.expr, metadata := check.md } =
      (.app () (.app () gtOp
        (Lambda.LExpr.app ()
          (Lambda.LExpr.app () fSpecOp (.const () (.intConst a)))
          (.const () (.intConst b))))
        (.const () (.intConst 0))) := by
    rw [hexpr]
    simp [Core.Logic.capturedExpr, specEns, zeroExpr,
      Lambda.LExpr.substFvarsFromEnv, Lambda.Env.mk, hgtClosed, hfCall]
  rw [hcap]
  have hty : Lambda.LExpr.HasTypeA (T := Core.CoreLParams) []
      (.app () (.app () gtOp
        (Lambda.LExpr.app ()
          (Lambda.LExpr.app () fSpecOp (.const () (.intConst a)))
          (.const () (.intConst b))))
        (.const () (.intConst 0))) .bool :=
    .app (.app (.op) (.app (.app (.op) (.const)) (.const))) (.const)
  refine ⟨hty, ?_⟩
  rw [denote_fSpec_gt_zero model world.freeVarVal world.tyVarVal a b hty]
  exact decide_eq_true hpos

/-- `CheckProduct` meets its contract although `fSpec` is not inline,
    because contract clauses use denotational interpretation rather than the
    executable expression evaluator. -/
theorem checkProduct_meets_contract :
    Core.Logic.Hoare.Procedure.contractTriple specOnlyAST testParams "CheckProduct" := by
  refine Core.Logic.Hoare.Procedure.contractTriple_of_core_typed
    specOnlyAST testParams "CheckProduct" checkProductProc []
      (by native_decide) checkProduct_body (by native_decide) (fun model => ?_)
  refine Strata.Logic.Hoare.consequence
    (Core.Logic.EventLang.coreBlock specOnlyAST.findProcByString?) testParams
    (Core.Logic.Hoare.skip (factory := specFactory) specOnlyAST.findProcByString?
      testParams "" #[]
      (Core.Logic.Hoare.Procedure.contractPre model checkProductProc) model)
    (fun _ hpre => hpre) (fun ρ hpre => ?_)
  obtain ⟨hchecks, hfac, _hold, htyped⟩ := hpre
  obtain ⟨vx, hx, hvx⟩ := htyped xId .int (by native_decide)
  obtain ⟨vy, hy, hvy⟩ := htyped yId .int (by native_decide)
  change ∃ a : Int, vx = Lambda.LExpr.intConst () a at hvx
  change ∃ b : Int, vy = Lambda.LExpr.intConst () b at hvy
  obtain ⟨a, rfl⟩ := hvx
  obtain ⟨b, rfl⟩ := hvy
  obtain ⟨labelXY, checkXY, hmemXY, hexprXY⟩ := specReqXY_mem
  obtain ⟨labelSum, checkSum, hmemSum, hexprSum⟩ := specReqSum_mem
  have hxy : a > b := check_reqXY_implies model specFactory_intGt
    ρ labelXY checkXY a b hfac hx hy hexprXY
    (hchecks labelXY checkXY hmemXY)
  have hsum : a + b > 0 := check_reqSum_implies model specFactory_intAdd
    specFactory_intGt ρ labelSum checkSum a b hfac hx hy hexprSum
    (hchecks labelSum checkSum hmemSum)
  exact specPost_holds model ρ a b hfac hx hy (result_positive a b hxy hsum)

/-- `fSpec` is deliberately not inline. -/
example : fSpecDef.toLFunc.attr.contains .inline = false := by
  native_decide

/-- `CheckProduct` has no output parameters and no executable statements. -/
example : checkProductProc.header.outputs.isEmpty ∧
    checkProductProc.body = .structured [] := by
  native_decide

end Strata
