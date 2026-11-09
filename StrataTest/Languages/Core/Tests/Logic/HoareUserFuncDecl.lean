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
  factory containing the preceding definition of `f`.
- `checkProduct_meets_contract` — a bodyless procedure satisfies an analogous
  contract using the non-inline `fSpec` only in its specification.
- `bodyExpr_eval` — a call to `f` evaluates to `(x + y) * (x - y)`.
-/

open StrataDDM (Program)

namespace Strata

private def cstToAST (p : Program) : Core.Program :=
  (TransM.run Inhabited.default (translateProgram p)).fst

private def userFuncPgm : Program :=
#strata
program Core;

function f(x : int, y : int) : int {
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
private abbrev visibleFactory : Lambda.Factory Core.CoreLParams :=
  userFuncAST.factoryBeforeProcedure "Compute"

private abbrev xId : Core.Expression.Ident := ⟨"x", ()⟩
private abbrev yId : Core.Expression.Ident := ⟨"y", ()⟩
private abbrev zId : Core.Expression.Ident := ⟨"z", ()⟩
private abbrev intTy : Option Lambda.LMonoTy := some .int

private def fBody : Core.Expression.Expr :=
  Lambda.LExpr.mkApp () Core.intMulOp [
    Lambda.LExpr.mkApp () Core.intAddOp [.fvar () xId intTy, .fvar () yId intTy],
    Lambda.LExpr.mkApp () Core.intSubOp [.fvar () xId intTy, .fvar () yId intTy]]

/-- The translated declaration of `f` has two integer parameters and the
    arithmetic body. -/
private theorem fDef_shape : fDef = {
    name := ⟨"f", ()⟩
    inputs := [(xId, .int), (yId, .int)]
    output := .int
    body := some fBody } := by
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

/-- The integer `k` as a value of the runtime factory `F`. -/
private abbrev intV (F : Core.Expression.Factory) (k : Int) : Core.Expression.Val :=
  Lambda.SemValue.ofInt F.model.tcInterp k

/-- `f`'s operator expression is the `f` operator at `int → int → int`. -/
private theorem fDef_opExpr :
    fDef.opExpr = .op () ⟨"f", ()⟩ (some (.arrow .int (.arrow .int .int))) := by
  native_decide

/-- The arithmetic body `(x + y) * (x - y)` denotes that expression when `x = a` and
    `y = b`, in a model where the Core integer operators retain their entries. -/
private theorem denote_fBody {factory : Lambda.Factory Core.CoreLParams}
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

/-- In every model of `visibleFactory`, the interpretation of `f` applied to `a` and `b`
    is `(a + b) * (a - b)`: a consistent model interprets a function with a body as its
    body. -/
private theorem f_opInterp (model : Lambda.Interp visibleFactory) (a b : Int) :
    (model.opInterp "f" (Lambda.LSort.mkArrow .int [.int, .int]) a b : Int) =
      (a + b) * (a - b) := by
  have hmem : "f" ∈ visibleFactory :=
    CoreHoareTestSupport.factory_mem_of_get? visibleFactory_f
  have hget : visibleFactory["f"]'hmem = fDef.toLFunc :=
    CoreHoareTestSupport.factory_get_of_get? visibleFactory_f
  have hbody : (visibleFactory["f"]'hmem).body = some fBody := by
    rw [hget, fDef_shape]
    rfl
  have hconsistent := model.interpConsistent.1 "f" hmem fBody hbody
  have hconsistent' : Lambda.LFunc.InterpConsistentBody
      model.tcInterp model.opInterp fDef.toLFunc fBody := by
    rw [← hget]
    exact hconsistent
  rw [fDef_shape] at hconsistent'
  simp only [Lambda.LFuncDefined.toLFunc] at hconsistent'
  have hbodyTy : Lambda.LExpr.HasTypeA (T := Core.CoreLParams) [] fBody .int :=
    Lambda.LExpr.typeCheck_to_HasTypeA (by native_decide)
  have fv : Lambda.FreeVarVal Core.CoreLParams model.tcInterp := fun _ s =>
    @default _ (@Lambda.SortDenote.instInhabited model.tcInterp model.allInhabited s)
  let vt : Lambda.TyVarVal := fun _ => .int
  let argVal := CoreHoareTestSupport.withTwoIntArgs fv xId yId a b
  have heq := hconsistent' vt fv hbodyTy (.cons a (.cons b .nil))
  change (model.opInterp "f" (Lambda.LSort.mkArrow .int [.int, .int]) a b : Int) =
    Lambda.LExpr.denote model.tcInterp model.opInterp argVal vt .nil fBody .int hbodyTy at heq
  have hfx : argVal xId Lambda.LSort.int = a :=
    CoreHoareTestSupport.withTwoIntArgs_left fv xId yId a b
  have hfy : argVal yId Lambda.LSort.int = b :=
    CoreHoareTestSupport.withTwoIntArgs_right fv xId yId a b (by decide)
  exact heq.trans (denote_fBody model visibleFactory_intAdd visibleFactory_intSub
    visibleFactory_intMul argVal vt a b hfx hfy hbodyTy)

/-- If `x` and `y` contain `a` and `b`, evaluating `f(x, y)` yields
    `(a + b) * (a - b)` on every runtime factory over `visibleFactory`. -/
private theorem bodyExpr_eval (F : Core.Expression.Factory) (hF : F.factory = visibleFactory)
    (σ : Core.CoreStore) (a b : Int)
    (hx : σ xId = some (intV F a)) (hy : σ yId = some (intV F b)) :
    Core.Expression.eval F σ bodyExpr = some (intV F ((a + b) * (a - b))) := by
  obtain ⟨Fl, model, tv⟩ := F
  obtain rfl : Fl = visibleFactory := hF
  rw [bodyExpr_shape, fDef_opExpr]
  have h := Lambda.LExpr.denoteEval_app2_op_int (T := Core.CoreLParams)
    (M := ⟨visibleFactory, model, tv⟩) (m := ()) (m' := ()) (m'' := ()) (o := ⟨"f", ()⟩)
    (c := .int) rfl (Core.eval_fvar_int (m := ()) (ty := intTy) _ hx)
    (Core.eval_fvar_int (m := ()) (ty := intTy) _ hy)
  refine h.trans (congrArg some ?_)
  unfold intV Lambda.SemValue.ofInt
  congr 1
  exact f_opInterp model a b


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

/-- A precondition `int.gt(x, y)` that holds evaluates, so the values of `x` and `y`
    belong to the runtime factory. -/
private theorem tc_of_reqXY (factory : Lambda.Factory Core.CoreLParams)
    (ρ : Imperative.Env Core.Expression) (label : Core.CoreLabel)
    (check : Core.Procedure.Check) {vx vy : Core.Expression.Val}
    (hfac : ρ.factory.factory = factory)
    (hx : ρ.store xId = some vx) (hy : ρ.store yId = some vy)
    (hexpr : check.expr = reqXY)
    (hcheck : Core.Logic.Hoare.Procedure.checkAsPredicate factory ρ label check) :
    vx.tc = ρ.factory.model.tcInterp ∧ vy.tc = ρ.factory.model.tcInterp := by
  rcases hcheck (CoreHoareTestSupport.someValuation _) with ⟨_, hex⟩ | ⟨hne, _⟩
  · change Core.Expression.eval ρ.factory ρ.store check.expr =
      some (Imperative.HasBool.ttVal ρ.factory) at hex
    rw [hexpr] at hex
    have hd := Lambda.LExpr.denoteEval_defines hex
    obtain ⟨wx, hwx, htx⟩ := hd xId
      (by simp [reqXY, xExpr, yExpr, gtOp, Lambda.LExpr.LExpr.getVars,
        Core.intGtOp, Lambda.WFLFunc.opExpr, Lambda.LFunc.opExpr, Lambda.LFuncDefined.opExpr])
    obtain ⟨wy, hwy, hty⟩ := hd yId
      (by simp [reqXY, xExpr, yExpr, gtOp, Lambda.LExpr.LExpr.getVars,
        Core.intGtOp, Lambda.WFLFunc.opExpr, Lambda.LFunc.opExpr, Lambda.LFuncDefined.opExpr])
    rw [hx] at hwx
    rw [hy] at hwy
    cases hwx
    cases hwy
    exact ⟨htx, hty⟩
  · exact absurd hfac hne

/-- If `Compute`'s `x > y` precondition holds with `x = a` and `y = b`,
    then `a > b`. -/
private theorem check_reqXY_implies (factory : Lambda.Factory Core.CoreLParams)
    (hgtLookup : factory["Int.Gt"]? =
      some (Lambda.intGtFunc (T := Core.CoreLParams)).func)
    (ρ : Imperative.Env Core.Expression) (label : Core.CoreLabel)
    (check : Core.Procedure.Check) (a b : Int)
    (hfac : ρ.factory.factory = factory)
    (hx : ρ.store xId = some (intV ρ.factory a))
    (hy : ρ.store yId = some (intV ρ.factory b))
    (hexpr : check.expr = reqXY)
    (hcheck : Core.Logic.Hoare.Procedure.checkAsPredicate factory ρ label check) : a > b := by
  rcases hcheck (CoreHoareTestSupport.someValuation _) with ⟨_, hex⟩ | ⟨hne, _⟩
  · change Core.Expression.eval ρ.factory ρ.store check.expr =
      some (Imperative.HasBool.ttVal ρ.factory) at hex
    rw [hexpr] at hex
    have hgt : Core.Expression.eval ρ.factory ρ.store reqXY =
        some (Lambda.SemValue.ofBool ρ.factory.model.tcInterp (decide (a > b))) :=
      Core.eval_intGt (by rw [hfac]; exact hgtLookup) (Core.eval_fvar_int (ty := intTy) _ hx)
        (Core.eval_fvar_int (ty := intTy) _ hy)
    exact of_decide_eq_true
      (Lambda.SemValue.ofBool_injective (Option.some.inj (hgt.symm.trans hex)))
  · exact absurd hfac hne

/-- If `Compute`'s `x + y > 0` precondition holds with `x = a` and
    `y = b`, then `a + b > 0`. -/
private theorem check_reqSum_implies (factory : Lambda.Factory Core.CoreLParams)
    (haddLookup : factory["Int.Add"]? =
      some (Lambda.intAddFunc (T := Core.CoreLParams)).func)
    (hgtLookup : factory["Int.Gt"]? =
      some (Lambda.intGtFunc (T := Core.CoreLParams)).func)
    (ρ : Imperative.Env Core.Expression) (label : Core.CoreLabel)
    (check : Core.Procedure.Check) (a b : Int)
    (hfac : ρ.factory.factory = factory)
    (hx : ρ.store xId = some (intV ρ.factory a))
    (hy : ρ.store yId = some (intV ρ.factory b))
    (hexpr : check.expr = reqSum)
    (hcheck : Core.Logic.Hoare.Procedure.checkAsPredicate factory ρ label check) :
    a + b > 0 := by
  rcases hcheck (CoreHoareTestSupport.someValuation _) with ⟨_, hex⟩ | ⟨hne, _⟩
  · change Core.Expression.eval ρ.factory ρ.store check.expr =
      some (Imperative.HasBool.ttVal ρ.factory) at hex
    rw [hexpr] at hex
    have hgt : Core.Expression.eval ρ.factory ρ.store reqSum =
        some (Lambda.SemValue.ofBool ρ.factory.model.tcInterp (decide (a + b > 0))) :=
      Core.eval_intGt (by rw [hfac]; exact hgtLookup)
        (Core.eval_intAdd (by rw [hfac]; exact haddLookup)
          (Core.eval_fvar_int (m := ()) (ty := intTy) _ hx)
    (Core.eval_fvar_int (m := ()) (ty := intTy) _ hy))
        (Core.eval_const _ _ (.intConst 0))
    exact of_decide_eq_true
      (Lambda.SemValue.ofBool_injective (Option.some.inj (hgt.symm.trans hex)))
  · exact absurd hfac hne

/-- If `z` contains a positive integer, `Compute`'s semantic postcondition
    holds in every world. -/
private theorem post_holds (factory : Lambda.Factory Core.CoreLParams)
    (hgtLookup : factory["Int.Gt"]? =
      some (Lambda.intGtFunc (T := Core.CoreLParams)).func)
    (ρ : Imperative.Env Core.Expression) (r : Int)
    (hfac : ρ.factory.factory = factory)
    (hz : ρ.store zId = some (intV ρ.factory r))
    (hr : r > 0) :
    Core.Logic.Hoare.Procedure.contractPost factory computeProc ρ := by
  intro label check hmem hattr world
  have hexpr := ensures_shape label check hmem hattr
  refine .inl ⟨hfac, ?_⟩
  show Core.Expression.eval ρ.factory ρ.store check.expr =
    some (Imperative.HasBool.ttVal ρ.factory)
  rw [hexpr]
  have hgt : Core.Expression.eval ρ.factory ρ.store ensZ =
      some (Lambda.SemValue.ofBool ρ.factory.model.tcInterp (decide (r > 0))) :=
    Core.eval_intGt (by rw [hfac]; exact hgtLookup) (Core.eval_fvar_int (ty := intTy) _ hz)
      (Core.eval_const _ _ (.intConst 0))
  rw [hgt, decide_eq_true hr]
  rfl

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
  · intro ρ₀ σ' emitted hpre _hwf hstep
    obtain ⟨hchecks, hfac, _hold, htyped⟩ := hpre
    obtain ⟨vx, hx, hvx⟩ := htyped xId .int (by native_decide)
    obtain ⟨vy, hy, hvy⟩ := htyped yId .int (by native_decide)
    obtain ⟨a, hva⟩ := Lambda.SemValue.exists_ofInt hvx
    obtain ⟨b, hvb⟩ := Lambda.SemValue.exists_ofInt hvy
    obtain ⟨labelXY, checkXY, hmemXY, hexprXY⟩ := reqXY_mem
    obtain ⟨labelSum, checkSum, hmemSum, hexprSum⟩ := reqSum_mem
    obtain ⟨htx, hty⟩ := tc_of_reqXY _ ρ₀ labelXY checkXY hfac hx hy hexprXY
      (hchecks labelXY checkXY hmemXY)
    rw [hva, htx] at hx
    rw [hvb, hty] at hy
    have hxy : a > b := check_reqXY_implies _ visibleFactory_intGt ρ₀ labelXY checkXY a b
      hfac hx hy hexprXY (hchecks labelXY checkXY hmemXY)
    have hsum : a + b > 0 := check_reqSum_implies _ visibleFactory_intAdd visibleFactory_intGt
      ρ₀ labelSum checkSum a b hfac hx hy hexprSum (hchecks labelSum checkSum hmemSum)
    have hpos := result_positive a b hxy hsum
    dsimp [command] at hstep
    cases hstep with
    | cmd_sem hcmd =>
      cases hcmd with
      | eval_set heval hupdate _ _ =>
        have hbody := bodyExpr_eval ρ₀.factory hfac ρ₀.store a b hx hy
        have hv : _ = intV ρ₀.factory ((a + b) * (a - b)) :=
          Option.some.inj (heval.symm.trans hbody)
        cases hupdate with
        | update _ hnew _ =>
          rw [hv] at hnew
          exact ⟨True.intro, fun _ =>
            post_holds _ visibleFactory_intGt { ρ₀ with store := σ' } ((a + b) * (a - b))
              hfac hnew hpos⟩
  · exact Imperative.Logic.Hoare.postWF_of_definedVars_nil _ (by
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
private abbrev specFactory : Lambda.Factory Core.CoreLParams :=
  specOnlyAST.factoryBeforeProcedure "CheckProduct"

/-- The specification-only function has the same arithmetic body as `f`. -/
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

/-- Applying `fSpec` to integers evaluates to `(a + b) * (a - b)` without requiring the
    function to be inline: every model interprets it as its body. -/
private theorem fSpecCall_eval (F : Core.Expression.Factory) (hF : F.factory = specFactory)
    (σ : Core.CoreStore) (a b : Int)
    (hx : σ xId = some (intV F a)) (hy : σ yId = some (intV F b)) :
    Core.Expression.eval F σ fSpecCall = some (intV F ((a + b) * (a - b))) := by
  obtain ⟨Fl, model, tv⟩ := F
  obtain rfl : Fl = specFactory := hF
  have h := Lambda.LExpr.denoteEval_app2_op_int (T := Core.CoreLParams)
    (M := ⟨specFactory, model, tv⟩) (m := ()) (m' := ()) (m'' := ()) (o := ⟨"fSpec", ()⟩)
    (c := .int) rfl (Core.eval_fvar_int (m := ()) (ty := intTy) _ hx)
    (Core.eval_fvar_int (m := ()) (ty := intTy) _ hy)
  refine h.trans (congrArg some ?_)
  unfold intV Lambda.SemValue.ofInt
  congr 1
  exact fSpec_opInterp model
    (fun _ s => @default _ (@Lambda.SortDenote.instInhabited model.tcInterp model.allInhabited s))
    (fun _ => .int) a b

/-- If `x = a`, `y = b`, and their product expression is positive, then
    `CheckProduct`'s semantic postcondition holds. -/
private theorem specPost_holds (ρ : Imperative.Env Core.Expression) (a b : Int)
    (hfac : ρ.factory.factory = specFactory)
    (hx : ρ.store xId = some (intV ρ.factory a))
    (hy : ρ.store yId = some (intV ρ.factory b))
    (hpos : (a + b) * (a - b) > 0) :
    Core.Logic.Hoare.Procedure.contractPost specFactory checkProductProc ρ := by
  intro label check hmem hattr world
  have hexpr := specEnsures_shape label check hmem hattr
  refine .inl ⟨hfac, ?_⟩
  show Core.Expression.eval ρ.factory ρ.store check.expr =
    some (Imperative.HasBool.ttVal ρ.factory)
  rw [hexpr]
  have hgt : Core.Expression.eval ρ.factory ρ.store specEns =
      some (Lambda.SemValue.ofBool ρ.factory.model.tcInterp (decide ((a + b) * (a - b) > 0))) :=
    Core.eval_intGt (by rw [hfac]; exact specFactory_intGt)
      (fSpecCall_eval ρ.factory hfac ρ.store a b hx hy) (Core.eval_const _ _ (.intConst 0))
  rw [hgt, decide_eq_true hpos]
  rfl

/-- `CheckProduct` meets its contract although `fSpec` is not inline, because
    Core's evaluator is denotational: every model interprets `fSpec` as its body. -/
theorem checkProduct_meets_contract :
    Core.Logic.Hoare.Procedure.contractTriple specOnlyAST testParams "CheckProduct" := by
  refine Core.Logic.Hoare.Procedure.contractTriple_of_core_typed
    specOnlyAST testParams "CheckProduct" checkProductProc []
      (by native_decide) checkProduct_body (by native_decide) ?_
  refine Strata.Logic.Hoare.consequence
    (Core.Logic.EventLang.coreBlock specOnlyAST.findProcByString?) testParams
    (Core.Logic.Hoare.skip (factory := specFactory) specOnlyAST.findProcByString?
      testParams "" #[]
      (Core.Logic.Hoare.Procedure.contractPre specFactory checkProductProc))
    (fun _ hpre => hpre) (fun ρ hpre => ?_)
  obtain ⟨hchecks, hfac, _hold, htyped⟩ := hpre
  obtain ⟨vx, hx, hvx⟩ := htyped xId .int (by native_decide)
  obtain ⟨vy, hy, hvy⟩ := htyped yId .int (by native_decide)
  obtain ⟨a, hva⟩ := Lambda.SemValue.exists_ofInt hvx
  obtain ⟨b, hvb⟩ := Lambda.SemValue.exists_ofInt hvy
  obtain ⟨labelXY, checkXY, hmemXY, hexprXY⟩ := specReqXY_mem
  obtain ⟨labelSum, checkSum, hmemSum, hexprSum⟩ := specReqSum_mem
  obtain ⟨htx, hty⟩ := tc_of_reqXY _ ρ labelXY checkXY hfac hx hy hexprXY
    (hchecks labelXY checkXY hmemXY)
  rw [hva, htx] at hx
  rw [hvb, hty] at hy
  have hxy : a > b := check_reqXY_implies _ specFactory_intGt
    ρ labelXY checkXY a b hfac hx hy hexprXY
    (hchecks labelXY checkXY hmemXY)
  have hsum : a + b > 0 := check_reqSum_implies _ specFactory_intAdd
    specFactory_intGt ρ labelSum checkSum a b hfac hx hy hexprSum
    (hchecks labelSum checkSum hmemSum)
  exact specPost_holds ρ a b hfac hx hy (result_positive a b hxy hsum)

/-- `fSpec` is deliberately not inline. -/
example : fSpecDef.toLFunc.attr.contains .inline = false := by
  native_decide

/-- `CheckProduct` has no output parameters and no executable statements. -/
example : checkProductProc.header.outputs.isEmpty ∧
    checkProductProc.body = .structured [] := by
  native_decide

end Strata
