/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Languages.Core.Tests.Logic.HoareUtils
import Strata.Transform.SimplifyCorrect
import Strata.Languages.Core.FactoryEvalSoundWF

open Imperative
open StrataDDM (Program)

namespace Strata.HoareAfterSimplifyTest

open HoareUtils

/-- The program. -/
private def simpPgm : Program :=
#strata
program Core;

procedure Test(a : int, out m : int)
spec {
  ensures int.lt(a, m);
}
{
  var k : int := int.add(1, 2);
  var d : int := int.add(a, 1);
  m := int.add(d, k);
};

procedure TestIte(a : int, out m : int)
spec {
  ensures int.lt(a, m);
}
{
  var k : int := int.add(1, 2);
  if (int.lt(0, k)) {
    m := int.add(a, k);
  } else {
    m := a;
  }
};
#end

private def simpPgmAST : Core.Program := cstToAST simpPgm

private abbrev π : String → Option Core.Procedure := simpPgmAST.findProcByString?

/-! # Contracts proved on simplified bodies

Simplify rewrites the bodies of both procedures and drops the definition of `k`, whose value
`3` it puts into every use:

* `Test` becomes `var d : int := int.add(a, 1); m := int.add(d, 3);`.
* `TestIte` becomes `if (true) { m := int.add(a, 3); } else { m := a; }`: the guard
  `int.lt(0, k)` folds to `true`, and the branch stays.  The `else` arm would break the
  contract if it ran; in the simplified body the folded guard shows it never does.

Each triple is proved on the simplified body with the Hoare rules and carried back to the
original body by `Core.Simplify.checkedBody_triple`: the postcondition reads only `a`
and `m`, which are live (`EnvAgreeOnLive`).  The block rule then wraps the body in the
procedure block, whose exit drops the locals.  The program declares no function, so the
factory visible to the procedures is `Core.Factory`, which meets the conditions of evaluator
soundness the Simplify theorem asks (`Core.factory_evalSoundWF`).

The translated bodies are spelled out as closed terms, with the statement metadata (source
locations) read off the translated program.  The facts that bind the translated
procedures to them, Simplify's output on them, and the procedure lookup and
`contractChecksTyped` premises of the contracts use `native_decide`: the translation is
`partial`, and the kernel cannot run Simplify's folding.

Key theorems: `test_meets_contract`, `testIte_meets_contract`.
-/

private def aId : Core.Expression.Ident := ⟨"a", ()⟩
private def mId : Core.Expression.Ident := ⟨"m", ()⟩
private def kId : Core.Expression.Ident := ⟨"k", ()⟩
private def dId : Core.Expression.Ident := ⟨"d", ()⟩

/-- An integer constant. -/
private abbrev cI (n : Int) : Core.Expression.Expr := .intConst Core.valueLoc n

/-- `int.add(x, y)`. -/
private abbrev addE (x y : Core.Expression.Expr) : Core.Expression.Expr :=
  .app Core.valueLoc (.app Core.valueLoc Core.intAddOp x) y

/-- `int.lt(x, y)`. -/
private abbrev ltE (x y : Core.Expression.Expr) : Core.Expression.Expr :=
  .app Core.valueLoc (.app Core.valueLoc Core.intLtOp x) y

/-- The context Simplify folds the bodies from: `Core.Factory`, recording nothing. -/
private abbrev base : Core.Simplify.Ctx := Core.Simplify.Ctx.ofFactory Core.Factory []

/-! ## The bodies and what Simplify makes of them -/

private def testProc : Core.Procedure := (π "Test").get!
private def testIteProc : Core.Procedure := (π "TestIte").get!

/-- The metadata of a statement. -/
private def stmtMd : Core.Statement → MetaData Core.Expression
  | .cmd (.cmd c) => c.getMetaData
  | .cmd (.call _ _ _ md) | .block _ _ md | .ite _ _ _ md | .loop _ _ _ _ md | .exit _ md
  | .typeDecl _ md => md

/-- The metadata of the statement at position `i` of `ss`. -/
private def mdAt (ss : Core.Statements) (i : Nat) : MetaData Core.Expression :=
  ((ss[i]?).map stmtMd).getD #[]

/-- The arms of a conditional, and nothing for another statement. -/
private def armsOf : Core.Statement → Core.Statements × Core.Statements
  | .ite _ ts es _ => (ts, es)
  | _ => ([], [])

/-- The translated statements of `Test`. -/
private def testSrc : Core.Statements := bodyOf simpPgmAST "Test"

/-- The translated statements of `TestIte`. -/
private def testIteSrc : Core.Statements := bodyOf simpPgmAST "TestIte"

/-- The translated body of `Test`. -/
private abbrev testBody : Core.Statements :=
  [Core.Statement.init kId intLTy (.det (addE (cI 1) (cI 2))) (mdAt testSrc 0),
   Core.Statement.init dId intLTy (.det (addE (v aId) (cI 1))) (mdAt testSrc 1),
   Core.Statement.set mId (addE (v dId) (v kId)) (mdAt testSrc 2)]

/-- The simplified body of `Test`. -/
private abbrev testOut : Core.Statements :=
  [Core.Statement.init dId intLTy (.det (addE (v aId) (cI 1))) (mdAt testSrc 1),
   Core.Statement.set mId (addE (v dId) (cI 3)) (mdAt testSrc 2)]

/-- The `then` arm of `TestIte`'s branch, before and after Simplify. -/
private abbrev thenArm (rhs : Core.Expression.Expr) : Core.Statements :=
  [Core.Statement.set mId (addE (v aId) rhs) (mdAt (armsOf ((testIteSrc[1]?).getD default)).1 0)]

/-- The `else` arm of `TestIte`'s branch. -/
private abbrev elseArm : Core.Statements :=
  [Core.Statement.set mId (v aId) (mdAt (armsOf ((testIteSrc[1]?).getD default)).2 0)]

/-- The translated body of `TestIte`. -/
private abbrev testIteBody : Core.Statements :=
  [Core.Statement.init kId intLTy (.det (addE (cI 1) (cI 2))) (mdAt testIteSrc 0),
   .ite (.det (ltE (cI 0) (v kId))) (thenArm (v kId)) elseArm (mdAt testIteSrc 1)]

/-- The simplified body of `TestIte`: the guard is folded to `true`. -/
private abbrev testIteOut : Core.Statements :=
  [.ite (.det (.boolConst Core.valueLoc true)) (thenArm (cI 3)) elseArm (mdAt testIteSrc 1)]

/-- The translated body of `Test` really is `testBody`. -/
private theorem test_body_eq : testProc.body = .structured testBody false := by native_decide

/-- The translated body of `TestIte` really is `testIteBody`. -/
private theorem testIte_body_eq : testIteProc.body = .structured testIteBody false := by
  native_decide

/-- **Simplify installs `testOut`.** -/
private theorem test_simp :
    Core.Simplify.checkedBody base testProc testBody = testOut := by
  native_decide

/-- **Simplify installs `testIteOut`.** -/
private theorem testIte_simp :
    Core.Simplify.checkedBody base testIteProc testIteBody = testIteOut := by
  native_decide

/-! ## The precondition of the Simplify theorem -/

/-- The entry typing: the entry variables `a` and `m` are integers. -/
private def Γ : VarTyping Core.Expression :=
  fun x => if x = aId ∨ x = mId then some intLTy else none

/-- The typing after the declaration of `k`. -/
private abbrev Γk : VarTyping Core.Expression := Γ.extend [(kId, intLTy)]

/-- `Core.Factory` resolves `Int.Add` at its annotation with the empty substitution. -/
private theorem intAddOp_consistent : Lambda.OpsConsistent Core.Factory Core.intAddOp :=
  .op_in (tySubst := Lambda.Subst.empty) Core.coreFactory_intAdd
    (by simp [Lambda.LFunc.opTypeSubst, Lambda.intAddFunc, Lambda.binaryOp])
    (by simp [Lambda.intAddFunc, Lambda.binaryOp, Lambda.LMonoTy.mkArrow',
      Lambda.LMonoTy.subst_unfold, Lambda.Subst.empty]; rfl)

/-- `Core.Factory` resolves `Int.Lt` at its annotation with the empty substitution. -/
private theorem intLtOp_consistent : Lambda.OpsConsistent Core.Factory Core.intLtOp :=
  .op_in (tySubst := Lambda.Subst.empty) Core.coreFactory_intLt
    (by simp [Lambda.LFunc.opTypeSubst, Lambda.intLtFunc, Lambda.binaryOp])
    (by simp [Lambda.intLtFunc, Lambda.binaryOp, Lambda.LMonoTy.mkArrow',
      Lambda.LMonoTy.subst_unfold, Lambda.Subst.empty]; rfl)

/-- `int.add(1, 2)` is a well-typed `int` under `Γ`. -/
private theorem k_ok : Core.Simplify.ExprOK Core.Factory Γ (addE (cI 1) (cI 2)) intLTy :=
  ⟨⟨_, rfl, by decide, by decide, Lambda.LExpr.typeCheck_to_HasTypeA (by native_decide)⟩,
    .app (.app intAddOp_consistent .const) .const, by native_decide⟩

/-- **The body of `Test` meets the precondition of the Simplify theorem.** -/
private theorem test_wf : Core.Simplify.BodyWF Core.Factory Γ testBody := by
  refine ⟨⟨by native_decide, by native_decide⟩, ?_⟩
  have hd : Core.Simplify.ExprOK Core.Factory Γk (addE (v aId) (cI 1)) intLTy :=
    ⟨⟨_, rfl, by decide, by decide, Lambda.LExpr.typeCheck_to_HasTypeA (by native_decide)⟩,
      .app (.app intAddOp_consistent .fvar) .const, by native_decide⟩
  have hm : Core.Simplify.ExprOK Core.Factory (Γk.extend [(dId, intLTy)])
      (addE (v dId) (v kId)) intLTy :=
    ⟨⟨_, rfl, by decide, by decide, Lambda.LExpr.typeCheck_to_HasTypeA (by native_decide)⟩,
      .app (.app intAddOp_consistent .fvar) .fvar, by native_decide⟩
  simp only [Core.Simplify.Block.exprsOKIn, Core.Simplify.Stmt.exprsOKIn,
    Stmt.typedDefinedVars, HasTypedVarsImp.typedDefinedVars, CmdExt.typedDefinedVars,
    Cmd.typedDefinedVars, and_true]
  exact ⟨k_ok, hd, ⟨intLTy, by decide, hm⟩⟩

/-- **The body of `TestIte` meets the precondition of the Simplify theorem.** -/
private theorem testIte_wf : Core.Simplify.BodyWF Core.Factory Γ testIteBody := by
  refine ⟨⟨by native_decide, by native_decide⟩, ?_⟩
  have hg : Core.Simplify.ExprOK Core.Factory Γk (ltE (cI 0) (v kId))
      (HasBool.boolTy (P := Core.Expression)) :=
    ⟨⟨_, rfl, by decide, by decide, Lambda.LExpr.typeCheck_to_HasTypeA (by native_decide)⟩,
      .app (.app intLtOp_consistent .const) .fvar, by native_decide⟩
  have ht : Core.Simplify.ExprOK Core.Factory Γk (addE (v aId) (v kId)) intLTy :=
    ⟨⟨_, rfl, by decide, by decide, Lambda.LExpr.typeCheck_to_HasTypeA (by native_decide)⟩,
      .app (.app intAddOp_consistent .fvar) .fvar, by native_decide⟩
  have he : Core.Simplify.ExprOK Core.Factory Γk (v aId) intLTy :=
    ⟨⟨_, rfl, by decide, by decide, Lambda.LExpr.typeCheck_to_HasTypeA (by native_decide)⟩,
      .fvar, by native_decide⟩
  simp only [Core.Simplify.Block.exprsOKIn, Core.Simplify.Stmt.exprsOKIn,
    Stmt.typedDefinedVars, HasTypedVarsImp.typedDefinedVars, CmdExt.typedDefinedVars,
    Cmd.typedDefinedVars, and_true]
  exact ⟨k_ok, hg, ⟨intLTy, by decide, ht⟩, ⟨intLTy, by decide, he⟩⟩

/-! ## Evaluating the expressions -/

/-- `x` holds the integer `n`. -/
private abbrev Holds (x : Core.Expression.Ident) (n : Int) (ρ : Env Core.Expression) : Prop :=
  ρ.store x = some (intOf ρ.factory n)

/-- `int.add(x, y)` of two integers evaluates to their sum. -/
private theorem add_eval {f : Core.Expression.Factory} (hf : f.factory = Core.Factory)
    {σ : Core.CoreStore} {x y : Core.Expression.Expr} {p q : Int}
    (hx : Core.Expression.eval f σ x = some (intOf f p))
    (hy : Core.Expression.eval f σ y = some (intOf f q)) :
    Core.Expression.eval f σ (addE x y) = some (intOf f (p + q)) :=
  Core.eval_intAdd (hf ▸ Core.coreFactory_intAdd) hx hy

/-- With `x ↦ p` and `y ↦ q`, `int.lt(x, y)` evaluates to `p < q`. -/
private theorem lt_eval {f : Core.Expression.Factory} (hf : f.factory = Core.Factory)
    {σ : Core.CoreStore} {x y : Core.Expression.Ident} {p q : Int}
    (hx : σ x = some (intOf f p)) (hy : σ y = some (intOf f q)) :
    Core.Expression.eval f σ (ltE (v x) (v y)) =
      some (Lambda.SemValue.ofBool f.model.tcInterp (decide (p < q))) :=
  Core.eval_intLt (hf ▸ Core.coreFactory_intLt) (Core.eval_fvar_int f hx)
    (Core.eval_fvar_int f hy)

/-! ## The triples of the simplified bodies -/

/-- Before a body: `a` and `m` hold integers. -/
private abbrev Entry (ρ : Env Core.Expression) : Prop :=
  Pinned ρ ∧ ∃ p q, Holds aId p ρ ∧ Holds mId q ρ

/-- After a body: `m` holds an integer greater than `a`'s. -/
private abbrev Exit (ρ : Env Core.Expression) : Prop :=
  Pinned ρ ∧ ∃ p r, Holds aId p ρ ∧ Holds mId r ρ ∧ p < r

/-- The variables `d` and `a` are distinct, so writing one keeps the other. -/
private theorem d_ne_a : dId ≠ aId := by decide
/-- The variables `d` and `m` are distinct, so writing one keeps the other. -/
private theorem d_ne_m : dId ≠ mId := by decide
/-- The variables `m` and `a` are distinct, so writing one keeps the other. -/
private theorem m_ne_a : mId ≠ aId := by decide

/-- `m := int.add(x, n)`, with `x` holding `p + j`, establishes `Exit` when `0 < j + n`. -/
private theorem set_m_triple {P : Env Core.Expression → Prop} (x : Core.Expression.Ident)
    (n j : Int) (md : MetaData Core.Expression) (hpos : 0 < j + n)
    (hP : ∀ ρ, P ρ → Pinned ρ ∧ ∃ p, Holds aId p ρ ∧ Holds x (p + j) ρ) :
    Core.Logic.Hoare.Triple π testParams P [Core.Statement.set mId (addE (v x) (cI n)) md]
      Exit := by
  refine Core.Logic.Hoare.set π testParams _ _ _ _ _ (fun ρ₀ σ' w h hev hup => ?_)
  obtain ⟨hp, p, ha, hx⟩ := hP ρ₀ h
  rw [add_eval hp (Core.eval_fvar_int _ hx) (Core.eval_intConst _ _ n)] at hev
  cases hev
  cases hup with
  | update _ hnew hoth =>
    exact ⟨hp, p, p + j + n, (hoth _ m_ne_a).trans ha, hnew, by omega⟩

/-- **The simplified body of `Test` establishes `Exit`.** -/
private theorem testOut_triple : Core.Logic.Hoare.Triple π testParams Entry testOut Exit := by
  refine Core.Logic.Hoare.seq π testParams (ss₁ := [testOut[0]])
    (Mid := fun ρ => Pinned ρ ∧ ∃ p, Holds aId p ρ ∧ Holds dId (p + 1) ρ)
    ?_ (set_m_triple dId 3 1 _ (by omega) fun _ h => h) (by covered)
  -- `d := int.add(a, 1)`.
  refine Core.Logic.Hoare.init π testParams _ _ _ _ _ _
    (fun ρ₀ σ' w ⟨hp, p, q, ha, hm⟩ hev hinit => ?_)
  rw [add_eval hp (Core.eval_fvar_int _ ha) (Core.eval_intConst _ _ 1)] at hev
  cases hev
  cases hinit with
  | init _ hnew hoth => exact ⟨hp, p, (hoth _ d_ne_a).trans ha, hnew⟩

/-- **The simplified body of `TestIte` establishes `Exit`**: the `then` arm sets `m` to
    `a + 3`, and the `else` arm does not run, its guard being `true`. -/
private theorem testIteOut_triple :
    Core.Logic.Hoare.Triple π testParams Entry testIteOut Exit := by
  refine Core.Logic.Hoare.ite π testParams
    (set_m_triple aId 3 0 _ (by omega) fun _ ⟨⟨hp, p, _, ha, _⟩, _⟩ => ⟨hp, p, ha, by simpa⟩)
    (Core.Logic.Hoare.consequence π testParams (Core.Logic.Hoare.false_pre π testParams _ Exit)
      (fun ρ ⟨_, hg⟩ => ?_) (fun _ h => h))
    (Imperative.Logic.Hoare.postWF_of_definedVars_nil _ (by decide +kernel))
    (Imperative.Logic.Hoare.postWF_of_definedVars_nil _ (by decide +kernel))
  rw [Core.eval_boolConst] at hg
  exact Bool.noConfusion (Lambda.SemValue.ofBool_injective (Option.some.inj hg))

/-! ## Back to the bodies Simplify started from -/

/-- An entry satisfying `Entry` gives the entry variables `a` and `m` of a body their `Γ`
    types. -/
private theorem entry_typed {ss : Core.Statements}
    (hE : ∀ x ∈ Block.entryVars ss, x = aId ∨ x = mId) {ρ : Env Core.Expression}
    (h : Entry ρ) : Core.Simplify.StoreTypedBy ρ.factory Γ ss ρ.store := by
  obtain ⟨-, p, q, ha, hm⟩ := h
  intro x hx w hw
  rcases hE x hx with rfl | rfl
  · rw [ha] at hw; cases hw; exact ⟨intLTy, by decide, rfl, rfl⟩
  · rw [hm] at hw; cases hw; exact ⟨intLTy, by decide, rfl, rfl⟩

/-- `Exit` survives replacing the final environment by one that agrees with it on live names
    that include `m` and `a` and has its factory. -/
private theorem exit_of_agree {L : Std.HashSet String} (hla : L.contains "a" = true)
    (hlm : L.contains "m" = true) {ρ' ρ'' : Env Core.Expression}
    (h : Core.Simplify.EnvAgreeOnLive L ρ' ρ'') (hx : Exit ρ'') : Exit ρ' := by
  obtain ⟨hst, hf⟩ := h
  obtain ⟨hp, p, r, ha, hm, hlt⟩ := hx
  refine ⟨by rw [Pinned, ← hf]; exact hp, p, r, ?_, ?_, hlt⟩
  · rw [Holds, ← hst aId hla, ha, hf]
  · rw [Holds, ← hst mId hlm, hm, hf]

/-- **The body of `Test` establishes `Exit`**, by `Core.Simplify.checkedBody_triple`
    from `testOut_triple`. -/
private theorem test_triple : Core.Logic.Hoare.Triple π testParams Entry testBody Exit :=
  Core.Simplify.checkedBody_triple π testParams base testProc Γ
    (Core.Simplify.Ctx.ofFactory_fresh _ _) Core.factory_evalSoundWF testBody test_wf
    (fun _ h => h.1)
    (fun _ h _ => entry_typed (List.forall_of_all_decide (by native_decide)) h)
    (fun _ _ => exit_of_agree (by native_decide) (by native_decide)) (test_simp ▸ testOut_triple)

/-- **The body of `TestIte` establishes `Exit`**, by
    `Core.Simplify.checkedBody_triple` from `testIteOut_triple`. -/
private theorem testIte_triple : Core.Logic.Hoare.Triple π testParams Entry testIteBody Exit :=
  Core.Simplify.checkedBody_triple π testParams base testIteProc Γ
    (Core.Simplify.Ctx.ofFactory_fresh _ _) Core.factory_evalSoundWF testIteBody testIte_wf
    (fun _ h => h.1)
    (fun _ h _ => entry_typed (List.forall_of_all_decide (by native_decide)) h)
    (fun _ _ => exit_of_agree (by native_decide) (by native_decide))
    (testIte_simp ▸ testIteOut_triple)

/-! ## The contracts -/

/-- `Exit` survives leaving a procedure block that declares neither `a` nor `m`. -/
private theorem exit_postWF {ss : Core.Statements}
    (ha : aId ∉ Block.definedVars (P := Core.Expression) (C := Core.Command) ss true)
    (hm : mId ∉ Block.definedVars (P := Core.Expression) (C := Core.Command) ss true) :
    Imperative.Logic.Hoare.PostWF ss Exit := by
  intro ρ ⟨hp, p, r, hpa, hpm, hlt⟩
  have hdrop : ∀ x, x ∉ Block.definedVars (P := Core.Expression) (C := Core.Command) ss true →
      Imperative.dropVars
        (Block.definedVars (P := Core.Expression) (C := Core.Command) ss true) ρ.store x =
          ρ.store x := fun x hx => by simp only [Imperative.dropVars, ite_eq_right hx]
  exact ⟨hp, p, r, (hdrop aId ha).trans hpa, (hdrop mId hm).trans hpm, hlt⟩

/-- `Exit` gives the postcondition of a procedure whose postconditions are all
    `int.lt(a, m)`. -/
private theorem post_of_exit {proc : Core.Procedure}
    (hpost : ∀ lc ∈ proc.spec.postconditions.toList, lc.2.expr = ltE (v aId) (v mId))
    {ρ : Env Core.Expression} (hx : Exit ρ) :
    Core.Logic.Hoare.Procedure.contractPost Core.Factory proc ρ := by
  obtain ⟨hp, p, r, ha, hm, hlt⟩ := hx
  intro label check hmem _ _
  refine .inl ⟨hp, ?_⟩
  change Core.Expression.eval ρ.factory ρ.store check.expr = some (HasBool.ttVal ρ.factory)
  rw [hpost _ hmem, lt_eval hp ha hm, decide_eq_true hlt]
  rfl

/-- **A procedure of the program meets its contract `int.lt(a, m)`** when its body
    establishes `Exit` from `Entry`: the contract's precondition gives `Entry`, and leaving the
    procedure block keeps `Exit`, which gives the postcondition. -/
private theorem meets_contract {name : String} {proc : Core.Procedure} {ss : Core.Statements}
    (hfactory : simpPgmAST.factoryBeforeProcedure name = Core.Factory)
    (hfind : π name = some proc) (htargs : proc.header.typeArgs = [])
    (hchecks : Core.Logic.Hoare.Procedure.contractChecksTyped proc)
    (hbody : proc.body = .structured ss false)
    (ha : (aId, Lambda.LMonoTy.int) ∈ proc.header.inputs.toList)
    (hm : (mId, Lambda.LMonoTy.int) ∈ proc.header.outputs.toList)
    (hpost : ∀ lc ∈ proc.spec.postconditions.toList, lc.2.expr = ltE (v aId) (v mId))
    (hpw : Imperative.Logic.Hoare.PostWF ss Exit)
    (h : Core.Logic.Hoare.Triple π testParams Entry ss Exit) :
    Core.Logic.Hoare.Procedure.contractTriple simpPgmAST testParams name := by
  rw [Core.Logic.Hoare.Procedure.contractTriple, hfactory]
  refine ⟨proc, hfind, Core.Procedure.forall_instance_of_typeArgs_nil htargs ⟨hchecks, ?_⟩⟩
  rw [hbody]
  refine Core.Logic.Hoare.consequence π testParams
    (Core.Logic.Hoare.block π testParams ?_ hpw) (fun _ h => h.1)
    (fun _ h => post_of_exit hpost h)
  refine Core.Logic.Hoare.of_storeWF_pre π testParams
    (Core.Logic.Hoare.consequence π testParams h ?_ (fun _ h => h))
  intro ρ ⟨⟨_, hp, _, hin, hout⟩, hwf⟩
  obtain ⟨p, hpa⟩ := Core.Logic.Hoare.Procedure.inputAsPredicate_int hwf hin aId ha
  obtain ⟨q, hqm⟩ := Core.Logic.Hoare.Procedure.outputAsPredicate_int hwf hout mId hm
  exact ⟨hp, p, q, hpa, hqm⟩

/-- **`Test` meets its contract**, from the triple of the body Simplify installs. -/
theorem test_meets_contract :
    Core.Logic.Hoare.Procedure.contractTriple simpPgmAST testParams "Test" :=
  meets_contract (Core.Program.factoryBeforeProcedure_eq_core_of_noFunctions (by decide +kernel))
    (by native_decide) (by native_decide) ⟨by native_decide, by native_decide⟩
    test_body_eq (by native_decide) (by native_decide)
    (List.forall_of_all_decide (by native_decide))
    (exit_postWF (by decide +kernel) (by decide +kernel)) test_triple

/-- **`TestIte` meets its contract**, from the triple of the body Simplify installs, in which
    the folded guard rules out the `else` arm. -/
theorem testIte_meets_contract :
    Core.Logic.Hoare.Procedure.contractTriple simpPgmAST testParams "TestIte" :=
  meets_contract (Core.Program.factoryBeforeProcedure_eq_core_of_noFunctions (by decide +kernel))
    (by native_decide) (by native_decide) ⟨by native_decide, by native_decide⟩
    testIte_body_eq (by native_decide) (by native_decide)
    (List.forall_of_all_decide (by native_decide))
    (exit_postWF (by decide +kernel) (by decide +kernel)) testIte_triple

end Strata.HoareAfterSimplifyTest
