/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core
import StrataTest.Languages.Core.Tests.Logic.HoareTestSupport
import Strata.Languages.Core.Logic.HoareCall
import Strata.Languages.Core.ProcedureProps
import Strata.Languages.Core.ProgramProps
import Strata.Languages.Core.BitVecEvalProps
import Strata.Languages.Core.InstWellFormedSemanticsEval
import Strata.DL.Lambda.LExprEvalProps
import Strata.DL.Lambda.Denote.LExprDenote
import Strata.DL.Lambda.Denote.LExprDenoteProps
import StrataDDM.Integration.Lean.HashCommands
import Strata.Languages.Core.IntEvalProps

/-! # Hoare logic for Core procedure calls

These tests prove procedure contracts and call triples using
`Procedure.call_of_contract`, including copied output values and the callee body
frame. The program proves `Max16`, `Min16`, and a four-call `Run` whose local
intermediate values establish the unsigned bitvector absorption identity in its
postcondition.

Key results are `max16_meets_contract`, `min16_meets_contract`, and
`mm_run_meets_contract`.
-/

open Imperative
open StrataDDM (Program)
open Lambda.LExpr.SyntaxMono

namespace Strata

open CoreHoareTestSupport


/-- Translate a DDM concrete-syntax program to the Core AST. -/
private def cstToAST (p : Program) : Core.Program :=
  (TransM.run Inhabited.default (translateProgram p)).fst

/-- Recover the concrete procedure named by a successful program lookup. -/
private theorem procOf_eq {p : Core.Program} {nm : String} {proc : Core.Procedure}
    (h : p.findProcByString? nm = some proc) : (p.findProcByString? nm).get! = proc := by
  rw [h]
  rfl

/-- Test gate with no reserved prefixes and every function name declared. -/
private def testParams : Core.Logic.InitEnvWFParams := ⟨[], fun _ => true⟩

/-! ## Pure bitvector absorption (the fact in Run's postcondition) -/

/-- `min(max(a,b), a) = max(min(a,b), a)` for 16-bit unsigned min/max (both equal `a`),
    stated on the raw `ite`/`ule` forms produced by the evaluator. -/
private theorem bv16_minmax_absorption (a b : BitVec 16) :
    (if BitVec.ule (if BitVec.ule a b then b else a) a then (if BitVec.ule a b then b else a) else a)
  = (if BitVec.ule (if BitVec.ule a b then a else b) a then a else (if BitVec.ule a b then a else b)) := by
  by_cases hab : BitVec.ule a b
  · by_cases hba : BitVec.ule b a
    · have hab' : a.toNat ≤ b.toNat := BitVec.ule_iff_toNat_le.mp hab
      have hba' : b.toNat ≤ a.toNat := BitVec.ule_iff_toNat_le.mp hba
      have heq : a = b := BitVec.eq_of_toNat_eq (by omega)
      subst b
      simp
    · simp [hab, hba]
  · have hba : BitVec.ule b a := by
      rw [BitVec.ule_iff_toNat_le]
      have hnle : ¬a.toNat ≤ b.toNat := by
        intro hle
        exact hab (BitVec.ule_iff_toNat_le.mpr hle)
      omega
    simp [hab, hba]

/-! ## The bv16 min/max program -/

/-- Unsigned min/max using the XOR-and-mask selection trick from
https://graphics.stanford.edu/~seander/bithacks.html#IntegerMinOrMax. The
comparison is expanded to an all-ones or all-zeros 16-bit mask. -/
private def mmPgm : Program :=
#strata
program Core;

procedure Max16(x : bv W16, y : bv W16, out result : bv W16)
spec {
  ensures result == (if bv16.uLe(x, y) then y else x);
}
{
  result := bv16.xor(x, bv16.and(bv16.xor(x, y),
    if bv16.uLe(x, y) then bv{16}(65535) else bv{16}(0)));
};

procedure Min16(x : bv W16, y : bv W16, out result : bv W16)
spec {
  ensures result == (if bv16.uLe(x, y) then x else y);
}
{
  result := bv16.xor(y, bv16.and(bv16.xor(x, y),
    if bv16.uLe(x, y) then bv{16}(65535) else bv{16}(0)));
};


procedure Run(a : bv W16, b : bv W16,
    out minMaxA : bv W16, out maxMinA : bv W16)
spec {
  ensures maxMinA == minMaxA;
}
{
  var maxAB : bv W16;
  call Max16(a, b, out maxAB);
  call Min16(maxAB, a, out minMaxA);
  var minAB : bv W16;
  call Min16(a, b, out minAB);
  call Max16(minAB, a, out maxMinA);
};
#end

private def mmAST : Core.Program := cstToAST mmPgm
private def maxProc : Core.Procedure := (mmAST.findProcByString? "Max16").get!
private def minProc : Core.Procedure := (mmAST.findProcByString? "Min16").get!
private def mmRunProc : Core.Procedure := (mmAST.findProcByString? "Run").get!

private def bv16Ty : Option Lambda.LMonoTy := some (Lambda.LMonoTy.bitvec 16)
private def resultId : Core.Expression.Ident := ⟨"result", ()⟩

/-! ## Max16 body/ensures projections -/

private def maxSetExpr : Core.Expression.Expr :=
  match maxProc.body with
  | .structured [Imperative.Stmt.cmd (Imperative.CmdExt.cmd (Imperative.Cmd.set _ (.det e) _))] => e
  | _ => Lambda.LExpr.const () (Lambda.LConst.boolConst true)

private def maxSetMd : Imperative.MetaData Core.Expression :=
  match maxProc.body with
  | .structured [Imperative.Stmt.cmd (Imperative.CmdExt.cmd (Imperative.Cmd.set _ _ md))] => md
  | _ => #[]

/-- Max16's translated body is one assignment to `result`. -/
private theorem max_body_eq :
    maxProc.body = .structured [Imperative.Stmt.cmd
      (Imperative.CmdExt.cmd (Imperative.Cmd.set resultId (.det maxSetExpr) maxSetMd))] := by
  native_decide

private def maxSpecExpr : Core.Expression.Expr :=
  match (maxProc.spec.postconditions.toList.head!).2.expr with
  | .eq _ _ rhs => rhs
  | _ => Lambda.LExpr.const () (Lambda.LConst.boolConst true)

/-- Max16's non-free postcondition equates `result` with its specification expression. -/
private theorem max_ensures_shape :
    ∀ lc ∈ maxProc.spec.postconditions.toList,
      (Prod.snd lc).attr = Core.Procedure.CheckAttr.Default →
      (Prod.snd lc).expr =
        Lambda.LExpr.eq () (Lambda.LExpr.fvar () resultId bv16Ty) maxSpecExpr := by
  native_decide

/-! ## Min16 body/ensures projections -/

private def minSetExpr : Core.Expression.Expr :=
  match minProc.body with
  | .structured [Imperative.Stmt.cmd (Imperative.CmdExt.cmd (Imperative.Cmd.set _ (.det e) _))] => e
  | _ => Lambda.LExpr.const () (Lambda.LConst.boolConst true)

private def minSetMd : Imperative.MetaData Core.Expression :=
  match minProc.body with
  | .structured [Imperative.Stmt.cmd (Imperative.CmdExt.cmd (Imperative.Cmd.set _ _ md))] => md
  | _ => #[]

/-- Min16's translated body is one assignment to `result`. -/
private theorem min_body_eq :
    minProc.body = .structured [Imperative.Stmt.cmd
      (Imperative.CmdExt.cmd (Imperative.Cmd.set resultId (.det minSetExpr) minSetMd))] := by
  native_decide

private def minSpecExpr : Core.Expression.Expr :=
  match (minProc.spec.postconditions.toList.head!).2.expr with
  | .eq _ _ rhs => rhs
  | _ => Lambda.LExpr.const () (Lambda.LConst.boolConst true)

/-- Min16's non-free postcondition equates `result` with its specification expression. -/
private theorem min_ensures_shape :
    ∀ lc ∈ minProc.spec.postconditions.toList,
      (Prod.snd lc).attr = Core.Procedure.CheckAttr.Default →
      (Prod.snd lc).expr =
        Lambda.LExpr.eq () (Lambda.LExpr.fvar () resultId bv16Ty) minSpecExpr := by
  native_decide


/-! ## Run AST projections -/

private def bv16ArrowTy : Lambda.LMonoTy :=
  Lambda.LMonoTy.tcons "arrow" [Lambda.LMonoTy.bitvec 16,
    Lambda.LMonoTy.tcons "arrow" [Lambda.LMonoTy.bitvec 16, Lambda.LMonoTy.tcons "bool" []]]

private def xId : Core.Expression.Ident := ⟨"x", ()⟩
private def yId : Core.Expression.Ident := ⟨"y", ()⟩
private def aId : Core.Expression.Ident := ⟨"a", ()⟩
private def bId : Core.Expression.Ident := ⟨"b", ()⟩
private def maxABId : Core.Expression.Ident := ⟨"maxAB", ()⟩
private def minMaxAId : Core.Expression.Ident := ⟨"minMaxA", ()⟩
private def minABId : Core.Expression.Ident := ⟨"minAB", ()⟩
private def maxMinAId : Core.Expression.Ident := ⟨"maxMinA", ()⟩

private def bv16ULeApp (x y : Core.Expression.Expr) : Core.Expression.Expr :=
  .app () (.app () (Lambda.LExpr.op () ⟨"Bv16.ULe", ()⟩ (some bv16ArrowTy)) x) y

private def bv16XorApp (x y : Core.Expression.Expr) : Core.Expression.Expr :=
  .app () (.app () Core.bv16XorFunc.opExpr x) y

private def bv16AndApp (x y : Core.Expression.Expr) : Core.Expression.Expr :=
  .app () (.app () Core.bv16AndFunc.opExpr x) y

private def bitHackMaskExpr : Core.Expression.Expr :=
  Lambda.LExpr.ite ()
    (bv16ULeApp (.fvar () xId bv16Ty) (.fvar () yId bv16Ty))
    (Lambda.LExpr.bitvecConst () 16 (BitVec.ofNat 16 65535))
    (Lambda.LExpr.bitvecConst () 16 (BitVec.ofNat 16 0))

private def maxBitHackExpr : Core.Expression.Expr :=
  bv16XorApp (.fvar () xId bv16Ty)
    (bv16AndApp
      (bv16XorApp (.fvar () xId bv16Ty) (.fvar () yId bv16Ty))
      bitHackMaskExpr)

private def minBitHackExpr : Core.Expression.Expr :=
  bv16XorApp (.fvar () yId bv16Ty)
    (bv16AndApp
      (bv16XorApp (.fvar () xId bv16Ty) (.fvar () yId bv16Ty))
      bitHackMaskExpr)

private def maxABInitTy : Core.Expression.Ty :=
  match mmRunProc.body with
  | .structured (Core.Statement.init _ ty .nondet _ :: _) => ty
  | _ => default
private def maxABInitMd : Imperative.MetaData Core.Expression :=
  match mmRunProc.body with
  | .structured (Core.Statement.init _ _ .nondet md :: _) => md
  | _ => #[]
private def maxABInitStmt : Core.Statement :=
  Core.Statement.init maxABId maxABInitTy .nondet maxABInitMd

private def cArgs1 : List (Imperative.CallArg Core.Expression) :=
  match mmRunProc.body with
  | .structured (_ :: Core.Statement.call _ a _ :: _) => a
  | _ => []
private def cMd1 : Imperative.MetaData Core.Expression :=
  match mmRunProc.body with
  | .structured (_ :: Core.Statement.call _ _ m :: _) => m
  | _ => #[]
private def cArgs2 : List (Imperative.CallArg Core.Expression) :=
  match mmRunProc.body with
  | .structured (_ :: _ :: Core.Statement.call _ a _ :: _) => a
  | _ => []
private def cMd2 : Imperative.MetaData Core.Expression :=
  match mmRunProc.body with
  | .structured (_ :: _ :: Core.Statement.call _ _ m :: _) => m
  | _ => #[]
private def minABInitTy : Core.Expression.Ty :=
  match mmRunProc.body with
  | .structured (_ :: _ :: _ :: Core.Statement.init _ ty .nondet _ :: _) => ty
  | _ => default
private def minABInitMd : Imperative.MetaData Core.Expression :=
  match mmRunProc.body with
  | .structured (_ :: _ :: _ :: Core.Statement.init _ _ .nondet md :: _) => md
  | _ => #[]
private def minABInitStmt : Core.Statement :=
  Core.Statement.init minABId minABInitTy .nondet minABInitMd

private def cArgs3 : List (Imperative.CallArg Core.Expression) :=
  match mmRunProc.body with
  | .structured (_ :: _ :: _ :: _ :: Core.Statement.call _ a _ :: _) => a
  | _ => []
private def cMd3 : Imperative.MetaData Core.Expression :=
  match mmRunProc.body with
  | .structured (_ :: _ :: _ :: _ :: Core.Statement.call _ _ m :: _) => m
  | _ => #[]
private def cArgs4 : List (Imperative.CallArg Core.Expression) :=
  match mmRunProc.body with
  | .structured (_ :: _ :: _ :: _ :: _ :: Core.Statement.call _ a _ :: _) => a
  | _ => []
private def cMd4 : Imperative.MetaData Core.Expression :=
  match mmRunProc.body with
  | .structured (_ :: _ :: _ :: _ :: _ :: Core.Statement.call _ _ m :: _) => m
  | _ => #[]

/-- The translated Run body interleaves two local declarations with its four calls. -/
private theorem mm_run_body_eq :
    mmRunProc.body = .structured
      [maxABInitStmt,
       Core.Statement.call "Max16" cArgs1 cMd1,
       Core.Statement.call "Min16" cArgs2 cMd2,
       minABInitStmt,
       Core.Statement.call "Min16" cArgs3 cMd3,
       Core.Statement.call "Max16" cArgs4 cMd4] := by native_decide

/-! ### Body-frame lemmas for Max16 / Min16 -/

/-- Every execution of the Max16 body respects its output frame. -/
private theorem max_body_frame :
    ∀ proc, mmAST.findProcByString? "Max16" = some proc →
      Core.Logic.Hoare.Procedure.bodyFrame mmAST.findProcByString? proc := by
  intro proc hlookup
  have hpe : proc = maxProc := (procOf_eq hlookup).symm
  subst hpe
  intro σ_entry fac σ_exit emitted hbody
  rw [max_body_eq] at hbody
  cases hbody with
  | structured hrun =>
    rename_i ρ'
    have hfr := Core.setBodyE_frame mmAST.findProcByString? resultId maxSetExpr maxSetMd
      σ_entry fac ρ' emitted hrun
    show Imperative.invStoresExcept σ_entry ρ'.store (ListMap.keys maxProc.header.outputs)
    rw [show ListMap.keys maxProc.header.outputs = [resultId] from by native_decide]
    exact hfr

/-- Every execution of the Min16 body respects its output frame. -/
private theorem min_body_frame :
    ∀ proc, mmAST.findProcByString? "Min16" = some proc →
      Core.Logic.Hoare.Procedure.bodyFrame mmAST.findProcByString? proc := by
  intro proc hlookup
  have hpe : proc = minProc := (procOf_eq hlookup).symm
  subst hpe
  intro σ_entry fac σ_exit emitted hbody
  rw [min_body_eq] at hbody
  cases hbody with
  | structured hrun =>
    rename_i ρ'
    have hfr := Core.setBodyE_frame mmAST.findProcByString? resultId minSetExpr minSetMd
      σ_entry fac ρ' emitted hrun
    show Imperative.invStoresExcept σ_entry ρ'.store (ListMap.keys minProc.header.outputs)
    rw [show ListMap.keys minProc.header.outputs = [resultId] from by native_decide]
    exact hfr

/-! ### Value helpers and evaluation of the callee body expression -/

private def vMax (a b : BitVec 16) : BitVec 16 := if BitVec.ule a b then b else a
private def vMin (a b : BitVec 16) : BitVec 16 := if BitVec.ule a b then a else b
private def bvc (w : BitVec 16) : Core.Expression.Expr := Lambda.LExpr.bitvecConst () 16 w

/-- The 16-bit bitvector `w` as a value of the runtime factory `F`. -/
private abbrev bvV (F : Core.Expression.Factory) (w : BitVec 16) : Core.Expression.Val :=
  Lambda.SemValue.ofBitVec F.model.tcInterp 16 w

/-- A 16-bit literal evaluates to its value. -/
private theorem bvc_eval (F : Core.Expression.Factory) (σ : Core.CoreStore) (w : BitVec 16) :
    Core.Expression.eval F σ (bvc w) = some (bvV F w) :=
  Core.eval_const F σ (.bitvecConst 16 w)

/-- A variable bound to a 16-bit value of the factory evaluates to it. -/
private theorem bv_fvar_eval {F : Core.Expression.Factory} {σ : Core.CoreStore}
    {id : Core.Expression.Ident} {w : BitVec 16} (h : σ id = some (bvV F w)) :
    Core.Expression.eval F σ (.fvar () id bv16Ty) = some (bvV F w) :=
  Core.eval_fvar F h rfl

/-- The test helper for unsigned comparison is the generated `Bv16.ULe` operator. -/
private theorem bv16ULeApp_eq (x y : Core.Expression.Expr) :
    bv16ULeApp x y = .app () (.app () (Core.bv16ULeFunc).opExpr x) y := by
  have h : (Core.bv16ULeFunc).opExpr = Lambda.LExpr.op () ⟨"Bv16.ULe", ()⟩ (some bv16ArrowTy) := by
    native_decide
  simp only [bv16ULeApp, h]

/-- **Initialized frame for a `(in x, in y, out result)` callee with no inout.**
    The two inputs receive the evaluated actuals, `result` the caller's out slot; the
    frame is a well-formed store and, with no inout params, equals the pre-old store. -/
private theorem bv16_callentry_facts
    (proc : Core.Procedure) (callArgs : List (Imperative.CallArg Core.Expression))
    (fac : Core.Expression.Factory) (σ σAO : Core.CoreStore)
    (exX exY : Core.Expression.Expr) (outVar : Core.Expression.Ident)
    (hsem : Imperative.WellFormedSemanticEval (P := Core.Expression) fac)
    (hwfσ : Imperative.WellFormedStore σ fac)
    (hIn : Core.CallArg.getInputExprs callArgs = [exX, exY])
    (hOutArgs : Imperative.CallArg.getOutArgs callArgs = [outVar])
    (hInKeys : ListMap.keys proc.header.inputs = [xId, yId])
    (hOutOnly : ListMap.keys proc.header.getOutputOnlyParams = [resultId])
    (hInout : ListMap.keys proc.header.getInoutParams = [])
    (h : Core.CallEntry fac σ proc callArgs σAO) :
    (∃ vx, Core.Expression.eval fac σ exX = some vx ∧ σAO xId = some vx ∧
        HasVal.value fac vx) ∧
    (∃ vy, Core.Expression.eval fac σ exY = some vy ∧ σAO yId = some vy ∧
        HasVal.value fac vy) ∧
    (∃ vr, σAO resultId = some vr ∧ HasVal.value fac vr) ∧
    Imperative.WellFormedStore σAO fac := by
  obtain ⟨inputVals, outOnlyVals, hEE, hRV, σA, σIO, hIA, hIO, hSnap⟩ := h
  rw [show Imperative.Calls.getInputExprs callArgs = _ from hIn] at hEE
  rw [hOutArgs] at hRV
  rw [show Imperative.ProcedureHeader.inputParams (P := Core.Expression) proc.header = _
    from hInKeys] at hIA
  rw [← Core.Procedure.Header.keys_getOutputOnlyParams, hOutOnly] at hIO
  have hAOeq : σAO = σIO := by
    rw [hSnap, ← Core.Procedure.Header.keys_getInoutParams, hInout]
    funext id
    simp [Imperative.Calls.withOldSnapshots]
  cases hEE with
  | eval_some _hd1 he1 hEE2 =>
    cases hEE2 with
    | eval_some _hd2 he2 hEE3 =>
      cases hEE3
      cases hRV with
      | read_some hrval hrcanon hRV2 =>
        cases hRV2
        have hcx := hsem.val.outputsAreValues _ _ _ hwfσ he1
        have hcy := hsem.val.outputsAreValues _ _ _ hwfσ he2
        have hwfA : Imperative.WellFormedStore σA fac :=
          Imperative.initStates_preserves_wf hIA
            (by intro w v hv; simp [Imperative.emptyStore] at hv)
            (by intro v hv
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
                rcases hv with rfl | rfl
                · exact hcx
                · exact hcy)
        have hwfIO : Imperative.WellFormedStore σIO fac :=
          Imperative.initStates_preserves_wf hIO hwfA
            (by intro v hv; simp only [List.mem_singleton] at hv; subst hv; exact hrcanon)
        cases hIA with
        | init_some hix hIA2 =>
          cases hIA2 with
          | init_some hiz hIA3 =>
            cases hIA3
            cases hIO with
            | init_some hiy hIO2 =>
              cases hIO2
              cases hix with
              | init _ hix2 _hixoth =>
                cases hiz with
                | init _ hiz2 hizoth =>
                  cases hiy with
                  | init _ hiy2 hiyoth =>
                    have hIOx : σIO xId = some _ :=
                      (hiyoth xId (by decide)).trans ((hizoth xId (by decide)).trans hix2)
                    have hIOy : σIO yId = some _ := (hiyoth yId (by decide)).trans hiz2
                    refine ⟨⟨_, he1, ?_, hcx⟩, ⟨_, he2, ?_, hcy⟩, ⟨_, ?_, hrcanon⟩, ?_⟩
                    · rw [hAOeq]; exact hIOx
                    · rw [hAOeq]; exact hIOy
                    · rw [hAOeq]; exact hiy2
                    · rw [hAOeq]; exact hwfIO

/-- **Write-back for a single `out result` callee.**  Reads `result` from the callee-exit
    store and writes it to the caller's `outVar`, preserving all other slots. -/
private theorem bv16_callexit_facts
    (proc : Core.Procedure) (callArgs : List (Imperative.CallArg Core.Expression))
    (fac : Core.Expression.Factory) (σ σEnd σ' : Core.CoreStore) (outVar : Core.Expression.Ident)
    (hOutKeys : ListMap.keys proc.header.outputs = [resultId])
    (hLhs : Imperative.CallArg.getLhs callArgs = [outVar])
    (h : Core.CallExit fac σ proc callArgs σEnd σ') :
    ∃ vr, σEnd resultId = some vr ∧ HasVal.value fac vr ∧
      σ' outVar = some vr ∧ (∀ k, k ≠ outVar → σ' k = σ k) := by
  obtain ⟨_, outputVals, hRV, hUpd, -⟩ := h
  rw [show Imperative.ProcedureHeader.outputParams (P := Core.Expression) proc.header = _
    from hOutKeys] at hRV
  rw [hLhs] at hUpd
  cases hRV with
  | read_some hres hrcanon hRV2 =>
    cases hRV2
    cases hUpd with
    | update_some hub hUpd2 =>
      cases hUpd2
      cases hub with
      | update _hold hnew hother =>
        exact ⟨_, hres, hrcanon, hnew, fun k hk => hother k (fun hc => hk hc.symm)⟩

/-- The conditional `if Bv16.ULe x y then t else e`, with the variables bound to 16-bit
    values of `F`, evaluates to the selected value. -/
private theorem ite_bv16ULe_eval (F : Core.Expression.Factory) (hF : F.factory = Core.Factory)
    (σ : Core.CoreStore) (va vb vt ve : BitVec 16)
    (cxId cyId tId eId : Core.Expression.Ident)
    (hcx : σ cxId = some (bvV F va)) (hcy : σ cyId = some (bvV F vb))
    (ht : σ tId = some (bvV F vt)) (he : σ eId = some (bvV F ve)) :
    Core.Expression.eval F σ
      (Lambda.LExpr.ite () (bv16ULeApp (.fvar () cxId bv16Ty) (.fvar () cyId bv16Ty))
        (.fvar () tId bv16Ty) (.fvar () eId bv16Ty)) =
      some (bvV F (if BitVec.ule va vb then vt else ve)) := by
  have hcond : Core.Expression.eval F σ (bv16ULeApp (.fvar () cxId bv16Ty) (.fvar () cyId bv16Ty)) =
      some (Lambda.SemValue.ofBool F.model.tcInterp (BitVec.ule va vb)) := by
    rw [bv16ULeApp_eq]
    exact Core.eval_bv16ULe hF (bv_fvar_eval hcx) (bv_fvar_eval hcy)
  rw [Core.eval_ite F hcond (bv_fvar_eval ht) (bv_fvar_eval he) rfl]
  cases BitVec.ule va vb <;> rfl

/-- From the semantic postcondition, the callee output `result` holds exactly
    `if BitVec.ule va vb then vt else ve`. -/
private theorem bv16_result_value
    (F : Core.Expression.Factory) (hF : F.factory = Core.Factory)
    (proc : Core.Procedure) (ρ' : Imperative.Env Core.Expression) (hρ : ρ'.factory = F)
    (va vb vt ve : BitVec 16)
    (cxId cyId tId eId : Core.Expression.Ident)
    (hpost : Core.Logic.Hoare.Procedure.contractPost Core.Factory proc ρ')
    (hout : Core.Logic.Hoare.Procedure.outputAsPredicate proc ρ')
    (hOutList : (resultId, Lambda.LMonoTy.bitvec 16) ∈ proc.header.outputs.toList)
    (hens1 : ∃ lbl chk, (lbl, chk) ∈ proc.spec.postconditions.toList ∧
        chk.attr = Core.Procedure.CheckAttr.Default ∧
        chk.expr = Lambda.LExpr.eq () (.fvar () resultId bv16Ty)
          (Lambda.LExpr.ite () (bv16ULeApp (.fvar () cxId bv16Ty) (.fvar () cyId bv16Ty))
            (.fvar () tId bv16Ty) (.fvar () eId bv16Ty)))
    (hcx : ρ'.store cxId = some (bvV F va)) (hcy : ρ'.store cyId = some (bvV F vb))
    (ht : ρ'.store tId = some (bvV F vt)) (he : ρ'.store eId = some (bvV F ve)) :
    ρ'.store resultId = some (bvV F (if BitVec.ule va vb then vt else ve)) := by
  obtain ⟨vr, hres, hvtr⟩ := hout resultId (Lambda.LMonoTy.bitvec 16) hOutList
  obtain ⟨lbl, chk, hmem, hattr, hexpr⟩ := hens1
  rcases hpost lbl chk hmem hattr (someValuation _) with ⟨_, hex⟩ | ⟨hne, _⟩
  · change Core.Expression.eval ρ'.factory ρ'.store chk.expr =
      some (HasBool.ttVal ρ'.factory) at hex
    rw [hexpr, hρ] at hex
    obtain ⟨w, hw, hwtc⟩ := Lambda.LExpr.denoteEval_defines hex resultId
      (by simp [Lambda.LExpr.LExpr.getVars])
    rw [hres] at hw
    cases hw
    rw [hres]
    refine congrArg some (Classical.byContradiction fun hne => HasBool.ttVal_ne_ffVal F
      (Option.some.inj (hex.symm.trans (Core.eval_eq_false F (Core.eval_fvar F hres hwtc)
        (ite_bv16ULe_eval F hF ρ'.store va vb vt ve cxId cyId tId eId hcx hcy ht he)
        (Lambda.LSort.toMonoTy_injective (t := .bitvec 16) hvtr) hne))))
  · exact absurd (by rw [hρ]; exact hF) hne

/-- **Callee body block well-formedness for a `set result := setE` body.**  The body
    declares nothing, its reads are covered by `hreads`, its one write `result` by `hres`;
    every operator is declared because `testParams` declares all names.  `hty` gives a
    typing of the store under which every type annotation on a free variable of `setE`
    is the type of the value the store holds there. -/
private theorem setBlockWF (setE : Core.Expression.Expr)
    (md : Imperative.MetaData Core.Expression) (ρ : Imperative.Env Core.Expression)
    (hf : ρ.factory.factory = Core.Factory)
    (hsv : Imperative.WellFormedStore ρ.store ρ.factory)
    (hreads : ∀ n ∈ Imperative.HasVarsImp.readVars (P := Core.Expression)
        (Imperative.CmdExt.cmd (Imperative.Cmd.set resultId (.det setE) md)),
        (ρ.store n).isSome = true)
    (hres : (ρ.store resultId).isSome = true)
    (hty : ∃ Γ, StoreHasTyping ρ.factory ρ.store Γ ∧
      Γ.annotates (Imperative.HasTypedVarsImp.typedReadVars (P := Core.Expression)
        (Imperative.CmdExt.cmd (Imperative.Cmd.set resultId (.det setE) md)))) :
    Core.Logic.BlockInitEnvWF testParams
      [Imperative.Stmt.block "" [Imperative.Stmt.cmd (Imperative.CmdExt.cmd
        (Imperative.Cmd.set resultId (.det setE) md))] #[]] ρ := by
  refine Core.Logic.BlockInitEnvWF.of_defUseOk (Core.coreFactory_WellFormedSemanticEval _ hf)
    hsv (fun n hn => ?_) (fun n hn => ?_) (fun n _ p hp => ?_) ?_
    (fun _ _ => rfl)
    (by
      simp [Block.InitTypesInhabited, Block.initTypes, Stmt.initTypes,
        HasInitTypesImp.initTypes, CmdExt.initTypes, Cmd.initTypes])
    (by obtain ⟨Γ, hσ, ha⟩ := hty; exact ⟨Γ, hσ, ⟨ha, trivial⟩, trivial⟩)
  · simp [Imperative.Block.definedVars, Imperative.Stmt.definedVars,
      Imperative.HasVarsImp.definedVars, Imperative.CmdExt.definedVars,
      Imperative.Cmd.definedVars] at hn
  · simp [Imperative.Block.definedVars, Imperative.Stmt.definedVars,
      Imperative.HasVarsImp.definedVars, Imperative.CmdExt.definedVars,
      Imperative.Cmd.definedVars] at hn
  · simp [testParams] at hp
  · simp only [Imperative.Block.defUseWellFormed, Imperative.Stmt.defUseWellFormed,
      Imperative.HasVarsImp.definedVars, Imperative.CmdExt.definedVars, Imperative.Cmd.definedVars,
      List.all_nil, Bool.and_true, testParams, Bool.and_eq_true, List.all_eq_true]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro n hn; exact hreads n hn
    · intro n hn
      simp only [Imperative.HasVarsImp.modifiedVars, Imperative.CmdExt.modifiedVars,
        Imperative.Cmd.modifiedVars, List.mem_singleton] at hn
      subst hn; exact hres
    · intro n _; trivial

/-! ### Generic single-call triple for a `(in,in,out)` bv16 callee -/

/-- One `call P(exX, exY, out outVar)` where `P` is a two-input/one-output bv16
    procedure whose body is `result := bodyE`. `hResultVal` derives the canonical result
    from the semantic contract and output typing; `hActuals` then establishes `Ppost`
    after writeback while preserving every other caller slot. -/
private theorem bv16_call_triple
    (procName : String) (proc : Core.Procedure)
    (callArgs : List (Imperative.CallArg Core.Expression))
    (md bmd : Imperative.MetaData Core.Expression)
    (bodyE : Core.Expression.Expr)
    (exX exY : Core.Expression.Expr) (outVar : Core.Expression.Ident)
    (fval : BitVec 16 → BitVec 16 → BitVec 16)
    (Ppre Ppost : Imperative.Env Core.Expression → Prop)
    (hcontract : Core.Logic.Hoare.Procedure.contractTriple mmAST testParams procName)
    (hframe : ∀ q, mmAST.findProcByString? procName = some q →
      Core.Logic.Hoare.Procedure.bodyFrame mmAST.findProcByString? q)
    (houtputs : ∀ q, mmAST.findProcByString? procName = some q →
      Core.Logic.Hoare.Procedure.bodyOutputsTyped
        (mmAST.factoryBeforeProcedure procName) mmAST.findProcByString? q)
    (hproc : mmAST.findProcByString? procName = some proc)
    (hbody : proc.body = .structured [Imperative.Stmt.cmd (Imperative.CmdExt.cmd
      (Imperative.Cmd.set resultId (.det bodyE) bmd))])
    (hIn : Core.CallArg.getInputExprs callArgs = [exX, exY])
    (hOutArgs : Imperative.CallArg.getOutArgs callArgs = [outVar])
    (hLhs : Imperative.CallArg.getLhs callArgs = [outVar])
    (hInKeys : ListMap.keys proc.header.inputs = [xId, yId])
    (hInList : proc.header.inputs.toList =
      [(xId, Lambda.LMonoTy.bitvec 16), (yId, Lambda.LMonoTy.bitvec 16)])
    (hOutOnly : ListMap.keys proc.header.getOutputOnlyParams = [resultId])
    (hInout : ListMap.keys proc.header.getInoutParams = [])
    (hOutKeys : ListMap.keys proc.header.outputs = [resultId])
    (hNoPre : proc.spec.preconditions.toList = [])
    (hReadsSub : ∀ n ∈ Imperative.HasVarsImp.readVars (P := Core.Expression)
        (Imperative.CmdExt.cmd (Imperative.Cmd.set resultId (.det bodyE) bmd)),
        n = xId ∨ n = yId)
    (hTypedSub : ∀ p ∈ Imperative.HasTypedVarsImp.typedReadVars (P := Core.Expression)
        (Imperative.CmdExt.cmd (Imperative.Cmd.set resultId (.det bodyE) bmd)),
        (p.1 = xId ∨ p.1 = yId) ∧ p.2 = Lambda.LTy.forAll [] (.bitvec 16))
    (hResultVal : ∀ (F : Core.Expression.Factory) (ρ' : Imperative.Env Core.Expression)
        (va vb : BitVec 16),
        F.factory = Core.Factory → ρ'.factory = F →
        Core.Logic.Hoare.Procedure.contractPost Core.Factory proc ρ' →
        Core.Logic.Hoare.Procedure.outputAsPredicate proc ρ' →
        ρ'.store xId = some (bvV F va) → ρ'.store yId = some (bvV F vb) →
        ρ'.store resultId = some (bvV F (fval va vb)))
    (hActuals : ∀ ρ : Imperative.Env Core.Expression, Ppre ρ →
        Core.Logic.InitEnvWF testParams (Core.Statement.call procName callArgs md) ρ →
        ρ.factory.factory = Core.Factory →
        ∃ va vb, Core.Expression.eval ρ.factory ρ.store exX = some (bvV ρ.factory va) ∧
          Core.Expression.eval ρ.factory ρ.store exY = some (bvV ρ.factory vb) ∧
          (∀ σ' : Core.CoreStore, (∀ k, k ≠ outVar → σ' k = ρ.store k) →
            σ' outVar = some (bvV ρ.factory (fval va vb)) → Ppost { ρ with store := σ' }))
    (hPreFac : ∀ ρ : Imperative.Env Core.Expression, Ppre ρ → ρ.factory.factory = Core.Factory)
    (hfactory : mmAST.factoryBeforeProcedure procName = Core.Factory) :
    Core.Logic.Hoare.Triple mmAST.findProcByString? testParams Ppre
      [Core.Statement.call procName callArgs md] Ppost := by
  rw [← hfactory]
  refine Core.Logic.Hoare.Procedure.call_of_contract mmAST testParams procName
    callArgs md Ppre Ppost hcontract hframe houtputs ?_ ?_
  · -- hentry
    intro ρ₀ proc' σAO hpre hwf hlk hce
    have hpe : proc' = proc := Option.some.inj (hlk.symm.trans hproc)
    subst proc'
    have hfac : ρ₀.factory.factory = Core.Factory := hPreFac ρ₀ hpre
    obtain ⟨⟨vx, hEEx, hAOx, _⟩, ⟨vy, hEEy, hAOy, _⟩,
        ⟨_, hAOr, _⟩, hwfAO⟩ :=
      bv16_callentry_facts proc callArgs ρ₀.factory ρ₀.store σAO exX exY outVar
        hwf.toWellFormedSemanticEval hwf.storeWellDefined hIn hOutArgs hInKeys hOutOnly hInout hce
    obtain ⟨va, vb, hExa, hExb, _⟩ := hActuals ρ₀ hpre hwf hfac
    have hvx : vx = bvV ρ₀.factory va := Option.some.inj (hEEx.symm.trans hExa)
    have hvy : vy = bvV ρ₀.factory vb := Option.some.inj (hEEy.symm.trans hExb)
    rw [hbody]
    refine ⟨⟨?_, hfac.trans hfactory.symm, ?_, ?_⟩, ?_⟩
    · intro label check hmem; rw [hNoPre] at hmem; simp at hmem
    · intro id hid; rw [hInout] at hid; simp at hid
    · intro id ty hmem
      rw [hInList] at hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with h | h
      · obtain ⟨rfl, rfl⟩ := h
        exact ⟨bvV ρ₀.factory va, by rw [← hvx]; exact hAOx, rfl⟩
      · obtain ⟨rfl, rfl⟩ := h
        exact ⟨bvV ρ₀.factory vb, by rw [← hvy]; exact hAOy, rfl⟩
    · exact setBlockWF bodyE bmd { store := σAO, factory := ρ₀.factory } hfac hwfAO
        (fun n hn => (hReadsSub n hn).elim (fun h => by subst h; simp [hAOx])
          (fun h => by subst h; simp [hAOy]))
        (by simp [hAOr])
        ⟨fun n => if n = xId ∨ n = yId then some (Lambda.LTy.forAll [] (.bitvec 16)) else none,
          fun n ty hn => by
            have hn' : (n = xId ∨ n = yId) ∧ Lambda.LTy.forAll [] (.bitvec 16) = ty := by
              by_cases h : n = xId ∨ n = yId <;> simp_all
            obtain ⟨hxy | hxy, rfl⟩ := hn'
            · subst hxy; exact ⟨_, hAOx, by rw [hvx]; exact ⟨rfl, rfl⟩⟩
            · subst hxy; exact ⟨_, hAOy, by rw [hvy]; exact ⟨rfl, rfl⟩⟩,
          fun x ty hm => by
            obtain ⟨hxy, rfl⟩ := hTypedSub (x, ty) hm
            simp [hxy]⟩
  · -- hexit
    intro ρ₀ proc' ρ' σ' σAO hpre hwf hlk hpost hout hρ'fac hce hframeRel hcallexit
    have hpe : proc' = proc := Option.some.inj (hlk.symm.trans hproc)
    subst proc'
    have hfac : ρ₀.factory.factory = Core.Factory := hPreFac ρ₀ hpre
    obtain ⟨va, vb, hExa, hExb, hcont⟩ := hActuals ρ₀ hpre hwf hfac
    obtain ⟨⟨vx, hEEx, hAOx, _⟩, ⟨vy, hEEy, hAOy, _⟩, _, _⟩ :=
      bv16_callentry_facts proc callArgs ρ₀.factory ρ₀.store σAO exX exY outVar
        hwf.toWellFormedSemanticEval hwf.storeWellDefined hIn hOutArgs hInKeys hOutOnly hInout hce
    have hvx : vx = bvV ρ₀.factory va := Option.some.inj (hEEx.symm.trans hExa)
    have hvy : vy = bvV ρ₀.factory vb := Option.some.inj (hEEy.symm.trans hExb)
    have hdisjx : ([xId] : List Core.Expression.Ident).Disj
        (ListMap.keys proc.header.outputs) := by
      rw [hOutKeys]; intro a ha; simp only [List.mem_singleton] at ha; subst ha; decide
    have hdisjy : ([yId] : List Core.Expression.Ident).Disj
        (ListMap.keys proc.header.outputs) := by
      rw [hOutKeys]; intro a ha; simp only [List.mem_singleton] at ha; subst ha; decide
    have hτx : ρ'.store xId = some (bvV ρ₀.factory va) := by
      have hf := hframeRel [xId] hdisjx xId xId (by simp)
      rw [← hf, hAOx, hvx]
    have hτy : ρ'.store yId = some (bvV ρ₀.factory vb) := by
      have hf := hframeRel [yId] hdisjy yId yId (by simp)
      rw [← hf, hAOy, hvy]
    obtain ⟨vres, hEndRes, _hEndCanon, hσ'out, hσ'other⟩ :=
      bv16_callexit_facts proc callArgs ρ₀.factory ρ₀.store ρ'.store σ' outVar hOutKeys hLhs hcallexit
    have hpostCore : Core.Logic.Hoare.Procedure.contractPost Core.Factory proc ρ' :=
      hfactory ▸ hpost
    have hresVal : ρ'.store resultId = some (bvV ρ₀.factory (fval va vb)) :=
      hResultVal ρ₀.factory ρ' va vb hfac hρ'fac hpostCore hout hτx hτy
    have hvres : vres = bvV ρ₀.factory (fval va vb) := Option.some.inj (hEndRes.symm.trans hresVal)
    rw [hvres] at hσ'out
    exact hcont σ' hσ'other hσ'out

/-! ### Shared Max16 / Min16 facts -/

/-- The Max16 assignment is the XOR-and-mask maximum expression. -/
private theorem max_setE_eq : maxSetExpr = maxBitHackExpr := by native_decide

/-- The Min16 assignment is the XOR-and-mask minimum expression. -/
private theorem min_setE_eq : minSetExpr = minBitHackExpr := by native_decide

/-- The unchanged Max16 specification uses the unsigned conditional maximum. -/
private theorem max_specE_eq :
    maxSpecExpr = Lambda.LExpr.ite ()
      (bv16ULeApp (.fvar () xId bv16Ty) (.fvar () yId bv16Ty))
      (.fvar () yId bv16Ty) (.fvar () xId bv16Ty) := by
  native_decide

/-- The unchanged Min16 specification uses the unsigned conditional minimum. -/
private theorem min_specE_eq :
    minSpecExpr = Lambda.LExpr.ite ()
      (bv16ULeApp (.fvar () xId bv16Ty) (.fvar () yId bv16Ty))
      (.fvar () xId bv16Ty) (.fvar () yId bv16Ty) := by
  native_decide

private def vMask (a b : BitVec 16) : BitVec 16 :=
  if BitVec.ule a b then BitVec.ofNat 16 65535 else BitVec.ofNat 16 0

/-- The comparison mask evaluates to all ones when `a ≤ᵤ b`, and zero otherwise. -/
private theorem hEval_mask (F : Core.Expression.Factory) (hF : F.factory = Core.Factory)
    (σ : Core.CoreStore) (va vb : BitVec 16)
    (hx : σ xId = some (bvV F va)) (hy : σ yId = some (bvV F vb)) :
    Core.Expression.eval F σ bitHackMaskExpr = some (bvV F (vMask va vb)) := by
  have hcond : Core.Expression.eval F σ
      (bv16ULeApp (.fvar () xId bv16Ty) (.fvar () yId bv16Ty)) =
      some (Lambda.SemValue.ofBool F.model.tcInterp (BitVec.ule va vb)) := by
    rw [bv16ULeApp_eq]
    exact Core.eval_bv16ULe (m := ()) (m' := ()) hF (bv_fvar_eval hx) (bv_fvar_eval hy)
  have hite := Core.eval_ite F (m := ()) hcond (bvc_eval F σ (BitVec.ofNat 16 65535))
    (bvc_eval F σ (BitVec.ofNat 16 0)) rfl
  refine hite.trans (congrArg some ?_)
  unfold vMask
  cases BitVec.ule va vb <;> rfl

/-- The XOR-and-mask expression selects the unsigned maximum. -/
private theorem bv16_bitHack_max (a b : BitVec 16) :
    BitVec.xor a (BitVec.and (BitVec.xor a b) (vMask a b)) = vMax a b := by
  by_cases h : BitVec.ule a b
  · have hall : BitVec.ofNat 16 65535 = BitVec.allOnes 16 := by native_decide
    simp only [vMask, vMax, h, ite_true, hall]
    change a ^^^ ((a ^^^ b) &&& BitVec.allOnes 16) = b
    rw [BitVec.and_allOnes, ← BitVec.xor_assoc, BitVec.xor_self, BitVec.zero_xor]
  · simp [vMask, vMax, h]

/-- The XOR-and-mask expression selects the unsigned minimum. -/
private theorem bv16_bitHack_min (a b : BitVec 16) :
    BitVec.xor b (BitVec.and (BitVec.xor a b) (vMask a b)) = vMin a b := by
  by_cases h : BitVec.ule a b
  · have hall : BitVec.ofNat 16 65535 = BitVec.allOnes 16 := by native_decide
    simp only [vMask, vMin, h, ite_true, hall]
    change b ^^^ ((a ^^^ b) &&& BitVec.allOnes 16) = a
    rw [BitVec.and_allOnes, BitVec.xor_comm a b, ← BitVec.xor_assoc,
      BitVec.xor_self, BitVec.zero_xor]
  · simp [vMask, vMin, h]

/-- The Max16 bit-twiddling assignment evaluates to unsigned maximum. -/
private theorem hEval_max (F : Core.Expression.Factory) (hF : F.factory = Core.Factory)
    (σ : Core.CoreStore) (va vb : BitVec 16)
    (hx : σ xId = some (bvV F va)) (hy : σ yId = some (bvV F vb)) :
    Core.Expression.eval F σ maxSetExpr = some (bvV F (vMax va vb)) := by
  rw [max_setE_eq]
  have hxy : Core.Expression.eval F σ
      (bv16XorApp (.fvar () xId bv16Ty) (.fvar () yId bv16Ty)) =
      some (bvV F (BitVec.xor va vb)) :=
    Core.eval_bv16Xor hF (bv_fvar_eval hx) (bv_fvar_eval hy)
  have hand : Core.Expression.eval F σ
      (bv16AndApp (bv16XorApp (.fvar () xId bv16Ty) (.fvar () yId bv16Ty)) bitHackMaskExpr) =
      some (bvV F (BitVec.and (BitVec.xor va vb) (vMask va vb))) :=
    Core.eval_bv16And hF hxy (hEval_mask F hF σ va vb hx hy)
  have hout : Core.Expression.eval F σ maxBitHackExpr =
      some (bvV F (BitVec.xor va (BitVec.and (BitVec.xor va vb) (vMask va vb)))) :=
    Core.eval_bv16Xor hF (bv_fvar_eval hx) hand
  rw [bv16_bitHack_max] at hout
  exact hout

/-- The Min16 bit-twiddling assignment evaluates to unsigned minimum. -/
private theorem hEval_min (F : Core.Expression.Factory) (hF : F.factory = Core.Factory)
    (σ : Core.CoreStore) (va vb : BitVec 16)
    (hx : σ xId = some (bvV F va)) (hy : σ yId = some (bvV F vb)) :
    Core.Expression.eval F σ minSetExpr = some (bvV F (vMin va vb)) := by
  rw [min_setE_eq]
  have hxy : Core.Expression.eval F σ
      (bv16XorApp (.fvar () xId bv16Ty) (.fvar () yId bv16Ty)) =
      some (bvV F (BitVec.xor va vb)) :=
    Core.eval_bv16Xor hF (bv_fvar_eval hx) (bv_fvar_eval hy)
  have hand : Core.Expression.eval F σ
      (bv16AndApp (bv16XorApp (.fvar () xId bv16Ty) (.fvar () yId bv16Ty)) bitHackMaskExpr) =
      some (bvV F (BitVec.and (BitVec.xor va vb) (vMask va vb))) :=
    Core.eval_bv16And hF hxy (hEval_mask F hF σ va vb hx hy)
  have hout : Core.Expression.eval F σ minBitHackExpr =
      some (bvV F (BitVec.xor vb (BitVec.and (BitVec.xor va vb) (vMask va vb)))) :=
    Core.eval_bv16Xor hF (bv_fvar_eval hy) hand
  rw [bv16_bitHack_min] at hout
  exact hout

/-- A captured `result == if Bv16.ULe x y then t else e` holds in every world when the
    store binds the variables to values satisfying the equality. -/
private theorem post_eq_ite_holds
    (world : Core.Logic.DenoteValuation Core.Factory)
    (F : Core.Expression.Factory) (hF : F.factory = Core.Factory)
    (σ : Core.CoreStore) (va vb vt ve vr : BitVec 16)
    (cxId cyId tId eId rId : Core.Expression.Ident)
    (label : Core.CoreLabel) (md : Imperative.MetaData Core.Expression)
    (hcx : σ cxId = some (bvV F va)) (hcy : σ cyId = some (bvV F vb))
    (ht : σ tId = some (bvV F vt)) (he : σ eId = some (bvV F ve))
    (hr : σ rId = some (bvV F vr))
    (hval : vr = if BitVec.ule va vb then vt else ve) :
    (Core.Logic.DenoteBasedInterp Core.Factory).holds world
      { factory := F, store := σ, label := label,
        expr := Lambda.LExpr.eq () (.fvar () rId bv16Ty)
          (Lambda.LExpr.ite () (bv16ULeApp (.fvar () cxId bv16Ty) (.fvar () cyId bv16Ty))
            (.fvar () tId bv16Ty) (.fvar () eId bv16Ty)),
        metadata := md } := by
  refine Or.inl ⟨hF, ?_⟩
  have hite := ite_bv16ULe_eval F hF σ va vb vt ve cxId cyId tId eId hcx hcy ht he
  rw [← hval] at hite
  exact Core.eval_eq_true F (bv_fvar_eval hr) hite

/-- A typed two-input Bv16 assignment meets its contract when `hBodyEval` computes
    the result function and `hPostDenote` establishes the semantic postcondition. -/
private theorem bv16_set_contract
    (procName : String) (proc : Core.Procedure)
    (bodyE : Core.Expression.Expr) (md : Imperative.MetaData Core.Expression)
    (fval : BitVec 16 → BitVec 16 → BitVec 16)
    (hproc : mmAST.findProcByString? procName = some proc)
    (hbody : proc.body = .structured [Imperative.Stmt.cmd
      (Imperative.CmdExt.cmd (Imperative.Cmd.set resultId (.det bodyE) md))])
    (hChecksTyped : Core.Logic.Hoare.Procedure.contractChecksTyped proc)
    (hInList : proc.header.inputs.toList =
      [(xId, Lambda.LMonoTy.bitvec 16), (yId, Lambda.LMonoTy.bitvec 16)])
    (hBodyEval : ∀ (F : Core.Expression.Factory), F.factory = Core.Factory →
      ∀ (σ : Core.CoreStore) (a b : BitVec 16),
      σ xId = some (bvV F a) → σ yId = some (bvV F b) →
      Core.Expression.eval F σ bodyE = some (bvV F (fval a b)))
    (hPostDenote : ∀ (F : Core.Expression.Factory) (ρ' : Imperative.Env Core.Expression)
        (a b : BitVec 16), F.factory = Core.Factory → ρ'.factory = F →
        ρ'.store xId = some (bvV F a) → ρ'.store yId = some (bvV F b) →
        ρ'.store resultId = some (bvV F (fval a b)) →
        Core.Logic.Hoare.Procedure.postAsPredicate Core.Factory proc ρ')
    (hfactory : mmAST.factoryBeforeProcedure procName = Core.Factory) :
    Core.Logic.Hoare.Procedure.contractTriple mmAST testParams procName := by
  rw [Core.Logic.Hoare.Procedure.contractTriple, hfactory]
  refine ⟨proc, hproc, hChecksTyped, ?_⟩
  rw [hbody]
  refine Core.Logic.Hoare.block mmAST.findProcByString? testParams ?_
    (Imperative.Logic.Hoare.postWF_of_definedVars_nil _ (by
      simp [Imperative.Block.definedVars, Imperative.Stmt.definedVars,
        Imperative.HasVarsImp.definedVars, Imperative.CmdExt.definedVars,
        Imperative.Cmd.definedVars]))
  refine Core.Logic.Hoare.cmd mmAST.findProcByString? testParams
    (Imperative.CmdExt.cmd (Imperative.Cmd.set resultId (.det bodyE) md))
    (Core.Logic.Hoare.Procedure.contractPre Core.Factory proc)
    (Core.Logic.Hoare.Procedure.contractPost Core.Factory proc)
    (fun ρ₀ σ' emitted hpre hwf hstep => ?_)
  obtain ⟨_, hfac, _, htyped⟩ := hpre
  cases hstep with
  | cmd_sem hcmd =>
    cases hcmd with
    | eval_set heval hupd _ =>
      obtain ⟨vx, hx, htx⟩ := htyped xId (.bitvec 16) (by rw [hInList]; simp)
      obtain ⟨vy, hy, hty⟩ := htyped yId (.bitvec 16) (by rw [hInList]; simp)
      obtain ⟨a, hva⟩ := Lambda.SemValue.exists_ofBitVec htx
      obtain ⟨b, hvb⟩ := Lambda.SemValue.exists_ofBitVec hty
      have htca : vx.tc = ρ₀.factory.model.tcInterp := hwf.storeWellDefined xId vx hx
      have htcb : vy.tc = ρ₀.factory.model.tcInterp := hwf.storeWellDefined yId vy hy
      rw [hva, htca] at hx
      rw [hvb, htcb] at hy
      have hbodyEval := hBodyEval ρ₀.factory hfac ρ₀.store a b hx hy
      have hv : _ = bvV ρ₀.factory (fval a b) := Option.some.inj (heval.symm.trans hbodyEval)
      cases hupd with
      | update _ hnew hother =>
        rw [hv] at hnew
        have hx' : σ' xId = some (bvV ρ₀.factory a) := (hother xId (by decide)).trans hx
        have hy' : σ' yId = some (bvV ρ₀.factory b) := (hother yId (by decide)).trans hy
        exact ⟨True.intro, fun _ =>
          hPostDenote ρ₀.factory { ρ₀ with store := σ' } a b hfac rfl hx' hy' hnew⟩

/-- Max16 has `x` and `y` as its input formals. -/
private theorem max_inKeys : ListMap.keys maxProc.header.inputs = [xId, yId] := by native_decide
/-- Max16 has `x` and `y` as 16-bit input formals. -/
private theorem max_inList : maxProc.header.inputs.toList =
    [(xId, Lambda.LMonoTy.bitvec 16), (yId, Lambda.LMonoTy.bitvec 16)] := by
  native_decide
/-- Max16 has `result` as its output-only formal. -/
private theorem max_outOnly : ListMap.keys maxProc.header.getOutputOnlyParams = [resultId] := by native_decide
/-- Max16 has no inout formals. -/
private theorem max_inout : ListMap.keys maxProc.header.getInoutParams = [] := by native_decide
/-- Max16 has `result` as its sole output formal. -/
private theorem max_outKeys : ListMap.keys maxProc.header.outputs = [resultId] := by native_decide
/-- Max16 has no preconditions. -/
private theorem max_noPre : maxProc.spec.preconditions.toList = [] := by native_decide
/-- Min16 has `x` and `y` as its input formals. -/
private theorem min_inKeys : ListMap.keys minProc.header.inputs = [xId, yId] := by native_decide
/-- Min16 has `x` and `y` as 16-bit input formals. -/
private theorem min_inList : minProc.header.inputs.toList =
    [(xId, Lambda.LMonoTy.bitvec 16), (yId, Lambda.LMonoTy.bitvec 16)] := by
  native_decide
/-- Min16 has `result` as its output-only formal. -/
private theorem min_outOnly : ListMap.keys minProc.header.getOutputOnlyParams = [resultId] := by native_decide
/-- Min16 has no inout formals. -/
private theorem min_inout : ListMap.keys minProc.header.getInoutParams = [] := by native_decide
/-- Min16 has `result` as its sole output formal. -/
private theorem min_outKeys : ListMap.keys minProc.header.outputs = [resultId] := by native_decide
/-- Min16 has no preconditions. -/
private theorem min_noPre : minProc.spec.preconditions.toList = [] := by native_decide

/-- No user functions precede `Max16`, so its visible factory is `Core.Factory`. -/
private theorem max_factory : mmAST.factoryBeforeProcedure "Max16" = Core.Factory :=
  Core.Program.factoryBeforeProcedure_eq_core_of_noFunctions (by decide +kernel)

/-- No user functions precede `Min16`, so its visible factory is `Core.Factory`. -/
private theorem min_factory : mmAST.factoryBeforeProcedure "Min16" = Core.Factory :=
  Core.Program.factoryBeforeProcedure_eq_core_of_noFunctions (by decide +kernel)

/-- No user functions precede `Run`, so its visible factory is `Core.Factory`. -/
private theorem run_factory : mmAST.factoryBeforeProcedure "Run" = Core.Factory :=
  Core.Program.factoryBeforeProcedure_eq_core_of_noFunctions (by decide +kernel)

/-- The Max16 assignment reads only `x` and `y`. -/
private theorem max_readsSub : ∀ n ∈ Imperative.HasVarsImp.readVars (P := Core.Expression)
    (Imperative.CmdExt.cmd (Imperative.Cmd.set resultId (.det maxSetExpr) maxSetMd)), n = xId ∨ n = yId := by
  native_decide
/-- The Min16 assignment reads only `x` and `y`. -/
private theorem min_readsSub : ∀ n ∈ Imperative.HasVarsImp.readVars (P := Core.Expression)
    (Imperative.CmdExt.cmd (Imperative.Cmd.set resultId (.det minSetExpr) minSetMd)), n = xId ∨ n = yId := by
  native_decide

/-- The Max16 assignment annotates only `x` and `y`, both as 16-bit vectors. -/
private theorem max_typedSub : ∀ p ∈ Imperative.HasTypedVarsImp.typedReadVars (P := Core.Expression)
    (Imperative.CmdExt.cmd (Imperative.Cmd.set resultId (.det maxSetExpr) maxSetMd)),
    (p.1 = xId ∨ p.1 = yId) ∧ p.2 = Lambda.LTy.forAll [] (.bitvec 16) := by
  native_decide
/-- The Min16 assignment annotates only `x` and `y`, both as 16-bit vectors. -/
private theorem min_typedSub : ∀ p ∈ Imperative.HasTypedVarsImp.typedReadVars (P := Core.Expression)
    (Imperative.CmdExt.cmd (Imperative.Cmd.set resultId (.det minSetExpr) minSetMd)),
    (p.1 = xId ∨ p.1 = yId) ∧ p.2 = Lambda.LTy.forAll [] (.bitvec 16) := by
  native_decide

/-- Max16 has the expected non-free functional postcondition. -/
private theorem max_hens1 : ∃ lbl chk, (lbl, chk) ∈ maxProc.spec.postconditions.toList ∧
    chk.attr = Core.Procedure.CheckAttr.Default ∧
    chk.expr = Lambda.LExpr.eq () (.fvar () resultId bv16Ty) maxSpecExpr :=
  ⟨(maxProc.spec.postconditions.toList.head!).1, (maxProc.spec.postconditions.toList.head!).2,
    by native_decide, by native_decide, by native_decide⟩
/-- Min16 has the expected non-free functional postcondition. -/
private theorem min_hens1 : ∃ lbl chk, (lbl, chk) ∈ minProc.spec.postconditions.toList ∧
    chk.attr = Core.Procedure.CheckAttr.Default ∧
    chk.expr = Lambda.LExpr.eq () (.fvar () resultId bv16Ty) minSpecExpr :=
  ⟨(minProc.spec.postconditions.toList.head!).1, (minProc.spec.postconditions.toList.head!).2,
    by native_decide, by native_decide, by native_decide⟩

/-- Max16's conditional postcondition holds once `x, y, result` carry `a, b, max(a,b)`. -/
private theorem max_post_denote (F : Core.Expression.Factory)
    (ρ' : Imperative.Env Core.Expression) (a b : BitVec 16)
    (hF : F.factory = Core.Factory) (hρ : ρ'.factory = F)
    (hx : ρ'.store xId = some (bvV F a)) (hy : ρ'.store yId = some (bvV F b))
    (hr : ρ'.store resultId = some (bvV F (vMax a b))) :
    Core.Logic.Hoare.Procedure.postAsPredicate Core.Factory maxProc ρ' := by
  intro label check hmem hattr world
  rw [max_ensures_shape (label, check) hmem hattr, max_specE_eq, hρ]
  exact post_eq_ite_holds world F hF ρ'.store a b b a (vMax a b)
    xId yId yId xId resultId label check.md hx hy hy hx hr rfl

/-- Min16's conditional postcondition holds once `x, y, result` carry `a, b, min(a,b)`. -/
private theorem min_post_denote (F : Core.Expression.Factory)
    (ρ' : Imperative.Env Core.Expression) (a b : BitVec 16)
    (hF : F.factory = Core.Factory) (hρ : ρ'.factory = F)
    (hx : ρ'.store xId = some (bvV F a)) (hy : ρ'.store yId = some (bvV F b))
    (hr : ρ'.store resultId = some (bvV F (vMin a b))) :
    Core.Logic.Hoare.Procedure.postAsPredicate Core.Factory minProc ρ' := by
  intro label check hmem hattr world
  rw [min_ensures_shape (label, check) hmem hattr, min_specE_eq, hρ]
  exact post_eq_ite_holds world F hF ρ'.store a b a b (vMin a b)
    xId yId xId yId resultId label check.md hx hy hx hy hr rfl

/-- Inversion of a single `set x := e` command step: exposes the evaluated value,
    that `x` was bound at entry, and that the post-command store maps `x` to it. -/
private theorem set_cmd_value
    {fac : Core.Expression.Factory} {σ σCmd : Core.CoreStore}
    {x : Core.Expression.Ident} {e : Core.Expression.Expr}
    {md : Imperative.MetaData Core.Expression}
    {emitted : Imperative.Trace Core.Expression}
    (h : Core.EvalCommandE mmAST.findProcByString? fac σ
      (Imperative.CmdExt.cmd (Imperative.Cmd.set x (.det e) md)) σCmd emitted) :
    ∃ v, Core.Expression.eval fac σ e = some v ∧
      (σ x).isSome = true ∧ σCmd x = some v := by
  cases h with
  | cmd_sem hbase =>
    cases hbase with
    | eval_set heval hupd _htyped _hwfvar =>
      cases hupd with
      | update hprev hnew _hother =>
        exact ⟨_, heval, by rw [hprev]; rfl, hnew⟩

/-- Every Max16 body run binds `result` to a 16-bit literal. -/
private theorem max_body_outputs :
    ∀ proc, mmAST.findProcByString? "Max16" = some proc →
      Core.Logic.Hoare.Procedure.bodyOutputsTyped
        (mmAST.factoryBeforeProcedure "Max16") mmAST.findProcByString? proc := by
  rw [max_factory]
  intro proc hlookup
  have hpe : proc = maxProc := (procOf_eq hlookup).symm
  subst hpe
  intro σ_entry fac σ_exit emitted hfeq hin hbody
  rw [max_body_eq] at hbody
  obtain ⟨σCmd, hcmd, hexit⟩ := Core.CoreBodyExecE.singleton_cmd_invert hbody
  obtain ⟨vx, hvx, hvtx⟩ := hin xId (Lambda.LMonoTy.bitvec 16) (by native_decide)
  obtain ⟨vy, hvy, hvty⟩ := hin yId (Lambda.LMonoTy.bitvec 16) (by native_decide)
  obtain ⟨a, hva⟩ := Lambda.SemValue.exists_ofBitVec hvtx
  obtain ⟨b, hvb⟩ := Lambda.SemValue.exists_ofBitVec hvty
  obtain ⟨v, heval, hprev, hnew⟩ := set_cmd_value hcmd
  have hdefs := Lambda.LExpr.denoteEval_defines heval
  obtain ⟨wx, hwx, hwxtc⟩ := hdefs xId (by rw [max_setE_eq]; native_decide)
  obtain ⟨wy, hwy, hwytc⟩ := hdefs yId (by rw [max_setE_eq]; native_decide)
  rw [show σ_entry xId = some vx from hvx] at hwx; cases hwx
  rw [show σ_entry yId = some vy from hvy] at hwy; cases hwy
  rw [hva, hwxtc] at hvx
  rw [hvb, hwytc] at hvy
  intro id ty hmem
  rw [show maxProc.header.outputs.toList = [(resultId, Lambda.LMonoTy.bitvec 16)]
    from by native_decide] at hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  obtain ⟨rfl, rfl⟩ := hmem
  have hcval := Option.some.inj (heval.symm.trans (hEval_max fac hfeq σ_entry a b hvx hvy))
  refine ⟨bvV fac (vMax a b), ?_, rfl⟩
  rw [hexit]
  show Imperative.projectStore σ_entry σCmd resultId = some (bvV fac (vMax a b))
  unfold Imperative.projectStore
  rw [ite_eq_left hprev, hnew, hcval]

/-- Every Min16 body run binds `result` to a 16-bit literal. -/
private theorem min_body_outputs :
    ∀ proc, mmAST.findProcByString? "Min16" = some proc →
      Core.Logic.Hoare.Procedure.bodyOutputsTyped
        (mmAST.factoryBeforeProcedure "Min16") mmAST.findProcByString? proc := by
  rw [min_factory]
  intro proc hlookup
  have hpe : proc = minProc := (procOf_eq hlookup).symm
  subst hpe
  intro σ_entry fac σ_exit emitted hfeq hin hbody
  rw [min_body_eq] at hbody
  obtain ⟨σCmd, hcmd, hexit⟩ := Core.CoreBodyExecE.singleton_cmd_invert hbody
  obtain ⟨vx, hvx, hvtx⟩ := hin xId (Lambda.LMonoTy.bitvec 16) (by native_decide)
  obtain ⟨vy, hvy, hvty⟩ := hin yId (Lambda.LMonoTy.bitvec 16) (by native_decide)
  obtain ⟨a, hva⟩ := Lambda.SemValue.exists_ofBitVec hvtx
  obtain ⟨b, hvb⟩ := Lambda.SemValue.exists_ofBitVec hvty
  obtain ⟨v, heval, hprev, hnew⟩ := set_cmd_value hcmd
  have hdefs := Lambda.LExpr.denoteEval_defines heval
  obtain ⟨wx, hwx, hwxtc⟩ := hdefs xId (by rw [min_setE_eq]; native_decide)
  obtain ⟨wy, hwy, hwytc⟩ := hdefs yId (by rw [min_setE_eq]; native_decide)
  rw [show σ_entry xId = some vx from hvx] at hwx; cases hwx
  rw [show σ_entry yId = some vy from hvy] at hwy; cases hwy
  rw [hva, hwxtc] at hvx
  rw [hvb, hwytc] at hvy
  intro id ty hmem
  rw [show minProc.header.outputs.toList = [(resultId, Lambda.LMonoTy.bitvec 16)]
    from by native_decide] at hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  obtain ⟨rfl, rfl⟩ := hmem
  have hcval := Option.some.inj (heval.symm.trans (hEval_min fac hfeq σ_entry a b hvx hvy))
  refine ⟨bvV fac (vMin a b), ?_, rfl⟩
  rw [hexit]
  show Imperative.projectStore σ_entry σCmd resultId = some (bvV fac (vMin a b))
  unfold Imperative.projectStore
  rw [ite_eq_left hprev, hnew, hcval]

/-- From `outputAsPredicate` and the semantic Max16 postcondition, the callee's
    `result` is exactly the unsigned maximum of its typed inputs. -/
private theorem max_result_val (F : Core.Expression.Factory)
    (ρ' : Imperative.Env Core.Expression) (va vb : BitVec 16)
    (hF : F.factory = Core.Factory) (hρ : ρ'.factory = F)
    (hpost : Core.Logic.Hoare.Procedure.contractPost Core.Factory maxProc ρ')
    (hout : Core.Logic.Hoare.Procedure.outputAsPredicate maxProc ρ')
    (hx : ρ'.store xId = some (bvV F va)) (hy : ρ'.store yId = some (bvV F vb)) :
    ρ'.store resultId = some (bvV F (vMax va vb)) := by
  have hens : ∃ lbl chk, (lbl, chk) ∈ maxProc.spec.postconditions.toList ∧
      chk.attr = Core.Procedure.CheckAttr.Default ∧
      chk.expr = Lambda.LExpr.eq () (.fvar () resultId bv16Ty)
        (Lambda.LExpr.ite () (bv16ULeApp (.fvar () xId bv16Ty) (.fvar () yId bv16Ty))
          (.fvar () yId bv16Ty) (.fvar () xId bv16Ty)) := by
    obtain ⟨lbl, chk, hmem, hattr, hexpr⟩ := max_hens1
    exact ⟨lbl, chk, hmem, hattr, by rw [hexpr, max_specE_eq]⟩
  exact bv16_result_value F hF maxProc ρ' hρ va vb vb va xId yId yId xId
    hpost hout (by native_decide) hens hx hy hy hx

/-- From `outputAsPredicate` and the semantic Min16 postcondition, the callee's
    `result` is exactly the unsigned minimum of its typed inputs. -/
private theorem min_result_val (F : Core.Expression.Factory)
    (ρ' : Imperative.Env Core.Expression) (va vb : BitVec 16)
    (hF : F.factory = Core.Factory) (hρ : ρ'.factory = F)
    (hpost : Core.Logic.Hoare.Procedure.contractPost Core.Factory minProc ρ')
    (hout : Core.Logic.Hoare.Procedure.outputAsPredicate minProc ρ')
    (hx : ρ'.store xId = some (bvV F va)) (hy : ρ'.store yId = some (bvV F vb)) :
    ρ'.store resultId = some (bvV F (vMin va vb)) := by
  have hens : ∃ lbl chk, (lbl, chk) ∈ minProc.spec.postconditions.toList ∧
      chk.attr = Core.Procedure.CheckAttr.Default ∧
      chk.expr = Lambda.LExpr.eq () (.fvar () resultId bv16Ty)
        (Lambda.LExpr.ite () (bv16ULeApp (.fvar () xId bv16Ty) (.fvar () yId bv16Ty))
          (.fvar () xId bv16Ty) (.fvar () yId bv16Ty)) := by
    obtain ⟨lbl, chk, hmem, hattr, hexpr⟩ := min_hens1
    exact ⟨lbl, chk, hmem, hattr, by rw [hexpr, min_specE_eq]⟩
  exact bv16_result_value F hF minProc ρ' hρ va vb va vb xId yId xId yId
    hpost hout (by native_decide) hens hx hy hx hy

/-- **Max16 meets its unchanged conditional contract with the XOR-and-mask body.** -/
theorem max16_meets_contract :
    Core.Logic.Hoare.Procedure.contractTriple mmAST testParams "Max16" :=
  bv16_set_contract "Max16" maxProc maxSetExpr maxSetMd vMax
    (by native_decide) max_body_eq (by native_decide) max_inList hEval_max
    max_post_denote max_factory

/-- **Min16 meets its unchanged conditional contract with the XOR-and-mask body.** -/
theorem min16_meets_contract :
    Core.Logic.Hoare.Procedure.contractTriple mmAST testParams "Min16" :=
  bv16_set_contract "Min16" minProc minSetExpr minSetMd vMin
    (by native_decide) min_body_eq (by native_decide) min_inList hEval_min
    min_post_denote min_factory

/-! ### Intermediate assertions threaded through the four calls -/

private def PA0 (ρ : Imperative.Env Core.Expression) : Prop :=
  ρ.factory.factory = Core.Factory ∧
    Core.Logic.Hoare.Procedure.oldInoutAsPredicate mmRunProc ρ ∧
    Core.Logic.Hoare.Procedure.inputAsPredicate mmRunProc ρ
private def PA1 (ρ : Imperative.Env Core.Expression) : Prop :=
  ρ.factory.factory = Core.Factory ∧ ∃ va vb : BitVec 16,
    ρ.store aId = some (bvV ρ.factory va) ∧ ρ.store bId = some (bvV ρ.factory vb) ∧
    ρ.store maxABId = some (bvV ρ.factory (vMax va vb))
private def PA2 (ρ : Imperative.Env Core.Expression) : Prop :=
  ρ.factory.factory = Core.Factory ∧ ∃ va vb : BitVec 16,
    ρ.store aId = some (bvV ρ.factory va) ∧ ρ.store bId = some (bvV ρ.factory vb) ∧
    ρ.store minMaxAId = some (bvV ρ.factory (vMin (vMax va vb) va))
private def PA3 (ρ : Imperative.Env Core.Expression) : Prop :=
  ρ.factory.factory = Core.Factory ∧ ∃ va vb : BitVec 16,
    ρ.store aId = some (bvV ρ.factory va) ∧
    ρ.store minMaxAId = some (bvV ρ.factory (vMin (vMax va vb) va)) ∧
    ρ.store minABId = some (bvV ρ.factory (vMin va vb))
private def PA4 (ρ : Imperative.Env Core.Expression) : Prop :=
  ρ.factory.factory = Core.Factory ∧ ∃ va vb : BitVec 16,
    ρ.store minMaxAId = some (bvV ρ.factory (vMin (vMax va vb) va)) ∧
    ρ.store maxMinAId = some (bvV ρ.factory (vMax (vMin va vb) va))

/-! ### Per-call argument shapes -/

/-- The first call passes `a` and `b` as inputs. -/
private theorem cArgs1_in : Core.CallArg.getInputExprs cArgs1 =
    [.fvar () aId bv16Ty, .fvar () bId bv16Ty] := by native_decide
/-- The first call reads the initialized `maxAB` output slot. -/
private theorem cArgs1_out : Imperative.CallArg.getOutArgs cArgs1 = [maxABId] := by native_decide
/-- The first call writes its result to `maxAB`. -/
private theorem cArgs1_lhs : Imperative.CallArg.getLhs cArgs1 = [maxABId] := by native_decide
/-- The second call passes `maxAB` and `a` as inputs. -/
private theorem cArgs2_in : Core.CallArg.getInputExprs cArgs2 =
    [.fvar () maxABId bv16Ty, .fvar () aId bv16Ty] := by native_decide
/-- The second call reads the initialized `minMaxA` output slot. -/
private theorem cArgs2_out : Imperative.CallArg.getOutArgs cArgs2 = [minMaxAId] := by native_decide
/-- The second call writes its result to `minMaxA`. -/
private theorem cArgs2_lhs : Imperative.CallArg.getLhs cArgs2 = [minMaxAId] := by native_decide
/-- The third call passes `a` and `b` as inputs. -/
private theorem cArgs3_in : Core.CallArg.getInputExprs cArgs3 =
    [.fvar () aId bv16Ty, .fvar () bId bv16Ty] := by native_decide
/-- The third call reads the initialized `minAB` output slot. -/
private theorem cArgs3_out : Imperative.CallArg.getOutArgs cArgs3 = [minABId] := by native_decide
/-- The third call writes its result to `minAB`. -/
private theorem cArgs3_lhs : Imperative.CallArg.getLhs cArgs3 = [minABId] := by native_decide
/-- The fourth call passes `minAB` and `a` as inputs. -/
private theorem cArgs4_in : Core.CallArg.getInputExprs cArgs4 =
    [.fvar () minABId bv16Ty, .fvar () aId bv16Ty] := by native_decide
/-- The fourth call reads the initialized `maxMinA` output slot. -/
private theorem cArgs4_out : Imperative.CallArg.getOutArgs cArgs4 = [maxMinAId] := by native_decide
/-- The fourth call writes its result to `maxMinA`. -/
private theorem cArgs4_lhs : Imperative.CallArg.getLhs cArgs4 = [maxMinAId] := by native_decide

/-! ### Run ensures shape -/

/-- Run ensures that the two composed results are equal. -/
private theorem mm_run_ensures_shape :
    ∀ lc ∈ mmRunProc.spec.postconditions.toList,
      (Prod.snd lc).attr = Core.Procedure.CheckAttr.Default →
      (Prod.snd lc).expr =
        Lambda.LExpr.eq () (.fvar () maxMinAId bv16Ty) (.fvar () minMaxAId bv16Ty) := by
  native_decide

/-! ### The four call triples -/

/-- The first call establishes `maxAB = max(a, b)`. -/
private theorem call1_triple :
    Core.Logic.Hoare.Triple mmAST.findProcByString? testParams PA0
      [Core.Statement.call "Max16" cArgs1 cMd1] PA1 := by
  refine bv16_call_triple "Max16" maxProc cArgs1 cMd1 maxSetMd maxSetExpr
    (.fvar () aId bv16Ty) (.fvar () bId bv16Ty) maxABId vMax PA0 PA1
    max16_meets_contract (max_body_frame) (max_body_outputs) (by native_decide) max_body_eq
    cArgs1_in cArgs1_out cArgs1_lhs max_inKeys max_inList max_outOnly max_inout max_outKeys max_noPre
    max_readsSub max_typedSub max_result_val ?_ (fun ρ hpre => hpre.1) max_factory
  · intro ρ₀ hpre hwf hfac
    obtain ⟨_hfac, _hold, htyped⟩ := hpre
    obtain ⟨va, hva, hta⟩ := htyped aId (.bitvec 16) (by native_decide)
    obtain ⟨vb, hvb, htb⟩ := htyped bId (.bitvec 16) (by native_decide)
    obtain ⟨wa, hva'⟩ := Lambda.SemValue.exists_ofBitVec hta
    obtain ⟨wb, hvb'⟩ := Lambda.SemValue.exists_ofBitVec htb
    have htca : va.tc = ρ₀.factory.model.tcInterp := hwf.storeWellDefined aId va hva
    have htcb : vb.tc = ρ₀.factory.model.tcInterp := hwf.storeWellDefined bId vb hvb
    have hwa : ρ₀.store aId = some (bvV ρ₀.factory wa) := by rw [hva, hva', htca]
    have hwb : ρ₀.store bId = some (bvV ρ₀.factory wb) := by rw [hvb, hvb', htcb]
    refine ⟨wa, wb, bv_fvar_eval hwa, bv_fvar_eval hwb, ?_⟩
    intro σ' hagree hout
    exact ⟨hfac, wa, wb, (hagree aId (by decide)).trans hwa,
      (hagree bId (by decide)).trans hwb, hout⟩

/-- The second call establishes `minMaxA = min(max(a, b), a)`. -/
private theorem call2_triple :
    Core.Logic.Hoare.Triple mmAST.findProcByString? testParams PA1
      [Core.Statement.call "Min16" cArgs2 cMd2] PA2 := by
  refine bv16_call_triple "Min16" minProc cArgs2 cMd2 minSetMd minSetExpr
    (.fvar () maxABId bv16Ty) (.fvar () aId bv16Ty) minMaxAId vMin PA1 PA2
    min16_meets_contract (min_body_frame) (min_body_outputs) (by native_decide) min_body_eq
    cArgs2_in cArgs2_out cArgs2_lhs min_inKeys min_inList min_outOnly min_inout min_outKeys min_noPre
    min_readsSub min_typedSub min_result_val ?_ (fun ρ hpre => hpre.1) min_factory
  · intro ρ₀ hpre _hwf _hfac
    obtain ⟨hfac, va, vb, ha, hb, hmaxAB⟩ := hpre
    refine ⟨vMax va vb, va, bv_fvar_eval hmaxAB, bv_fvar_eval ha, ?_⟩
    intro σ' hagree hout
    exact ⟨hfac, va, vb, (hagree aId (by decide)).trans ha, (hagree bId (by decide)).trans hb, hout⟩

/-- The third call establishes `minAB = min(a, b)`. -/
private theorem call3_triple :
    Core.Logic.Hoare.Triple mmAST.findProcByString? testParams PA2
      [Core.Statement.call "Min16" cArgs3 cMd3] PA3 := by
  refine bv16_call_triple "Min16" minProc cArgs3 cMd3 minSetMd minSetExpr
    (.fvar () aId bv16Ty) (.fvar () bId bv16Ty) minABId vMin PA2 PA3
    min16_meets_contract (min_body_frame) (min_body_outputs) (by native_decide) min_body_eq
    cArgs3_in cArgs3_out cArgs3_lhs min_inKeys min_inList min_outOnly min_inout min_outKeys min_noPre
    min_readsSub min_typedSub min_result_val ?_ (fun ρ hpre => hpre.1) min_factory
  · intro ρ₀ hpre _hwf _hfac
    obtain ⟨hfac, va, vb, ha, hb, hmm⟩ := hpre
    refine ⟨va, vb, bv_fvar_eval ha, bv_fvar_eval hb, ?_⟩
    intro σ' hagree hout
    exact ⟨hfac, va, vb, (hagree aId (by decide)).trans ha,
      (hagree minMaxAId (by decide)).trans hmm, hout⟩

/-- The fourth call establishes `maxMinA = max(min(a, b), a)`. -/
private theorem call4_triple :
    Core.Logic.Hoare.Triple mmAST.findProcByString? testParams PA3
      [Core.Statement.call "Max16" cArgs4 cMd4] PA4 := by
  refine bv16_call_triple "Max16" maxProc cArgs4 cMd4 maxSetMd maxSetExpr
    (.fvar () minABId bv16Ty) (.fvar () aId bv16Ty) maxMinAId vMax PA3 PA4
    max16_meets_contract (max_body_frame) (max_body_outputs) (by native_decide) max_body_eq
    cArgs4_in cArgs4_out cArgs4_lhs max_inKeys max_inList max_outOnly max_inout max_outKeys max_noPre
    max_readsSub max_typedSub max_result_val ?_ (fun ρ hpre => hpre.1) max_factory
  · intro ρ₀ hpre _hwf _hfac
    obtain ⟨hfac, va, vb, ha, hmm, hminAB⟩ := hpre
    refine ⟨vMin va vb, va, bv_fvar_eval hminAB, bv_fvar_eval ha, ?_⟩
    intro σ' hagree hout
    exact ⟨hfac, va, vb, (hagree minMaxAId (by decide)).trans hmm, hout⟩

/-! ### Local declarations and the Run contract -/

/-- Declaring the local `maxAB` preserves the Run contract-entry facts. -/
private theorem maxAB_init_triple :
    Core.Logic.Hoare.Triple mmAST.findProcByString? testParams PA0 [maxABInitStmt] PA0 := by
  change Core.Logic.Hoare.Triple mmAST.findProcByString? testParams PA0
    [Core.Statement.init maxABId maxABInitTy .nondet maxABInitMd] PA0
  refine Core.Logic.Hoare.cmd mmAST.findProcByString? testParams
    (Imperative.CmdExt.cmd (Imperative.Cmd.init maxABId maxABInitTy .nondet maxABInitMd))
    PA0 PA0 (fun ρ₀ σ' emitted hpre _ hstep => ?_)
  cases hstep with
  | cmd_sem hcmd =>
    cases hcmd with
    | eval_init_unconstrained hinit _ _ =>
      cases hinit with
      | init _ _ hother =>
        obtain ⟨hfac, _, htyped⟩ := hpre
        refine ⟨True.intro, fun _ => ⟨hfac, ?_, ?_⟩⟩
        · intro id hid
          have hnone : ListMap.keys mmRunProc.header.getInoutParams = [] := by native_decide
          rw [hnone] at hid
          simp at hid
        · intro id ty hmem
          have hinputs : mmRunProc.header.inputs.toList =
              [(aId, Lambda.LMonoTy.bitvec 16), (bId, Lambda.LMonoTy.bitvec 16)] := by
            native_decide
          rw [hinputs] at hmem
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
          rcases hmem with h | h
          · obtain ⟨rfl, rfl⟩ := h
            obtain ⟨v, hv, hty⟩ := htyped aId (.bitvec 16) (by native_decide)
            exact ⟨v, (hother aId (by decide)).trans hv, hty⟩
          · obtain ⟨rfl, rfl⟩ := h
            obtain ⟨v, hv, hty⟩ := htyped bId (.bitvec 16) (by native_decide)
            exact ⟨v, (hother bId (by decide)).trans hv, hty⟩

/-- Declaring the local `minAB` preserves the facts established by the first two calls. -/
private theorem minAB_init_triple :
    Core.Logic.Hoare.Triple mmAST.findProcByString? testParams PA2 [minABInitStmt] PA2 := by
  change Core.Logic.Hoare.Triple mmAST.findProcByString? testParams PA2
    [Core.Statement.init minABId minABInitTy .nondet minABInitMd] PA2
  refine Core.Logic.Hoare.cmd mmAST.findProcByString? testParams
    (Imperative.CmdExt.cmd (Imperative.Cmd.init minABId minABInitTy .nondet minABInitMd))
    PA2 PA2 (fun ρ₀ σ' emitted hpre _ hstep => ?_)
  cases hstep with
  | cmd_sem hcmd =>
    cases hcmd with
    | eval_init_unconstrained hinit _ _ =>
      cases hinit with
      | init _ _ hother =>
        obtain ⟨hfac, va, vb, ha, hb, hmm⟩ := hpre
        refine ⟨True.intro, fun _ => ⟨hfac, va, vb, ?_, ?_, ?_⟩⟩
        · exact (hother aId (by decide)).trans ha
        · exact (hother bId (by decide)).trans hb
        · exact (hother minMaxAId (by decide)).trans hmm

/-- The final output facts survive when the procedure block drops local intermediates. -/
private theorem mm_run_PA4_postWF :
    Imperative.Logic.Hoare.PostWF
      [maxABInitStmt, Core.Statement.call "Max16" cArgs1 cMd1,
       Core.Statement.call "Min16" cArgs2 cMd2, minABInitStmt,
       Core.Statement.call "Min16" cArgs3 cMd3,
       Core.Statement.call "Max16" cArgs4 cMd4] PA4 := by
  intro ρ hpost
  obtain ⟨hfac, va, vb, hmm, hmma⟩ := hpost
  have hdefs : Imperative.Block.definedVars
      (P := Core.Expression) (C := Core.Command)
      [maxABInitStmt, Core.Statement.call "Max16" cArgs1 cMd1,
       Core.Statement.call "Min16" cArgs2 cMd2, minABInitStmt,
       Core.Statement.call "Min16" cArgs3 cMd3,
       Core.Statement.call "Max16" cArgs4 cMd4] true = [maxABId, minABId] := by
    native_decide
  rw [hdefs]
  refine ⟨hfac, va, vb, ?_, ?_⟩
  · simpa [Imperative.dropVars, minMaxAId, maxABId, minABId] using hmm
  · simpa [Imperative.dropVars, maxMinAId, maxABId, minABId] using hmma

/-- In any world, an equality of two variables bound to the same 16-bit value of a
    runtime factory over `Core.Factory` holds: both sides evaluate to that value. -/
private theorem eq_fvars_holds
    (world : Core.Logic.DenoteValuation Core.Factory)
    (F : Core.Expression.Factory) (hF : F.factory = Core.Factory)
    (σ : Core.CoreStore) (id1 id2 : Core.Expression.Ident) (w : BitVec 16)
    (label : Core.CoreLabel) (md : Imperative.MetaData Core.Expression)
    (h1 : σ id1 = some (bvV F w)) (h2 : σ id2 = some (bvV F w)) :
    (Core.Logic.DenoteBasedInterp Core.Factory).holds world
      { factory := F, store := σ, label := label,
        expr := Lambda.LExpr.eq () (.fvar () id1 bv16Ty) (.fvar () id2 bv16Ty),
        metadata := md } :=
  Or.inl ⟨hF, Core.eval_eq_true F (bv_fvar_eval h1) (bv_fvar_eval h2)⟩

/-- The final call facts imply the Run’s sole postcondition. -/
private theorem run_post_of_PA4 :
    ∀ ρ, PA4 ρ → Core.Logic.Hoare.Procedure.contractPost Core.Factory mmRunProc ρ := by
  intro ρ hpre
  obtain ⟨hfac, va, vb, hmm, hmma⟩ := hpre
  have habs : vMax (vMin va vb) va = vMin (vMax va vb) va := by
    simp only [vMax, vMin]; exact (bv16_minmax_absorption va vb).symm
  intro label check hmem hattr world
  rw [mm_run_ensures_shape (label, check) hmem hattr]
  exact eq_fvars_holds world ρ.factory hfac ρ.store maxMinAId minMaxAId (vMin (vMax va vb) va)
    label check.md (habs ▸ hmma) hmm

/-- The unsigned 16-bit-vector Run meets its contract: local intermediates
compute two equal nested min/max compositions in its output parameters. -/
theorem mm_run_meets_contract :
    Core.Logic.Hoare.Procedure.contractTriple mmAST testParams "Run" := by
  rw [Core.Logic.Hoare.Procedure.contractTriple, run_factory]
  refine ⟨mmRunProc, by native_decide, by native_decide, ?_⟩
  rw [mm_run_body_eq]
  have hpre : ∀ ρ, Core.Logic.Hoare.Procedure.contractPre Core.Factory mmRunProc ρ → PA0 ρ :=
    fun _ hc => ⟨hc.2.1, hc.2.2.1, hc.2.2.2⟩
  refine Core.Logic.Hoare.consequence mmAST.findProcByString? testParams
    (Core.Logic.Hoare.block mmAST.findProcByString? testParams ?_ (mm_run_PA4_postWF))
    hpre run_post_of_PA4
  have h56 := Core.Logic.Hoare.seq mmAST.findProcByString? testParams
    call3_triple call4_triple
    (by simp [Imperative.Block.exitsCoveredByBlocks, Imperative.Stmt.exitsCoveredByBlocks])
  have h456 := Core.Logic.Hoare.seq mmAST.findProcByString? testParams
    (minAB_init_triple) h56
    (by simp [Imperative.Block.exitsCoveredByBlocks, minABInitStmt,
      Imperative.Stmt.exitsCoveredByBlocks])
  have h3456 := Core.Logic.Hoare.seq mmAST.findProcByString? testParams
    call2_triple h456
    (by simp [Imperative.Block.exitsCoveredByBlocks, Imperative.Stmt.exitsCoveredByBlocks])
  have h23456 := Core.Logic.Hoare.seq mmAST.findProcByString? testParams
    call1_triple h3456
    (by simp [Imperative.Block.exitsCoveredByBlocks, Imperative.Stmt.exitsCoveredByBlocks])
  exact Core.Logic.Hoare.seq mmAST.findProcByString? testParams
    (maxAB_init_triple) h23456
    (by simp [Imperative.Block.exitsCoveredByBlocks, maxABInitStmt,
      Imperative.Stmt.exitsCoveredByBlocks])
end Strata
