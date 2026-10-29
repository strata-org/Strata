/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.Languages.Core
import StrataTest.Languages.Core.Tests.Logic.HoareTestSupport
import Strata.Languages.Core.Logic.HoareCall
import Strata.Languages.Core.ProcedureProps
import Strata.Languages.Core.BitVecEvalProps
import Strata.Languages.Core.ExpressionsProps
import Strata.Languages.Core.InstWellFormedSemanticsEval
import Strata.DL.Lambda.LExprEvalProps
import Strata.DL.Lambda.Denote.LExprDenote
import Strata.DL.Lambda.Denote.LExprDenoteProps
import StrataDDM.Integration.Lean.HashCommands

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

/-- Every 16-bit bitvector literal is a value in `Core.Factory`. -/
private theorem bvc_value (w : BitVec 16) :
    Lambda.LExpr.isValue Core.Factory (bvc w) = true := by
  simp [bvc, Lambda.LExpr.isValue, Lambda.LExpr.bitvecConst]

/-- A variable bound to a 16-bit literal evaluates to that literal. -/
private theorem bvc_evalFully {σ : Core.CoreStore} {id : Core.Expression.Ident} {w : BitVec 16}
    (h : σ id = some (bvc w)) :
    Lambda.LExpr.evalFully Core.Factory σ (.fvar () id bv16Ty) = some (bvc w) :=
  Lambda.evalFully_fvar_of_value Core.Factory σ () id bv16Ty (bvc w) h (bvc_value w)

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
        Lambda.LExpr.isValue fac vx = true) ∧
    (∃ vy, Core.Expression.eval fac σ exY = some vy ∧ σAO yId = some vy ∧
        Lambda.LExpr.isValue fac vy = true) ∧
    (∃ vr, σAO resultId = some vr ∧ Lambda.LExpr.isValue fac vr = true) ∧
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
    ∃ vr, σEnd resultId = some vr ∧ Lambda.LExpr.isValue fac vr = true ∧
      σ' outVar = some vr ∧ (∀ k, k ≠ outVar → σ' k = σ k) := by
  obtain ⟨_, outputVals, hRV, hUpd⟩ := h
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

/-- From the semantic postcondition, the callee output `result` holds exactly
    `if BitVec.ule va vb then vt else ve`. -/
private theorem bv16_result_value
    (model : Lambda.Interp Core.Factory)
    (proc : Core.Procedure) (ρ' : Imperative.Env Core.Expression)
    (va vb vt ve : BitVec 16)
    (cxId cyId tId eId : Core.Expression.Ident)
    (hfac : ρ'.factory = Core.Factory)
    (hpost : Core.Logic.Hoare.Procedure.contractPost model proc ρ')
    (hout : Core.Logic.Hoare.Procedure.outputAsPredicate proc ρ')
    (hOutList : (resultId, Lambda.LMonoTy.bitvec 16) ∈ proc.header.outputs.toList)
    (hens1 : ∃ lbl chk, (lbl, chk) ∈ proc.spec.postconditions.toList ∧
        chk.attr = Core.Procedure.CheckAttr.Default ∧
        chk.expr = Lambda.LExpr.eq () (.fvar () resultId bv16Ty)
          (Lambda.LExpr.ite () (bv16ULeApp (.fvar () cxId bv16Ty) (.fvar () cyId bv16Ty))
            (.fvar () tId bv16Ty) (.fvar () eId bv16Ty)))
    (hcx : ρ'.store cxId = some (bvc va)) (hcy : ρ'.store cyId = some (bvc vb))
    (ht : ρ'.store tId = some (bvc vt)) (he : ρ'.store eId = some (bvc ve)) :
    ρ'.store resultId = some (bvc (if BitVec.ule va vb then vt else ve)) := by
  obtain ⟨vr, hres, hvtr⟩ := hout resultId (Lambda.LMonoTy.bitvec 16) hOutList
  obtain ⟨w0, rfl⟩ := hvtr
  obtain ⟨lbl, chk, hmem, hattr, hexpr⟩ := hens1
  have htw0 : Lambda.LExpr.HasTypeA (T := Core.CoreLParams) [] (bvc w0)
      (Lambda.LMonoTy.bitvec 16) := .const
  have htva : Lambda.LExpr.HasTypeA (T := Core.CoreLParams) [] (bvc va)
      (Lambda.LMonoTy.bitvec 16) := .const
  have htvb : Lambda.LExpr.HasTypeA (T := Core.CoreLParams) [] (bvc vb)
      (Lambda.LMonoTy.bitvec 16) := .const
  have htvt : Lambda.LExpr.HasTypeA (T := Core.CoreLParams) [] (bvc vt)
      (Lambda.LMonoTy.bitvec 16) := .const
  have htve : Lambda.LExpr.HasTypeA (T := Core.CoreLParams) [] (bvc ve)
      (Lambda.LMonoTy.bitvec 16) := .const
  have hop : Lambda.LExpr.HasTypeA (T := Core.CoreLParams) []
      (Lambda.LExpr.op () ⟨"Bv16.ULe", ()⟩ (some bv16ArrowTy))
      (Lambda.LMonoTy.arrow (.bitvec 16) (Lambda.LMonoTy.arrow (.bitvec 16) .bool)) := .op
  have happ1 : Lambda.LExpr.HasTypeA (T := Core.CoreLParams) []
      (.app () (Lambda.LExpr.op () ⟨"Bv16.ULe", ()⟩ (some bv16ArrowTy)) (bvc va))
      (Lambda.LMonoTy.arrow (.bitvec 16) .bool) := .app hop htva
  have hcond : Lambda.LExpr.HasTypeA (T := Core.CoreLParams) []
      (bv16ULeApp (bvc va) (bvc vb)) .bool := .app happ1 htvb
  have hite : Lambda.LExpr.HasTypeA (T := Core.CoreLParams) []
      (Lambda.LExpr.ite () (bv16ULeApp (bvc va) (bvc vb)) (bvc vt) (bvc ve))
      (Lambda.LMonoTy.bitvec 16) := .ite hcond htvt htve
  have heq : Lambda.LExpr.HasTypeA (T := Core.CoreLParams) []
      (Lambda.LExpr.eq () (bvc w0)
        (Lambda.LExpr.ite () (bv16ULeApp (bvc va) (bvc vb)) (bvc vt) (bvc ve))) .bool :=
    .eq htw0 hite
  have hbvc : ∀ (w : BitVec 16)
      (h : Lambda.LExpr.HasTypeA (T := Core.CoreLParams) [] (bvc w) (Lambda.LMonoTy.bitvec 16)),
      Lambda.LExpr.denote model.tcInterp model.opInterp (someValuation model).freeVarVal
        (someValuation model).tyVarVal .nil (bvc w) (Lambda.LMonoTy.bitvec 16) h = w := by
    intro w h
    show Lambda.LExpr.denote model.tcInterp model.opInterp (someValuation model).freeVarVal
      (someValuation model).tyVarVal .nil
      (Lambda.LExpr.const () (Lambda.LConst.bitvecConst 16 w)) (Lambda.LMonoTy.bitvec 16) h = w
    simp only [someValuation]
    apply Lambda.denote_const
  have hcond_denote : Lambda.LExpr.denote model.tcInterp model.opInterp
      (someValuation model).freeVarVal (someValuation model).tyVarVal .nil
      (bv16ULeApp (bvc va) (bvc vb)) .bool hcond = BitVec.ule va vb := by
    simp only [bv16ULeApp]
    rw [Lambda.denote_app .nil happ1 htvb hcond, Lambda.denote_app .nil hop htva happ1,
      hbvc va htva, hbvc vb htvb, Lambda.denote_op]
    show (model.opInterp "Bv16.ULe"
      (bv16ArrowTy.substTyVars (someValuation model).tyVarVal)) va vb = BitVec.ule va vb
    have hop_eq : model.opInterp "Bv16.ULe"
        (bv16ArrowTy.substTyVars (someValuation model).tyVarVal)
        = fun (a b : BitVec 16) => BitVec.ule a b := Core.bv16ULe_opInterp model
    exact congrFun (congrFun hop_eq va) vb
  rcases hpost lbl chk hmem hattr (someValuation model) with ⟨_, hex⟩ | ⟨hne, _⟩
  · have hcap : Core.Logic.capturedExpr
        { factory := ρ'.factory, store := ρ'.store, label := lbl, expr := chk.expr,
          metadata := chk.md }
        = Lambda.LExpr.eq () (bvc w0)
            (Lambda.LExpr.ite () (bv16ULeApp (bvc va) (bvc vb)) (bvc vt) (bvc ve)) := by
      simp only [Core.Logic.capturedExpr, hexpr, bv16ULeApp, Lambda.LExpr.substFvarsFromEnv,
        Lambda.Env.mk, hcx, hcy, ht, he, hres, bvc]
    rw [hcap] at hex
    obtain ⟨_hty, hd⟩ := hex
    have heqd := Lambda.denote_eq_true_implies_eq .nil htw0 hite heq hd
    rw [hbvc w0 htw0, Lambda.denote_ite .nil hcond htvt htve hite, hcond_denote,
      hbvc vt htvt, hbvc ve htve] at heqd
    rw [hres, heqd]
    cases BitVec.ule va vb <;> rfl
  · exact absurd hfac hne

/-- **Callee body block well-formedness for a `set result := setE` body.**  The body
    declares nothing, its reads are covered by `hreads`, its one write `result` by `hres`;
    every operator is declared because `testParams` declares all names. -/
private theorem setBlockWF (setE : Core.Expression.Expr)
    (md : Imperative.MetaData Core.Expression) (ρ : Imperative.Env Core.Expression)
    (hf : ρ.factory = Core.Factory)
    (hsv : Imperative.WellFormedStore ρ.store ρ.factory)
    (hreads : ∀ n ∈ Imperative.HasVarsImp.readVars (P := Core.Expression)
        (Imperative.CmdExt.cmd (Imperative.Cmd.set resultId (.det setE) md)),
        (ρ.store n).isSome = true)
    (hres : (ρ.store resultId).isSome = true) :
    Core.Logic.BlockInitEnvWF testParams
      [Imperative.Stmt.block "" [Imperative.Stmt.cmd (Imperative.CmdExt.cmd
        (Imperative.Cmd.set resultId (.det setE) md))] #[]] ρ := by
  refine Core.Logic.BlockInitEnvWF.of_defUseOk (hf.symm ▸ Core.coreFactory_WellFormedSemanticEval)
    hsv (fun n hn => ?_) (fun n hn => ?_) (fun n _ p hp => ?_) ?_
    (fun _ _ => rfl)
    (by
      simp [Block.InitTypesInhabited, Block.initTypes, Stmt.initTypes,
        HasInitTypesImp.initTypes, CmdExt.initTypes, Cmd.initTypes])
  · simp [Imperative.Block.definedVars, Imperative.Stmt.definedVars,
      Imperative.HasVarsImp.definedVars, Core.Command.definedVars, Imperative.Cmd.definedVars] at hn
  · simp [Imperative.Block.definedVars, Imperative.Stmt.definedVars,
      Imperative.HasVarsImp.definedVars, Core.Command.definedVars, Imperative.Cmd.definedVars] at hn
  · simp [testParams] at hp
  · simp only [Imperative.Block.defUseWellFormed, Imperative.Stmt.defUseWellFormed,
      Imperative.HasVarsImp.definedVars, Core.Command.definedVars, Imperative.Cmd.definedVars,
      List.all_nil, Bool.and_true, testParams, Bool.and_eq_true, List.all_eq_true]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro n hn; exact hreads n hn
    · intro n hn
      simp only [Imperative.HasVarsImp.modifiedVars, Core.Command.modifiedVars,
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
      Core.Logic.Hoare.Procedure.bodyOutputsTyped mmAST.findProcByString? q)
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
    (hResultVal : ∀ (model : Lambda.Interp Core.Factory) (ρ' : Imperative.Env Core.Expression)
        (va vb : BitVec 16),
        ρ'.factory = Core.Factory →
        Core.Logic.Hoare.Procedure.contractPost model proc ρ' →
        Core.Logic.Hoare.Procedure.outputAsPredicate proc ρ' →
        ρ'.store xId = some (bvc va) → ρ'.store yId = some (bvc vb) →
        ρ'.store resultId = some (bvc (fval va vb)))
    (hActuals : ∀ ρ : Imperative.Env Core.Expression, Ppre ρ →
        Core.Logic.InitEnvWF testParams (Core.Statement.call procName callArgs md) ρ →
        ρ.factory = Core.Factory →
        ∃ va vb, Core.Expression.eval Core.Factory ρ.store exX = some (bvc va) ∧
          Core.Expression.eval Core.Factory ρ.store exY = some (bvc vb) ∧
          (∀ σ' : Core.CoreStore, (∀ k, k ≠ outVar → σ' k = ρ.store k) →
            σ' outVar = some (bvc (fval va vb)) → Ppost { ρ with store := σ' }))
    (hPreFac : ∀ ρ : Imperative.Env Core.Expression, Ppre ρ → ρ.factory = Core.Factory) :
    Core.Logic.Hoare.Triple mmAST.findProcByString? testParams Ppre
      [Core.Statement.call procName callArgs md] Ppost := by
  refine Core.Logic.Hoare.Procedure.call_of_contract mmAST testParams procName
    callArgs md Ppre Ppost hcontract hframe houtputs ?_ ?_
  · -- hentry
    intro model ρ₀ proc' σAO hpre hwf hlk hce
    have hpe : proc' = proc := Option.some.inj (hlk.symm.trans hproc)
    subst proc'
    have hfac : ρ₀.factory = Core.Factory := hPreFac ρ₀ hpre
    obtain ⟨⟨vx, hEEx, hAOx, _⟩, ⟨vy, hEEy, hAOy, _⟩,
        ⟨_, hAOr, _⟩, hwfAO⟩ :=
      bv16_callentry_facts proc callArgs ρ₀.factory ρ₀.store σAO exX exY outVar
        hwf.toWellFormedSemanticEval hwf.storeWellDefined hIn hOutArgs hInKeys hOutOnly hInout hce
    obtain ⟨va, vb, hExa, hExb, _⟩ := hActuals ρ₀ hpre hwf hfac
    rw [hfac] at hEEx hEEy
    have hvx : vx = bvc va := Option.some.inj (hEEx.symm.trans hExa)
    have hvy : vy = bvc vb := Option.some.inj (hEEy.symm.trans hExb)
    rw [hbody]
    refine ⟨⟨?_, hfac, ?_, ?_⟩, ?_⟩
    · intro label check hmem; rw [hNoPre] at hmem; simp at hmem
    · intro id hid; rw [hInout] at hid; simp at hid
    · intro id ty hmem
      rw [hInList] at hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with h | h
      · obtain ⟨rfl, rfl⟩ := h
        refine ⟨bvc va, ?_, ?_⟩
        · show σAO xId = some (bvc va)
          rw [hAOx, hvx]
        · exact ⟨va, rfl⟩
      · obtain ⟨rfl, rfl⟩ := h
        refine ⟨bvc vb, ?_, ?_⟩
        · show σAO yId = some (bvc vb)
          rw [hAOy, hvy]
        · exact ⟨vb, rfl⟩
    · exact setBlockWF bodyE bmd { store := σAO, factory := ρ₀.factory, hasFailure := false } hfac hwfAO
        (fun n hn => (hReadsSub n hn).elim (fun h => by subst h; simp [hAOx])
          (fun h => by subst h; simp [hAOy]))
        (by simp [hAOr])
  · -- hexit
    intro model ρ₀ proc' ρ' σ' σAO hpre hwf hlk hpost hout hρ'fac hce hframeRel hcallexit
    have hpe : proc' = proc := Option.some.inj (hlk.symm.trans hproc)
    subst proc'
    have hfac : ρ₀.factory = Core.Factory := hPreFac ρ₀ hpre
    obtain ⟨va, vb, hExa, hExb, hcont⟩ := hActuals ρ₀ hpre hwf hfac
    obtain ⟨⟨vx, hEEx, hAOx, _⟩, ⟨vy, hEEy, hAOy, _⟩, _, _⟩ :=
      bv16_callentry_facts proc callArgs ρ₀.factory ρ₀.store σAO exX exY outVar
        hwf.toWellFormedSemanticEval hwf.storeWellDefined hIn hOutArgs hInKeys hOutOnly hInout hce
    rw [hfac] at hEEx hEEy
    have hvx : vx = bvc va := Option.some.inj (hEEx.symm.trans hExa)
    have hvy : vy = bvc vb := Option.some.inj (hEEy.symm.trans hExb)
    have hdisjx : ([xId] : List Core.Expression.Ident).Disj
        (ListMap.keys proc.header.outputs) := by
      rw [hOutKeys]; intro a ha; simp only [List.mem_singleton] at ha; subst ha; decide
    have hdisjy : ([yId] : List Core.Expression.Ident).Disj
        (ListMap.keys proc.header.outputs) := by
      rw [hOutKeys]; intro a ha; simp only [List.mem_singleton] at ha; subst ha; decide
    have hτx : ρ'.store xId = some (bvc va) := by
      have hf := hframeRel [xId] hdisjx xId xId (by simp)
      rw [← hf, hAOx, hvx]
    have hτy : ρ'.store yId = some (bvc vb) := by
      have hf := hframeRel [yId] hdisjy yId yId (by simp)
      rw [← hf, hAOy, hvy]
    obtain ⟨vres, hEndRes, _hEndCanon, hσ'out, hσ'other⟩ :=
      bv16_callexit_facts proc callArgs ρ₀.factory ρ₀.store ρ'.store σ' outVar hOutKeys hLhs hcallexit
    have hresVal : ρ'.store resultId = some (bvc (fval va vb)) :=
      hResultVal model ρ' va vb (hρ'fac.trans hfac) hpost hout hτx hτy
    have hvres : vres = bvc (fval va vb) := Option.some.inj (hEndRes.symm.trans hresVal)
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
private theorem hEval_mask (σ : Core.CoreStore) (va vb : BitVec 16)
    (hx : σ xId = some (bvc va)) (hy : σ yId = some (bvc vb)) :
    Lambda.LExpr.evalFully Core.Factory σ bitHackMaskExpr = some (bvc (vMask va vb)) := by
  have hcond : Lambda.LExpr.evalFully Core.Factory σ
      (bv16ULeApp (.fvar () xId bv16Ty) (.fvar () yId bv16Ty)) =
      some (Lambda.LExpr.boolConst () (BitVec.ule va vb)) := by
    rw [bv16ULeApp_eq]
    exact Core.coreEval_bv16ULe σ _ _ va vb (bvc_evalFully hx) (bvc_evalFully hy)
  have hite := Core.coreEval_ite σ ()
    (bv16ULeApp (.fvar () xId bv16Ty) (.fvar () yId bv16Ty))
    (bvc (BitVec.ofNat 16 65535)) (bvc (BitVec.ofNat 16 0))
    (BitVec.ule va vb) (bvc (BitVec.ofNat 16 65535)) (bvc (BitVec.ofNat 16 0))
    hcond
    (Lambda.evalFully_const Core.Factory σ () (.bitvecConst 16 (BitVec.ofNat 16 65535)))
    (Lambda.evalFully_const Core.Factory σ () (.bitvecConst 16 (BitVec.ofNat 16 0)))
  by_cases hle : BitVec.ule va vb
  · simpa [bitHackMaskExpr, bvc, vMask, hle] using hite
  · simpa [bitHackMaskExpr, bvc, vMask, hle] using hite

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
private theorem hEval_max (σ : Core.CoreStore) (va vb : BitVec 16)
    (hx : σ xId = some (bvc va)) (hy : σ yId = some (bvc vb)) :
    Lambda.LExpr.evalFully Core.Factory σ maxSetExpr = some (bvc (vMax va vb)) := by
  rw [max_setE_eq]
  have hxy : Lambda.LExpr.evalFully Core.Factory σ
      (bv16XorApp (.fvar () xId bv16Ty) (.fvar () yId bv16Ty)) =
      some (bvc (BitVec.xor va vb)) := by
    simpa [bv16XorApp, bvc] using Core.coreEval_bv16Xor σ _ _ va vb
      (bvc_evalFully hx) (bvc_evalFully hy)
  have hmask := hEval_mask σ va vb hx hy
  have hand : Lambda.LExpr.evalFully Core.Factory σ
      (bv16AndApp
        (bv16XorApp (.fvar () xId bv16Ty) (.fvar () yId bv16Ty))
        bitHackMaskExpr) =
      some (bvc (BitVec.and (BitVec.xor va vb) (vMask va vb))) := by
    simpa [bv16AndApp, bvc] using Core.coreEval_bv16And σ _ _
      (BitVec.xor va vb) (vMask va vb) hxy hmask
  have hout := Core.coreEval_bv16Xor σ (.fvar () xId bv16Ty)
    (bv16AndApp
      (bv16XorApp (.fvar () xId bv16Ty) (.fvar () yId bv16Ty))
      bitHackMaskExpr)
    va (BitVec.and (BitVec.xor va vb) (vMask va vb)) (bvc_evalFully hx) hand
  rw [bv16_bitHack_max] at hout
  simpa [maxBitHackExpr, bv16XorApp, bvc] using hout

/-- The Min16 bit-twiddling assignment evaluates to unsigned minimum. -/
private theorem hEval_min (σ : Core.CoreStore) (va vb : BitVec 16)
    (hx : σ xId = some (bvc va)) (hy : σ yId = some (bvc vb)) :
    Lambda.LExpr.evalFully Core.Factory σ minSetExpr = some (bvc (vMin va vb)) := by
  rw [min_setE_eq]
  have hxy : Lambda.LExpr.evalFully Core.Factory σ
      (bv16XorApp (.fvar () xId bv16Ty) (.fvar () yId bv16Ty)) =
      some (bvc (BitVec.xor va vb)) := by
    simpa [bv16XorApp, bvc] using Core.coreEval_bv16Xor σ _ _ va vb
      (bvc_evalFully hx) (bvc_evalFully hy)
  have hmask := hEval_mask σ va vb hx hy
  have hand : Lambda.LExpr.evalFully Core.Factory σ
      (bv16AndApp
        (bv16XorApp (.fvar () xId bv16Ty) (.fvar () yId bv16Ty))
        bitHackMaskExpr) =
      some (bvc (BitVec.and (BitVec.xor va vb) (vMask va vb))) := by
    simpa [bv16AndApp, bvc] using Core.coreEval_bv16And σ _ _
      (BitVec.xor va vb) (vMask va vb) hxy hmask
  have hout := Core.coreEval_bv16Xor σ (.fvar () yId bv16Ty)
    (bv16AndApp
      (bv16XorApp (.fvar () xId bv16Ty) (.fvar () yId bv16Ty))
      bitHackMaskExpr)
    vb (BitVec.and (BitVec.xor va vb) (vMask va vb)) (bvc_evalFully hy) hand
  rw [bv16_bitHack_min] at hout
  simpa [minBitHackExpr, bv16XorApp, bvc] using hout

/-- A closed captured `result == if Bv16.ULe x y then t else e` holds in every
    world when the store binds the variables to literals satisfying the equality. -/
private theorem post_eq_ite_holds
    (model : Lambda.Interp Core.Factory) (world : Core.Logic.DenoteValuation model)
    (σ : Core.CoreStore) (va vb vt ve vr : BitVec 16)
    (cxId cyId tId eId rId : Core.Expression.Ident)
    (label : Core.CoreLabel) (md : Imperative.MetaData Core.Expression)
    (hcx : σ cxId = some (bvc va)) (hcy : σ cyId = some (bvc vb))
    (ht : σ tId = some (bvc vt)) (he : σ eId = some (bvc ve))
    (hr : σ rId = some (bvc vr))
    (hval : vr = if BitVec.ule va vb then vt else ve) :
    (Core.Logic.DenoteBasedInterp model).holds world
      { factory := Core.Factory, store := σ, label := label,
        expr := Lambda.LExpr.eq () (.fvar () rId bv16Ty)
          (Lambda.LExpr.ite () (bv16ULeApp (.fvar () cxId bv16Ty) (.fvar () cyId bv16Ty))
            (.fvar () tId bv16Ty) (.fvar () eId bv16Ty)),
        metadata := md } := by
  have htvr : Lambda.LExpr.HasTypeA (T := Core.CoreLParams) [] (bvc vr)
      (Lambda.LMonoTy.bitvec 16) := .const
  have htva : Lambda.LExpr.HasTypeA (T := Core.CoreLParams) [] (bvc va)
      (Lambda.LMonoTy.bitvec 16) := .const
  have htvb : Lambda.LExpr.HasTypeA (T := Core.CoreLParams) [] (bvc vb)
      (Lambda.LMonoTy.bitvec 16) := .const
  have htvt : Lambda.LExpr.HasTypeA (T := Core.CoreLParams) [] (bvc vt)
      (Lambda.LMonoTy.bitvec 16) := .const
  have htve : Lambda.LExpr.HasTypeA (T := Core.CoreLParams) [] (bvc ve)
      (Lambda.LMonoTy.bitvec 16) := .const
  have hop : Lambda.LExpr.HasTypeA (T := Core.CoreLParams) []
      (Lambda.LExpr.op () ⟨"Bv16.ULe", ()⟩ (some bv16ArrowTy))
      (Lambda.LMonoTy.arrow (.bitvec 16) (Lambda.LMonoTy.arrow (.bitvec 16) .bool)) := .op
  have happ1 : Lambda.LExpr.HasTypeA (T := Core.CoreLParams) []
      (.app () (Lambda.LExpr.op () ⟨"Bv16.ULe", ()⟩ (some bv16ArrowTy)) (bvc va))
      (Lambda.LMonoTy.arrow (.bitvec 16) .bool) := .app hop htva
  have hcond : Lambda.LExpr.HasTypeA (T := Core.CoreLParams) []
      (bv16ULeApp (bvc va) (bvc vb)) .bool := .app happ1 htvb
  have hite : Lambda.LExpr.HasTypeA (T := Core.CoreLParams) []
      (Lambda.LExpr.ite () (bv16ULeApp (bvc va) (bvc vb)) (bvc vt) (bvc ve))
      (Lambda.LMonoTy.bitvec 16) := .ite hcond htvt htve
  have heq : Lambda.LExpr.HasTypeA (T := Core.CoreLParams) []
      (Lambda.LExpr.eq () (bvc vr)
        (Lambda.LExpr.ite () (bv16ULeApp (bvc va) (bvc vb)) (bvc vt) (bvc ve))) .bool :=
    .eq htvr hite
  have hcap : Core.Logic.capturedExpr
      { factory := Core.Factory, store := σ, label := label,
        expr := Lambda.LExpr.eq () (.fvar () rId bv16Ty)
          (Lambda.LExpr.ite () (bv16ULeApp (.fvar () cxId bv16Ty) (.fvar () cyId bv16Ty))
            (.fvar () tId bv16Ty) (.fvar () eId bv16Ty)),
        metadata := md }
      = Lambda.LExpr.eq () (bvc vr)
          (Lambda.LExpr.ite () (bv16ULeApp (bvc va) (bvc vb)) (bvc vt) (bvc ve)) := by
    simp only [Core.Logic.capturedExpr, bv16ULeApp, Lambda.LExpr.substFvarsFromEnv,
      Lambda.Env.mk, hcx, hcy, ht, he, hr]
  have hbvc : ∀ (w : BitVec 16)
      (h : Lambda.LExpr.HasTypeA (T := Core.CoreLParams) [] (bvc w) (Lambda.LMonoTy.bitvec 16)),
      Lambda.LExpr.denote model.tcInterp model.opInterp world.freeVarVal world.tyVarVal
        .nil (bvc w) (Lambda.LMonoTy.bitvec 16) h = w := by
    intro w h
    show Lambda.LExpr.denote model.tcInterp model.opInterp world.freeVarVal world.tyVarVal
      .nil (Lambda.LExpr.const () (Lambda.LConst.bitvecConst 16 w)) (Lambda.LMonoTy.bitvec 16) h = w
    apply Lambda.denote_const
  have hcond_denote : Lambda.LExpr.denote model.tcInterp model.opInterp world.freeVarVal
      world.tyVarVal .nil (bv16ULeApp (bvc va) (bvc vb)) .bool hcond = BitVec.ule va vb := by
    simp only [bv16ULeApp]
    rw [Lambda.denote_app .nil happ1 htvb hcond, Lambda.denote_app .nil hop htva happ1,
      hbvc va htva, hbvc vb htvb, Lambda.denote_op]
    show (model.opInterp "Bv16.ULe" (bv16ArrowTy.substTyVars world.tyVarVal)) va vb
      = BitVec.ule va vb
    have hop_eq : model.opInterp "Bv16.ULe" (bv16ArrowTy.substTyVars world.tyVarVal)
        = fun (a b : BitVec 16) => BitVec.ule a b := Core.bv16ULe_opInterp model
    exact congrFun (congrFun hop_eq va) vb
  simp only [Core.Logic.DenoteBasedInterp]
  refine Or.inl ⟨trivial, ?_⟩
  rw [hcap]
  refine ⟨heq, ?_⟩
  apply Lambda.denote_eq_true .nil htvr hite heq
  rw [hbvc vr htvr, Lambda.denote_ite .nil hcond htvt htve hite, hcond_denote,
    hbvc vt htvt, hbvc ve htve, hval]
  cases hb : BitVec.ule va vb <;> rfl

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
    (hBodyEval : ∀ (σ : Core.CoreStore) (a b : BitVec 16),
      σ xId = some (bvc a) → σ yId = some (bvc b) →
      Lambda.LExpr.evalFully Core.Factory σ bodyE = some (bvc (fval a b)))
    (hPostDenote : ∀ (model : Lambda.Interp Core.Factory) (ρ' : Imperative.Env Core.Expression)
        (a b : BitVec 16), ρ'.factory = Core.Factory →
        ρ'.store xId = some (bvc a) → ρ'.store yId = some (bvc b) →
        ρ'.store resultId = some (bvc (fval a b)) →
        Core.Logic.Hoare.Procedure.postAsPredicate model proc ρ') :
    Core.Logic.Hoare.Procedure.contractTriple mmAST testParams procName := by
  refine Core.Logic.Hoare.Procedure.contractTriple_of_core_typed mmAST testParams
    procName proc [Imperative.Stmt.cmd (Imperative.CmdExt.cmd
      (Imperative.Cmd.set resultId (.det bodyE) md))] hproc hbody hChecksTyped (fun model => ?_)
  refine (Core.Logic.Hoare.block mmAST.findProcByString? testParams ?_
    (Imperative.Logic.Hoare.postWF_of_definedVars_nil _ (by
      simp [Imperative.Block.definedVars, Imperative.Stmt.definedVars,
        Imperative.HasVarsImp.definedVars, Core.Command.definedVars,
        Imperative.Cmd.definedVars]))) model
  refine Core.Logic.Hoare.cmd mmAST.findProcByString? testParams
    (Imperative.CmdExt.cmd (Imperative.Cmd.set resultId (.det bodyE) md))
    (Core.Logic.Hoare.Procedure.contractPre model proc)
    (Core.Logic.Hoare.Procedure.contractPost model proc)
    (fun _ ρ₀ σ' emitted hpre hwf hstep => ?_)
  obtain ⟨_, hfac, _, htyped⟩ := hpre
  cases hstep with
  | cmd_sem hcmd =>
    cases hcmd with
    | eval_set heval hupd _ =>
      obtain ⟨vx, hx, htx⟩ := htyped xId (.bitvec 16) (by rw [hInList]; simp)
      obtain ⟨vy, hy, hty⟩ := htyped yId (.bitvec 16) (by rw [hInList]; simp)
      change ∃ a : BitVec 16, vx = bvc a at htx
      change ∃ b : BitVec 16, vy = bvc b at hty
      obtain ⟨a, rfl⟩ := htx
      obtain ⟨b, rfl⟩ := hty
      have hbodyEval := hBodyEval ρ₀.store a b hx hy
      rw [hfac] at heval
      have hv : _ = bvc (fval a b) := Option.some.inj (heval.symm.trans hbodyEval)
      cases hupd with
      | update _ hnew hother =>
        rw [hv] at hnew
        have hx' : σ' xId = some (bvc a) := (hother xId (by decide)).trans hx
        have hy' : σ' yId = some (bvc b) := (hother yId (by decide)).trans hy
        exact ⟨True.intro, fun _ =>
          hPostDenote model { ρ₀ with store := σ' } a b hfac hx' hy' hnew⟩

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

/-- The Max16 assignment reads only `x` and `y`. -/
private theorem max_readsSub : ∀ n ∈ Imperative.HasVarsImp.readVars (P := Core.Expression)
    (Imperative.CmdExt.cmd (Imperative.Cmd.set resultId (.det maxSetExpr) maxSetMd)), n = xId ∨ n = yId := by
  native_decide
/-- The Min16 assignment reads only `x` and `y`. -/
private theorem min_readsSub : ∀ n ∈ Imperative.HasVarsImp.readVars (P := Core.Expression)
    (Imperative.CmdExt.cmd (Imperative.Cmd.set resultId (.det minSetExpr) minSetMd)), n = xId ∨ n = yId := by
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
private theorem max_post_denote (model : Lambda.Interp Core.Factory)
    (ρ' : Imperative.Env Core.Expression) (a b : BitVec 16)
    (hfac : ρ'.factory = Core.Factory)
    (hx : ρ'.store xId = some (bvc a)) (hy : ρ'.store yId = some (bvc b))
    (hr : ρ'.store resultId = some (bvc (vMax a b))) :
    Core.Logic.Hoare.Procedure.postAsPredicate model maxProc ρ' := by
  intro label check hmem hattr world
  rw [max_ensures_shape (label, check) hmem hattr, max_specE_eq, hfac]
  exact post_eq_ite_holds model world ρ'.store a b b a (vMax a b)
    xId yId yId xId resultId label check.md hx hy hy hx hr rfl

/-- Min16's conditional postcondition holds once `x, y, result` carry `a, b, min(a,b)`. -/
private theorem min_post_denote (model : Lambda.Interp Core.Factory)
    (ρ' : Imperative.Env Core.Expression) (a b : BitVec 16)
    (hfac : ρ'.factory = Core.Factory)
    (hx : ρ'.store xId = some (bvc a)) (hy : ρ'.store yId = some (bvc b))
    (hr : ρ'.store resultId = some (bvc (vMin a b))) :
    Core.Logic.Hoare.Procedure.postAsPredicate model minProc ρ' := by
  intro label check hmem hattr world
  rw [min_ensures_shape (label, check) hmem hattr, min_specE_eq, hfac]
  exact post_eq_ite_holds model world ρ'.store a b a b (vMin a b)
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
    ∃ v, Lambda.LExpr.evalFully fac σ e = some v ∧
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
      Core.Logic.Hoare.Procedure.bodyOutputsTyped mmAST.findProcByString? proc := by
  intro proc hlookup
  have hpe : proc = maxProc := (procOf_eq hlookup).symm
  subst hpe
  intro σ_entry fac σ_exit emitted hfeq hin hbody
  rw [max_body_eq] at hbody
  obtain ⟨σCmd, hcmd, hexit⟩ := Core.CoreBodyExecE.singleton_cmd_invert hbody
  obtain ⟨vx, hvx, hvtx⟩ := hin xId (Lambda.LMonoTy.bitvec 16) (by native_decide)
  obtain ⟨vy, hvy, hvty⟩ := hin yId (Lambda.LMonoTy.bitvec 16) (by native_decide)
  obtain ⟨a, rfl⟩ := hvtx
  obtain ⟨b, rfl⟩ := hvty
  obtain ⟨v, heval, hprev, hnew⟩ := set_cmd_value hcmd
  subst hfeq
  intro id ty hmem
  rw [show maxProc.header.outputs.toList = [(resultId, Lambda.LMonoTy.bitvec 16)]
    from by native_decide] at hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  obtain ⟨rfl, rfl⟩ := hmem
  have hcval := Option.some.inj (heval.symm.trans (hEval_max σ_entry a b hvx hvy))
  refine ⟨bvc (vMax a b), ?_, vMax a b, rfl⟩
  rw [hexit]
  show Imperative.projectStore σ_entry σCmd resultId = some (bvc (vMax a b))
  unfold Imperative.projectStore
  rw [ite_eq_left hprev, hnew, hcval]

/-- Every Min16 body run binds `result` to a 16-bit literal. -/
private theorem min_body_outputs :
    ∀ proc, mmAST.findProcByString? "Min16" = some proc →
      Core.Logic.Hoare.Procedure.bodyOutputsTyped mmAST.findProcByString? proc := by
  intro proc hlookup
  have hpe : proc = minProc := (procOf_eq hlookup).symm
  subst hpe
  intro σ_entry fac σ_exit emitted hfeq hin hbody
  rw [min_body_eq] at hbody
  obtain ⟨σCmd, hcmd, hexit⟩ := Core.CoreBodyExecE.singleton_cmd_invert hbody
  obtain ⟨vx, hvx, hvtx⟩ := hin xId (Lambda.LMonoTy.bitvec 16) (by native_decide)
  obtain ⟨vy, hvy, hvty⟩ := hin yId (Lambda.LMonoTy.bitvec 16) (by native_decide)
  obtain ⟨a, rfl⟩ := hvtx
  obtain ⟨b, rfl⟩ := hvty
  obtain ⟨v, heval, hprev, hnew⟩ := set_cmd_value hcmd
  subst hfeq
  intro id ty hmem
  rw [show minProc.header.outputs.toList = [(resultId, Lambda.LMonoTy.bitvec 16)]
    from by native_decide] at hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  obtain ⟨rfl, rfl⟩ := hmem
  have hcval := Option.some.inj (heval.symm.trans (hEval_min σ_entry a b hvx hvy))
  refine ⟨bvc (vMin a b), ?_, vMin a b, rfl⟩
  rw [hexit]
  show Imperative.projectStore σ_entry σCmd resultId = some (bvc (vMin a b))
  unfold Imperative.projectStore
  rw [ite_eq_left hprev, hnew, hcval]

/-- From `outputAsPredicate` and the semantic Max16 postcondition, the callee's
    `result` is exactly the unsigned maximum of its typed inputs. -/
private theorem max_result_val (model : Lambda.Interp Core.Factory)
    (ρ' : Imperative.Env Core.Expression) (va vb : BitVec 16)
    (hfac : ρ'.factory = Core.Factory)
    (hpost : Core.Logic.Hoare.Procedure.contractPost model maxProc ρ')
    (hout : Core.Logic.Hoare.Procedure.outputAsPredicate maxProc ρ')
    (hx : ρ'.store xId = some (bvc va)) (hy : ρ'.store yId = some (bvc vb)) :
    ρ'.store resultId = some (bvc (vMax va vb)) := by
  have hens : ∃ lbl chk, (lbl, chk) ∈ maxProc.spec.postconditions.toList ∧
      chk.attr = Core.Procedure.CheckAttr.Default ∧
      chk.expr = Lambda.LExpr.eq () (.fvar () resultId bv16Ty)
        (Lambda.LExpr.ite () (bv16ULeApp (.fvar () xId bv16Ty) (.fvar () yId bv16Ty))
          (.fvar () yId bv16Ty) (.fvar () xId bv16Ty)) := by
    obtain ⟨lbl, chk, hmem, hattr, hexpr⟩ := max_hens1
    exact ⟨lbl, chk, hmem, hattr, by rw [hexpr, max_specE_eq]⟩
  exact bv16_result_value model maxProc ρ' va vb vb va xId yId yId xId
    hfac hpost hout (by native_decide) hens hx hy hy hx

/-- From `outputAsPredicate` and the semantic Min16 postcondition, the callee's
    `result` is exactly the unsigned minimum of its typed inputs. -/
private theorem min_result_val (model : Lambda.Interp Core.Factory)
    (ρ' : Imperative.Env Core.Expression) (va vb : BitVec 16)
    (hfac : ρ'.factory = Core.Factory)
    (hpost : Core.Logic.Hoare.Procedure.contractPost model minProc ρ')
    (hout : Core.Logic.Hoare.Procedure.outputAsPredicate minProc ρ')
    (hx : ρ'.store xId = some (bvc va)) (hy : ρ'.store yId = some (bvc vb)) :
    ρ'.store resultId = some (bvc (vMin va vb)) := by
  have hens : ∃ lbl chk, (lbl, chk) ∈ minProc.spec.postconditions.toList ∧
      chk.attr = Core.Procedure.CheckAttr.Default ∧
      chk.expr = Lambda.LExpr.eq () (.fvar () resultId bv16Ty)
        (Lambda.LExpr.ite () (bv16ULeApp (.fvar () xId bv16Ty) (.fvar () yId bv16Ty))
          (.fvar () xId bv16Ty) (.fvar () yId bv16Ty)) := by
    obtain ⟨lbl, chk, hmem, hattr, hexpr⟩ := min_hens1
    exact ⟨lbl, chk, hmem, hattr, by rw [hexpr, min_specE_eq]⟩
  exact bv16_result_value model minProc ρ' va vb va vb xId yId xId yId
    hfac hpost hout (by native_decide) hens hx hy hx hy

/-- **Max16 meets its unchanged conditional contract with the XOR-and-mask body.** -/
theorem max16_meets_contract :
    Core.Logic.Hoare.Procedure.contractTriple mmAST testParams "Max16" :=
  bv16_set_contract "Max16" maxProc maxSetExpr maxSetMd vMax
    (by native_decide) max_body_eq (by native_decide) max_inList hEval_max
    max_post_denote

/-- **Min16 meets its unchanged conditional contract with the XOR-and-mask body.** -/
theorem min16_meets_contract :
    Core.Logic.Hoare.Procedure.contractTriple mmAST testParams "Min16" :=
  bv16_set_contract "Min16" minProc minSetExpr minSetMd vMin
    (by native_decide) min_body_eq (by native_decide) min_inList hEval_min
    min_post_denote

/-! ### Intermediate assertions threaded through the four calls -/

private def PA0 (ρ : Imperative.Env Core.Expression) : Prop :=
  ρ.factory = Core.Factory ∧
    Core.Logic.Hoare.Procedure.oldInoutAsPredicate mmRunProc ρ ∧
    Core.Logic.Hoare.Procedure.inputAsPredicate mmRunProc ρ
private def PA1 (ρ : Imperative.Env Core.Expression) : Prop :=
  ρ.factory = Core.Factory ∧ ∃ va vb : BitVec 16,
    ρ.store aId = some (bvc va) ∧ ρ.store bId = some (bvc vb) ∧
    ρ.store maxABId = some (bvc (vMax va vb))
private def PA2 (ρ : Imperative.Env Core.Expression) : Prop :=
  ρ.factory = Core.Factory ∧ ∃ va vb : BitVec 16,
    ρ.store aId = some (bvc va) ∧ ρ.store bId = some (bvc vb) ∧
    ρ.store minMaxAId = some (bvc (vMin (vMax va vb) va))
private def PA3 (ρ : Imperative.Env Core.Expression) : Prop :=
  ρ.factory = Core.Factory ∧ ∃ va vb : BitVec 16,
    ρ.store aId = some (bvc va) ∧ ρ.store minMaxAId = some (bvc (vMin (vMax va vb) va)) ∧
    ρ.store minABId = some (bvc (vMin va vb))
private def PA4 (ρ : Imperative.Env Core.Expression) : Prop :=
  ρ.factory = Core.Factory ∧ ∃ va vb : BitVec 16,
    ρ.store minMaxAId = some (bvc (vMin (vMax va vb) va)) ∧
    ρ.store maxMinAId = some (bvc (vMax (vMin va vb) va))

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

/-- The Run’s equality postcondition holds once the two output slots carry the
    absorbing min/max values. -/
private theorem run_ensures_holds (σ : Core.CoreStore) (va vb : BitVec 16)
    (hmm : σ minMaxAId = some (bvc (vMin (vMax va vb) va)))
    (hmma : σ maxMinAId = some (bvc (vMax (vMin va vb) va))) :
    Lambda.LExpr.evalFully Core.Factory σ
      (Lambda.LExpr.eq () (.fvar () maxMinAId bv16Ty) (.fvar () minMaxAId bv16Ty))
      = some (Lambda.LExpr.boolConst () true) := by
  have habs : vMax (vMin va vb) va = vMin (vMax va vb) va := by
    simp only [vMax, vMin]; exact (bv16_minmax_absorption va vb).symm
  rw [habs] at hmma
  exact Lambda.evalFully_eq_self Core.Factory σ () _ _ _ (bvc_evalFully hmma) (bvc_evalFully hmm)

/-! ### The four call triples -/

/-- The first call establishes `maxAB = max(a, b)`. -/
private theorem call1_triple :
    Core.Logic.Hoare.Triple mmAST.findProcByString? testParams PA0
      [Core.Statement.call "Max16" cArgs1 cMd1] PA1 := by
  refine bv16_call_triple "Max16" maxProc cArgs1 cMd1 maxSetMd maxSetExpr
    (.fvar () aId bv16Ty) (.fvar () bId bv16Ty) maxABId vMax PA0 PA1
    max16_meets_contract (max_body_frame) (max_body_outputs) (by native_decide) max_body_eq
    cArgs1_in cArgs1_out cArgs1_lhs max_inKeys max_inList max_outOnly max_inout max_outKeys max_noPre
    max_readsSub max_result_val ?_ (fun ρ hpre => hpre.1)
  · intro ρ₀ hpre _hwf hfac
    obtain ⟨_hfac, _hold, htyped⟩ := hpre
    obtain ⟨va, hva, hta⟩ := htyped aId (.bitvec 16) (by native_decide)
    obtain ⟨vb, hvb, htb⟩ := htyped bId (.bitvec 16) (by native_decide)
    change ∃ wa : BitVec 16, va = bvc wa at hta
    change ∃ wb : BitVec 16, vb = bvc wb at htb
    obtain ⟨wa, hva'⟩ := hta
    obtain ⟨wb, hvb'⟩ := htb
    have hwa : ρ₀.store aId = some (bvc wa) := by rw [hva, hva']
    have hwb : ρ₀.store bId = some (bvc wb) := by rw [hvb, hvb']
    refine ⟨wa, wb, bvc_evalFully hwa, bvc_evalFully hwb, ?_⟩
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
    min_readsSub min_result_val ?_ (fun ρ hpre => hpre.1)
  · intro ρ₀ hpre _hwf _hfac
    obtain ⟨hfac, va, vb, ha, hb, hmaxAB⟩ := hpre
    refine ⟨vMax va vb, va, bvc_evalFully hmaxAB, bvc_evalFully ha, ?_⟩
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
    min_readsSub min_result_val ?_ (fun ρ hpre => hpre.1)
  · intro ρ₀ hpre _hwf _hfac
    obtain ⟨hfac, va, vb, ha, hb, hmm⟩ := hpre
    refine ⟨va, vb, bvc_evalFully ha, bvc_evalFully hb, ?_⟩
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
    max_readsSub max_result_val ?_ (fun ρ hpre => hpre.1)
  · intro ρ₀ hpre _hwf _hfac
    obtain ⟨hfac, va, vb, ha, hmm, hminAB⟩ := hpre
    refine ⟨vMin va vb, va, bvc_evalFully hminAB, bvc_evalFully ha, ?_⟩
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
    PA0 PA0 (fun _ ρ₀ σ' emitted hpre _ hstep => ?_)
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
    PA2 PA2 (fun _ ρ₀ σ' emitted hpre _ hstep => ?_)
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

/-- In any denotational world, an equality of two variables bound to the same
    16-bit literal holds: the captured expression substitutes to `w == w`, whose
    denotation is `true`. -/
private theorem eq_fvars_holds
    (model : Lambda.Interp Core.Factory) (world : Core.Logic.DenoteValuation model)
    (σ : Core.CoreStore) (id1 id2 : Core.Expression.Ident) (w : BitVec 16)
    (label : Core.CoreLabel) (md : Imperative.MetaData Core.Expression)
    (h1 : σ id1 = some (bvc w)) (h2 : σ id2 = some (bvc w)) :
    (Core.Logic.DenoteBasedInterp model).holds world
      { factory := Core.Factory, store := σ, label := label,
        expr := Lambda.LExpr.eq () (.fvar () id1 bv16Ty) (.fvar () id2 bv16Ty),
        metadata := md } := by
  have hty : Lambda.LExpr.HasTypeA (T := Core.CoreLParams) [] (bvc w) (Lambda.LMonoTy.bitvec 16) :=
    Lambda.LExpr.HasTypeA.const
  have hcap : Core.Logic.capturedExpr
      { factory := Core.Factory, store := σ, label := label,
        expr := Lambda.LExpr.eq () (.fvar () id1 bv16Ty) (.fvar () id2 bv16Ty),
        metadata := md }
      = Lambda.LExpr.eq () (bvc w) (bvc w) := by
    simp only [Core.Logic.capturedExpr, Lambda.LExpr.substFvarsFromEnv, Lambda.Env.mk, h1, h2]
  simp only [Core.Logic.DenoteBasedInterp]
  refine Or.inl ⟨trivial, ?_⟩
  rw [hcap]
  exact ⟨Lambda.LExpr.HasTypeA.eq hty hty,
    Lambda.denote_eq_true .nil hty hty (Lambda.LExpr.HasTypeA.eq hty hty) rfl⟩

/-- The final call facts imply the Run’s sole postcondition. -/
private theorem run_post_of_PA4 (model : Lambda.Interp Core.Factory) :
    ∀ ρ, PA4 ρ → Core.Logic.Hoare.Procedure.contractPost model mmRunProc ρ := by
  intro ρ hpre
  obtain ⟨hfac, va, vb, hmm, hmma⟩ := hpre
  have habs : vMax (vMin va vb) va = vMin (vMax va vb) va := by
    simp only [vMax, vMin]; exact (bv16_minmax_absorption va vb).symm
  intro label check hmem hattr world
  rw [mm_run_ensures_shape (label, check) hmem hattr, hfac]
  exact eq_fvars_holds model world ρ.store maxMinAId minMaxAId (vMin (vMax va vb) va)
    label check.md (habs ▸ hmma) hmm

/-- The unsigned 16-bit-vector Run meets its contract: local intermediates
compute two equal nested min/max compositions in its output parameters. -/
theorem mm_run_meets_contract :
    Core.Logic.Hoare.Procedure.contractTriple mmAST testParams "Run" := by
  refine Core.Logic.Hoare.Procedure.contractTriple_of_core_typed mmAST testParams "Run"
    mmRunProc [maxABInitStmt, Core.Statement.call "Max16" cArgs1 cMd1,
      Core.Statement.call "Min16" cArgs2 cMd2, minABInitStmt,
      Core.Statement.call "Min16" cArgs3 cMd3, Core.Statement.call "Max16" cArgs4 cMd4]
    (by native_decide) mm_run_body_eq (by native_decide) (fun model => ?_)
  have hpre : ∀ ρ, Core.Logic.Hoare.Procedure.contractPre model mmRunProc ρ → PA0 ρ :=
    fun _ hc => ⟨hc.2.1, hc.2.2.1, hc.2.2.2⟩
  refine (Core.Logic.Hoare.consequence mmAST.findProcByString? testParams
    (Core.Logic.Hoare.block mmAST.findProcByString? testParams ?_ (mm_run_PA4_postWF))
    hpre (run_post_of_PA4 model)) model
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
