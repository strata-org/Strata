/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Languages.Core.Tests.Logic.HoareAfterSupport
import Strata.Transform.NondetElimCoreCorrect

open Imperative
open StrataDDM (Program)

namespace Strata.HoareAfterNondetElimTest

open HoareAfterSupport

/-- The program.  It comes first in the file: the translation records the byte offsets of its
    statements in their metadata, which `walkBody` spells out with `loc`, so an edit above it
    moves them. -/
private def walkPgm : Program :=
#strata
program Core;

procedure Walk(n : int, out r : int)
spec {
  requires int.ge(n, 0);
  ensures int.ge(r, 0);
}
{
  r := n;
  while * {
    if * {
      if (int.gt(r, 0)) {
        r := int.sub(r, 1);
      }
    } else {
      r := int.add(r, 2);
    }
  }
};
#end

private def walkPgmAST : Core.Program := cstToAST walkPgm

private abbrev π : String → Option Core.Procedure := walkPgmAST.findProcByString?

/-! # The contract of a nondeterministic walk, proved on its deterministic encoding

`Walk`'s loop runs an arbitrary number of times, and each iteration either steps `r` down
while it is positive or steps it up by two.  The structural rules of `Core.Logic.Hoare` read
only deterministic guards.  The Core pass `Core.NondetElim.nondetElim` replaces each
nondeterministic guard by a fresh Boolean, havocked where the choice is made:

```
r := n;
var $__ndelim_loop$_0 : bool;
while ($__ndelim_loop$_0) {
  var $__ndelim_ite$_1 : bool;
  if ($__ndelim_ite$_1) { if (int.gt(r, 0)) { r := int.sub(r, 1); } }
  else { r := int.add(r, 2); }
  havoc $__ndelim_loop$_0;
}
```

The while rule with the invariant `r ≥ 0` proves the contract of this body, never reading the
fresh guards.  `Core.NondetElim.triple` carries the triple back to the nondeterministic body,
at gate parameters reserving the prefixes of the fresh guards: the postcondition reads only
`r`, which is not a generated name, so it survives dropping the guard bindings.

The translated body is spelled out as the closed term `walkBody`; the facts about the pass's
output on it are decided by the kernel (`decide +kernel`).  The facts that bind the translated
program to it (`walk_body_eq`, `walk_decl`, `walk_out`'s run, `walk_pre_expr`,
`walk_post_expr`, the input typing, and the procedure lookup and `contractChecksTyped` premises
of `walk_meets_contract`) use `native_decide`: the translation is `partial`, so the kernel
cannot reduce it.
-/

/-- Gate parameters of the source: the prefixes of the fresh guards reserved. -/
private def srcParams : Core.Logic.InitEnvWFParams :=
  testParams.extend Imperative.NondetElim.prefixesReserved

private def walkProc : Core.Procedure := (π "Walk").get!

private def nId : Core.Expression.Ident := ⟨"n", ()⟩
private def rId : Core.Expression.Ident := ⟨"r", ()⟩

/-- `int.gt(r, 0)`. -/
private abbrev gtE : Core.Expression.Expr := .app Core.valueLoc (.app Core.valueLoc Core.intGtOp (v rId)) (.intConst Core.valueLoc 0)
/-- `int.sub(r, 1)`. -/
private abbrev subE : Core.Expression.Expr :=
  .app Core.valueLoc (.app Core.valueLoc Core.intSubOp (v rId)) (.intConst Core.valueLoc 1)
/-- `int.add(r, 2)`. -/
private abbrev addE : Core.Expression.Expr :=
  .app Core.valueLoc (.app Core.valueLoc Core.intAddOp (v rId)) (.intConst Core.valueLoc 2)

/-- The inner `if`. -/
private abbrev innerIte : Core.Statement :=
  .ite (.det gtE) [Core.Statement.set rId subE (loc 731 750)] [] (loc 703 758)

/-- The step up. -/
private abbrev stepUp : Core.Statement := Core.Statement.set rId addE (loc 778 797)

/-- The metadata of the nondeterministic `if` and of the loop. -/
private abbrev mdOut : MetaData Core.Expression := loc 690 803
private abbrev mdL : MetaData Core.Expression := loc 676 807

/-- The translated body. -/
private abbrev walkBody : Core.Statements :=
  [Core.Statement.set rId (v nId) (loc 666 673),
   .loop .nondet none [] [.ite .nondet [innerIte] [stepUp] mdOut] mdL]

/-- The translated body really is the assignment followed by the nondeterministic loop. -/
private theorem walk_body_eq : walkProc.body = .structured walkBody := by native_decide

/-! ## The deterministic encoding -/

/-- The fresh guard of the loop. -/
private abbrev gLoop : Core.Expression.Ident :=
  HasIdent.ident (P := Core.Expression) "$__ndelim_loop$_0"

/-- The fresh guard of the nondeterministic `if`. -/
private abbrev gIte : Core.Expression.Ident :=
  HasIdent.ident (P := Core.Expression) "$__ndelim_ite$_1"

/-- The body of the encoded loop. -/
private abbrev tgtLoopBody : Core.Statements :=
  [.cmd (HasInit.init gIte HasBool.boolTy .nondet mdOut)] ++
    ([.ite (.det (HasFvar.mkTypedFvar gIte HasBool.boolTy)) [innerIte] [stepUp] mdOut] ++
      [.cmd (HasHavoc.havoc gLoop mdL)])

/-- The statements after `r := n` of the encoded body. -/
private abbrev tgtRest : Core.Statements :=
  [.cmd (HasInit.init gLoop HasBool.boolTy .nondet mdL),
   .loop (.det (HasFvar.mkTypedFvar gLoop HasBool.boolTy)) none [] tgtLoopBody mdL]

/-- The encoded body. -/
private abbrev walkTgt : Core.Statements :=
  [Core.Statement.set rId (v nId) (loc 666 673)] ++ tgtRest

/-- Nondeterminism elimination turns the body into `walkTgt`. -/
private theorem walk_nondetElim : Imperative.Block.nondetElim walkBody = walkTgt := by
  decide +kernel

/-- The metadata of the declaration of the procedure. -/
private def walkDeclMd : MetaData Core.Expression :=
  match walkPgmAST.decls[0]? with
  | some (Core.Decl.proc _ md) => md
  | _ => default

/-- The procedure is the first declaration of the program. -/
private theorem walk_decl : walkPgmAST.decls[0]? = some (.proc walkProc walkDeclMd) := by
  native_decide

/-- A run of the Core pass on the program. -/
private def walkRun := Core.NondetElim.nondetElim walkPgmAST Core.Transform.CoreTransformState.emp

/-- The program the run returns. -/
private def walkOut : Core.Program := match walkRun.1 with
  | .ok r => r.2
  | .error _ => default

/-- **The Core pass encodes the body.**  The run of `Core.NondetElim.nondetElim` on the
    program succeeds, and the program it returns has the procedure with the body `walkTgt`. -/
theorem walk_out : (∃ c σ', walkRun = (.ok (c, walkOut), σ')) ∧
    Core.Decl.proc { walkProc with body := .structured walkTgt } walkDeclMd ∈ walkOut.decls := by
  have h : (match walkRun.1 with | .ok _ => true | .error _ => false) = true := by
    native_decide
  have hrun : ∃ c σ', walkRun = (.ok (c, walkOut), σ') := by
    unfold walkOut
    revert h
    generalize walkRun = r
    obtain ⟨_ | ⟨c, q⟩, σ'⟩ := r
    · intro h; cases h
    · intro _; exact ⟨c, σ', rfl⟩
  refine ⟨hrun, ?_⟩
  obtain ⟨c, σ', hr⟩ := hrun
  have hphase := (Core.NondetElim.nondetElimPipelinePhase_over.{0} (π := π)
    (s := Core.Transform.CoreTransformState.emp) (s' := σ') (changed := c)
    (by rw [Core.NondetElim.nondetElimPipelinePhase_ok]; exact hr)
    (show Core.Program.allStatements Core.Statements.noCalls walkPgmAST = true by native_decide)
    (List.mem_of_getElem? walk_decl) walk_body_eq).1
  rwa [walk_nondetElim] at hphase

/-! ## Evaluating the conditions -/

/-- The precondition is `int.ge(n, 0)`. -/
private theorem walk_pre_expr : ∀ lc ∈ walkProc.spec.preconditions.toList, lc.2.expr = ge0 nId :=
  List.forall_of_all_decide (by native_decide)

/-- The postcondition is `int.ge(r, 0)`. -/
private theorem walk_post_expr :
    ∀ lc ∈ walkProc.spec.postconditions.toList, lc.2.expr = ge0 rId :=
  List.forall_of_all_decide (by native_decide)

/-- `x` holds the integer `k`. -/
private abbrev Holds (x : Core.Expression.Ident) (k : Int) (ρ : Env Core.Expression) : Prop :=
  ρ.store x = some (intOf ρ.factory k)

section Eval

variable {f : Core.Expression.Factory} (hf : f.factory = Core.Factory) {σ : Core.CoreStore}
include hf

/-- With `r ↦ k`, the inner guard `int.gt(r, 0)` evaluates to `k > 0`. -/
private theorem gt_eval {k : Int} (hr : σ rId = some (intOf f k)) :
    Core.Expression.eval f σ gtE =
      some (Lambda.SemValue.ofBool f.model.tcInterp (decide (k > 0))) :=
  Core.eval_intGt (hf ▸ Core.coreFactory_intGt) (Core.eval_fvar_int f hr)
    (Core.eval_intConst f σ 0)

/-- With `r ↦ k`, `int.sub(r, 1)` evaluates to `k - 1`. -/
private theorem sub_eval {k : Int} (hr : σ rId = some (intOf f k)) :
    Core.Expression.eval f σ subE = some (intOf f (k - 1)) :=
  Core.eval_intSub (hf ▸ Core.coreFactory_intSub) (Core.eval_fvar_int f hr)
    (Core.eval_intConst f σ 1)

/-- With `r ↦ k`, `int.add(r, 2)` evaluates to `k + 2`. -/
private theorem add_eval {k : Int} (hr : σ rId = some (intOf f k)) :
    Core.Expression.eval f σ addE = some (intOf f (k + 2)) :=
  Core.eval_intAdd (hf ▸ Core.coreFactory_intAdd) (Core.eval_fvar_int f hr)
    (Core.eval_intConst f σ 2)

end Eval

/-! ## Rules for the commands of the encoding -/

/-- A precondition reading only the factory and `r` survives a store change that keeps `r`. -/
private abbrev OnR (Q : Env Core.Expression → Prop) : Prop :=
  ∀ ρ σ, ρ.store rId = σ rId → Q ρ → Q { ρ with store := σ }

/-- A nondeterministic `init` of a name other than `r` keeps a precondition reading only `r`. -/
private theorem init_nondet_keep (x : Core.Expression.Ident) (hx : x ≠ rId) (ty : Lambda.LTy)
    (md : MetaData Core.Expression) {Q : Env Core.Expression → Prop} (hQ : OnR Q) :
    Core.Logic.Hoare.Triple π testParams Q [.cmd (HasInit.init x ty .nondet md)] Q :=
  Core.Logic.Hoare.cmd π testParams _ Q Q fun ρ₀ σ' _ hρ _ hstep =>
    have ⟨_, _, _, _, hoth, he⟩ := EvalCmdE.init_nondet_inv (evalCmdExtE_cmd_iff.mp hstep)
    ⟨by rw [he]; trivial, fun _ => hQ ρ₀ σ' (hoth rId hx).symm hρ⟩

/-- A havoc of a name other than `r` keeps a precondition reading only `r`. -/
private theorem havoc_keep (x : Core.Expression.Ident) (hx : x ≠ rId)
    (md : MetaData Core.Expression) {Q : Env Core.Expression → Prop} (hQ : OnR Q) :
    Core.Logic.Hoare.Triple π testParams Q [.cmd (HasHavoc.havoc x md)] Q :=
  Core.Logic.Hoare.cmd π testParams _ Q Q fun ρ₀ σ' _ hρ _ hstep =>
    have ⟨_, _, _, hoth, he⟩ := EvalCmdE.set_nondet_inv (evalCmdExtE_cmd_iff.mp hstep)
    ⟨by rw [he]; trivial, fun _ => hQ ρ₀ σ' (hoth rId hx).symm hρ⟩

/-! ## The triple of the encoded body -/

/-- The loop invariant: `r` holds a non-negative integer. -/
private abbrev Inv (ρ : Env Core.Expression) : Prop :=
  Pinned ρ ∧ ∃ k, Holds rId k ρ ∧ 0 ≤ k

/-- `Inv` reads only the factory and `r`. -/
private theorem inv_onR : OnR Inv := fun _ _ he ⟨hp, k, hr, hk⟩ =>
  ⟨hp, k, (show _ = _ from he.symm.trans hr), hk⟩

/-- The fresh guard of the loop is not `r`. -/
private theorem gLoop_ne_r : gLoop ≠ rId := by decide
/-- The fresh guard of the nondeterministic `if` is not `r`. -/
private theorem gIte_ne_r : gIte ≠ rId := by decide

/-- `Inv` survives leaving a block whose body does not define `r`. -/
private theorem inv_postWF (ss : Core.Statements)
    (h : rId ∉ Block.definedVars (P := Core.Expression) (C := Core.Command) ss true) :
    Imperative.Logic.Hoare.PostWF ss Inv := fun ρ hρ =>
  inv_onR ρ _ (by simp only [Imperative.dropVars, ite_eq_right h]) hρ

/-- The nondeterministic `if` of an iteration keeps `Inv`, whichever branch it takes. -/
private theorem choice_triple {Pre : Env Core.Expression → Prop} (hpre : ∀ ρ, Pre ρ → Inv ρ) :
    Core.Logic.Hoare.Triple π testParams Pre [.ite (.det (HasFvar.mkTypedFvar gIte
      HasBool.boolTy)) [innerIte] [stepUp] mdOut] Inv := by
  refine Core.Logic.Hoare.ite π testParams ?_ ?_
    (inv_postWF _ (by decide +kernel)) (inv_postWF _ (by decide +kernel))
  · -- Step down while positive.
    refine Core.Logic.Hoare.ite π testParams ?_ ?_
      (inv_postWF _ (by decide +kernel)) (inv_postWF _ (by decide +kernel))
    · refine Core.Logic.Hoare.set π testParams _ _ _ _ _
        (fun ρ₀ σ' w ⟨⟨hρ, _⟩, hg⟩ hev hup => ?_)
      obtain ⟨hp, k, hr, _⟩ := hpre ρ₀ hρ
      rw [gt_eval hp hr] at hg
      have hk : k > 0 := of_decide_eq_true (Lambda.SemValue.ofBool_injective (Option.some.inj hg))
      rw [sub_eval hp hr] at hev
      cases hev
      cases hup with
      | update _ hnew _ => exact ⟨hp, k - 1, hnew, by omega⟩
    · exact Core.Logic.Hoare.consequence π testParams
        (Imperative.Logic.Hoare.skip_block (Core.EvalCommandE π) Core.Logic.BlockInitEnvWF
          testParams _)
        (fun _ h => h) (fun ρ ⟨⟨hρ, _⟩, _⟩ => hpre ρ hρ)
  · -- Step up by two.
    refine Core.Logic.Hoare.set π testParams _ _ _ _ _ (fun ρ₀ σ' w ⟨hρ, _⟩ hev hup => ?_)
    obtain ⟨hp, k, hr, hk⟩ := hpre ρ₀ hρ
    rw [add_eval hp hr] at hev
    cases hev
    cases hup with
    | update _ hnew _ => exact ⟨hp, k + 2, hnew, by omega⟩

/-- An iteration of the encoded loop keeps `Inv`. -/
private theorem loopBody_triple :
    Core.Logic.Hoare.Triple π testParams
      (fun ρ => Inv ρ ∧ Core.Expression.eval ρ.factory ρ.store
        (HasFvar.mkTypedFvar gLoop HasBool.boolTy) = some (HasBool.ttVal ρ.factory))
      tgtLoopBody Inv := by
  refine Core.Logic.Hoare.consequence π testParams (Pre := Inv) ?_ (fun _ h => h.1) (fun _ h => h)
  refine Core.Logic.Hoare.seq π testParams (Mid := Inv)
    (init_nondet_keep _ gIte_ne_r _ _ inv_onR) ?_ (by covered)
  exact Core.Logic.Hoare.seq π testParams (Mid := Inv) (choice_triple fun _ h => h)
    (havoc_keep _ gLoop_ne_r _ inv_onR) (by covered)

/-- **The encoded body establishes `Inv`.** -/
private theorem walkTgt_triple :
    Core.Logic.Hoare.Triple π testParams
      (Core.Logic.Hoare.Procedure.contractPre Core.Factory walkProc) walkTgt Inv := by
  refine Core.Logic.Hoare.of_storeWF_pre π _ (Core.Logic.Hoare.consequence π testParams
    (Pre := fun ρ => Pinned ρ ∧ ∃ k, Holds nId k ρ ∧ 0 ≤ k) ?_
    (fun _ ⟨h, hwf⟩ => ⟨h.2.1, nonneg_of_pre h hwf (by native_decide) walk_pre_expr
      (by native_decide)⟩) (fun _ h => h))
  refine Core.Logic.Hoare.seq π testParams (Mid := Inv) ?_ ?_ (by covered)
  · refine Core.Logic.Hoare.set π testParams _ _ _ _ _
      (fun ρ₀ σ' w ⟨hp, k, hn, hk⟩ hev hup => ?_)
    rw [Core.eval_fvar_int _ hn] at hev
    cases hev
    cases hup with
    | update _ hnew _ => exact ⟨hp, k, hnew, hk⟩
  refine Core.Logic.Hoare.seq π testParams (Mid := Inv)
    (init_nondet_keep _ gLoop_ne_r _ _ inv_onR) ?_ (by covered)
  exact Core.Logic.Hoare.consequence π testParams
    (Core.Logic.Hoare.while_rule π testParams loopBody_triple (by covered)
      (inv_postWF _ (by decide +kernel)))
    (fun _ h => h) (fun _ h => h.1)

/-! ## Back to the nondeterministic body -/

/-- `r` is not a name the pass generates. -/
private theorem r_not_generated (name : String) (h : Imperative.NondetElim.isGeneratedName name) :
    HasIdent.ident (P := Core.Expression) name ≠ rId := by
  intro heq
  have hname : name = "r" := congrArg (·.name) heq
  subst hname
  rcases (Imperative.NondetElim.isGeneratedName_iff _).1 h with ⟨σ, h⟩ | ⟨σ, h⟩ <;>
  · rw [StringGenState.gen_eq] at h
    have hl := congrArg String.length h
    simp [Imperative.NondetElim.prefixIte, Imperative.NondetElim.prefixLoop] at hl
    have h1 : ("r" : String).length = 1 := by decide
    have h15 : ("$__ndelim_ite$_" : String).length = 15 := by decide
    have h16 : ("$__ndelim_loop$_" : String).length = 16 := by decide
    omega

/-- `Inv` survives dropping the bindings of the generated guards. -/
private theorem inv_of_extends {ρ' ρ'' : Env Core.Expression}
    (h : Env.ExtendsWith
      (Imperative.IdentOfStringKind Imperative.NondetElim.isGeneratedName) ρ' ρ'')
    (hx : Inv ρ'') : Inv ρ' := by
  obtain ⟨hf, hagree, hdom⟩ := h
  obtain ⟨hp, k, hr, hk⟩ := hx
  have hsome : (ρ'.store rId).isSome = true := by
    rcases hdom rId (by rw [hr]; rfl) with h | ⟨name, hname, heq⟩
    · exact h
    · exact absurd heq.symm (r_not_generated name hname)
  have heq := hagree rId fun y hy => by rw [List.mem_singleton.mp hy]; exact hsome
  refine ⟨?_, k, ?_, hk⟩
  · change ρ'.factory.factory = _
    rw [hf]
    exact hp
  · change ρ'.store rId = some (intOf ρ'.factory k)
    rw [heq, hr, hf]

/-- **`Walk` meets its contract**, from the triple of the encoded body
    (`Core.NondetElim.triple`), inside the procedure block. -/
theorem walk_meets_contract :
    Core.Logic.Hoare.Procedure.contractTriple walkPgmAST srcParams "Walk" := by
  have hfactory : walkPgmAST.factoryBeforeProcedure "Walk" = Core.Factory :=
    Core.Program.factoryBeforeProcedure_eq_core_of_noFunctions (by decide +kernel)
  rw [Core.Logic.Hoare.Procedure.contractTriple, hfactory]
  refine ⟨walkProc, by native_decide, by native_decide, ?_⟩
  rw [walk_body_eq]
  have hvars : Block.definedVars (C := Core.Command) walkBody false ++
      Block.modifiedVars (C := Core.Command) walkBody = [rId, rId, rId] := by decide +kernel
  have hsrc := Core.NondetElim.triple π testParams (ss := walkBody)
    (by simp [Core.Statements.noCalls, Block.allSubstmts_cons, Stmt.allSubstmts_loop,
      Stmt.allSubstmts_ite, Stmt.allSubstmts_cmd, Block.allSubstmts_nil,
      Core.Statement.isNotCall])
    (fun name hname hmem => by
      rw [hvars] at hmem
      simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hmem
      exact r_not_generated name hname hmem)
    (fun _ hp _ _ => by simp [testParams] at hp)
    (fun _ h => h.2.1) (fun _ _ h hx => inv_of_extends h hx)
    (walk_nondetElim ▸ walkTgt_triple)
  refine Core.Logic.Hoare.consequence π srcParams
    (Core.Logic.Hoare.block π srcParams hsrc
      (Imperative.Logic.Hoare.postWF_of_definedVars_nil _ (by decide +kernel)))
    (fun _ h => h) (fun _ ⟨hp, _, hr, hk⟩ => post_ge0 walk_post_expr hp hr hk)

end Strata.HoareAfterNondetElimTest
