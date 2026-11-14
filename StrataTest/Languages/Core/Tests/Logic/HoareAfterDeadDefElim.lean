/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import StrataTest.Languages.Core.Tests.Logic.HoareAfterSupport
import Strata.Transform.DeadDefElimCoreCorrect

open Imperative
open StrataDDM (Program)

namespace Strata.HoareAfterDeadDefElimTest

open HoareAfterSupport

/-- The program.  It comes first in the file: the translation records the byte offsets of its
    statements in their metadata, which `maxBody` spells out with `loc`, so an edit above it
    moves them. -/
private def maxPgm : Program :=
#strata
program Core;

procedure Max(a : int, b : int, out m : int)
spec {
  ensures int.ge(m, a);
  ensures int.ge(m, b);
}
{
  var d : int := int.sub(a, b);
  var sq : int := int.mul(d, d);
  if (int.ge(a, b)) {
    m := a;
  } else {
    m := b;
  }
};
#end

private def maxPgmAST : Core.Program := cstToAST maxPgm

private abbrev π : String → Option Core.Procedure := maxPgmAST.findProcByString?

/-! # A contract proved on the body without its dead definitions

No statement of `Max`'s body reads `sq`, and once `sq` is gone none reads `d`.  The Core pass
`Core.DeadDefElim.deadDefElimProgram` erases both in one backward sweep, leaving

```
if (int.ge(a, b)) { m := a; } else { m := b; }
```

whose triple follows from the `ite` and `set` rules.  `Core.DeadDefElim.deadDefElim_triple`
carries it back to the original body: the postcondition, which reads only `a`, `b` and `m`,
survives putting back the erased bindings (`DDOut`).  The block rule wraps the body in the
procedure block, whose exit drops `d` and `sq`, which the postcondition does not read.

The translated body is spelled out as the closed term `maxBody`; the facts about the pass's
output on it are decided by the kernel (`decide +kernel`).  The facts that bind the translated
procedure to it (`max_body_eq`, `max_decl`, `max_post_expr`, and the procedure lookup and
`contractChecksTyped` premises of `max_meets_contract`) use `native_decide`: the translation is
`partial`, so the kernel cannot reduce it.
-/

private def maxProc : Core.Procedure := (π "Max").get!

private def aId : Core.Expression.Ident := ⟨"a", ()⟩
private def bId : Core.Expression.Ident := ⟨"b", ()⟩
private def mId : Core.Expression.Ident := ⟨"m", ()⟩
private def dId : Core.Expression.Ident := ⟨"d", ()⟩
private def sqId : Core.Expression.Ident := ⟨"sq", ()⟩

/-- `int.ge(x, y)` of two variables. -/
private abbrev geE (x y : Core.Expression.Ident) : Core.Expression.Expr :=
  .app Core.valueLoc (.app Core.valueLoc Core.intGeOp (v x)) (v y)

/-- The `if` of the body. -/
private abbrev maxIte : Core.Statement :=
  .ite (.det (geE aId bId)) [Core.Statement.set mId (v aId) (loc 762 769)]
    [Core.Statement.set mId (v bId) (loc 785 792)] (loc 738 796)

/-- The translated body. -/
private abbrev maxBody : Core.Statements :=
  [Core.Statement.init dId intLTy (.det (.app Core.valueLoc (.app Core.valueLoc Core.intSubOp (v aId)) (v bId)))
      (loc 673 702),
   Core.Statement.init sqId intLTy (.det (.app Core.valueLoc (.app Core.valueLoc Core.intMulOp (v dId)) (v dId)))
      (loc 705 735),
   maxIte]

/-- The translated body really is the two definitions followed by the `if`. -/
private theorem max_body_eq : maxProc.body = .structured maxBody := by native_decide

/-- Erasing the unread definitions leaves the `if` alone. -/
private theorem max_dde : Imperative.DeadDefElim.deadDefElim [] maxBody = [maxIte] := by
  decide +kernel

/-- The metadata of the declaration of the procedure. -/
private def maxDeclMd : MetaData Core.Expression :=
  match maxPgmAST.decls[0]? with
  | some (Core.Decl.proc _ md) => md
  | _ => default

/-- The procedure is the first declaration of the program. -/
private theorem max_decl : maxPgmAST.decls[0]? = some (.proc maxProc maxDeclMd) := by
  native_decide

/-- **The Core pass leaves the `if` alone as the procedure body.**  A run of
    `deadDefElimProgram` on the program returns it with the body `[maxIte]`. -/
theorem max_run_out :
    ∃ b out s', (Core.DeadDefElim.deadDefElimProgram maxPgmAST).run
        Core.Transform.CoreTransformState.emp = (.ok (b, out), s') ∧
      Core.Decl.proc { maxProc with body := .structured [maxIte] } maxDeclMd ∈ out.decls := by
  refine ⟨_, _, _, rfl, ?_⟩
  have h := (Core.DeadDefElim.deadDefElimProgram_over (s := Core.Transform.CoreTransformState.emp)
    rfl (List.mem_of_getElem? max_decl) max_body_eq).1
  rwa [Imperative.DeadDefElim.deadDefElimH_eq (P := Core.Expression), max_dde] at h

/-! ## Evaluating the conditions -/

/-- The two postconditions are `int.ge(m, a)` and `int.ge(m, b)`. -/
private theorem max_post_expr :
    ∀ lc ∈ maxProc.spec.postconditions.toList, lc.2.expr = geE mId aId ∨ lc.2.expr = geE mId bId :=
  List.forall_of_all_decide (by native_decide)

/-- `x` holds the integer `n`. -/
private abbrev Holds (x : Core.Expression.Ident) (n : Int) (ρ : Env Core.Expression) : Prop :=
  ρ.store x = some (intOf ρ.factory n)

/-- With `x ↦ p` and `y ↦ q`, `int.ge(x, y)` evaluates to `p ≥ q`. -/
private theorem ge_eval {f : Core.Expression.Factory} (hf : f.factory = Core.Factory)
    {σ : Core.CoreStore} {x y : Core.Expression.Ident} {p q : Int}
    (hx : σ x = some (intOf f p)) (hy : σ y = some (intOf f q)) :
    Core.Expression.eval f σ (geE x y) =
      some (Lambda.SemValue.ofBool f.model.tcInterp (decide (p ≥ q))) :=
  Core.eval_intGe (hf ▸ Core.coreFactory_intGe) (Core.eval_fvar_int f hx)
    (Core.eval_fvar_int f hy)

/-! ## The triple of the body without dead definitions -/

/-- Before the `if`: `a` and `b` hold integers. -/
private abbrev Entry (ρ : Env Core.Expression) : Prop :=
  Pinned ρ ∧ ∃ p q, Holds aId p ρ ∧ Holds bId q ρ

/-- After the `if`: `m` holds an integer at least those of `a` and `b`. -/
private abbrev Exit (ρ : Env Core.Expression) : Prop :=
  Pinned ρ ∧ ∃ p q r, Holds aId p ρ ∧ Holds bId q ρ ∧ Holds mId r ρ ∧ p ≤ r ∧ q ≤ r

/-- `m` is not `a`. -/
private theorem a_ne_m : mId ≠ aId := by decide
/-- `m` is not `b`. -/
private theorem b_ne_m : mId ≠ bId := by decide

/-- **The body without its dead definitions establishes `Exit`.** -/
private theorem maxTgt_triple :
    Core.Logic.Hoare.Triple π testParams
      (Core.Logic.Hoare.Procedure.contractPre Core.Factory maxProc) [maxIte] Exit := by
  refine Core.Logic.Hoare.of_storeWF_pre π _
    (Core.Logic.Hoare.consequence π testParams (Pre := Entry) ?_
    (fun ρ ⟨⟨_, hp, _, hin⟩, hwf⟩ =>
      have ⟨p, ha⟩ := Core.Logic.Hoare.Procedure.inputAsPredicate_int hwf hin aId (by native_decide)
      have ⟨q, hb⟩ := Core.Logic.Hoare.Procedure.inputAsPredicate_int hwf hin bId (by native_decide)
      ⟨hp, p, q, ha, hb⟩) (fun _ h => h))
  refine Core.Logic.Hoare.ite π testParams ?_ ?_
    (Imperative.Logic.Hoare.postWF_of_definedVars_nil _ (by decide +kernel))
    (Imperative.Logic.Hoare.postWF_of_definedVars_nil _ (by decide +kernel))
  · -- `a ≥ b`: `m := a`.
    refine Core.Logic.Hoare.set π testParams _ _ _ _ _
      (fun ρ₀ σ' w ⟨⟨hp, p, q, ha, hb⟩, hg⟩ hev hup => ?_)
    rw [ge_eval hp ha hb] at hg
    have hpq : p ≥ q := of_decide_eq_true (Lambda.SemValue.ofBool_injective (Option.some.inj hg))
    rw [Core.eval_fvar_int _ ha] at hev
    cases hev
    cases hup with
    | update _ hnew hoth =>
      exact ⟨hp, p, q, p, (hoth _ a_ne_m).trans ha, (hoth _ b_ne_m).trans hb, hnew,
        Int.le_refl p, hpq⟩
  · -- `a < b`: `m := b`.
    refine Core.Logic.Hoare.set π testParams _ _ _ _ _
      (fun ρ₀ σ' w ⟨⟨hp, p, q, ha, hb⟩, hg⟩ hev hup => ?_)
    rw [ge_eval hp ha hb] at hg
    have hpq : ¬ p ≥ q :=
      of_decide_eq_false (Lambda.SemValue.ofBool_injective (Option.some.inj hg))
    rw [Core.eval_fvar_int _ hb] at hev
    cases hev
    cases hup with
    | update _ hnew hoth =>
      exact ⟨hp, p, q, q, (hoth _ a_ne_m).trans ha, (hoth _ b_ne_m).trans hb, hnew,
        by omega, Int.le_refl q⟩

/-! ## Back to the body with its dead definitions -/

/-- A binding of the store of the output is a binding of the source's store. -/
private theorem holds_of_ddOut {ρ' ρ'' : Env Core.Expression} (h : Core.DeadDefElim.DDOut ρ' ρ'')
    {x : Core.Expression.Ident} {n : Int} (hx : Holds x n ρ'') : Holds x n ρ' := by
  obtain ⟨hf, hagree⟩ := h
  have hd : SemanticStore.varsDefined (· ∈ [x]) ρ''.store := fun y hy => by
    rw [List.mem_singleton.mp hy, hx]; rfl
  change ρ'.store x = some (intOf ρ'.factory n)
  rw [← hagree x hd, hx, hf]

/-- `Exit` survives putting back the erased bindings. -/
private theorem exit_of_ddOut {ρ' ρ'' : Env Core.Expression} (h : Core.DeadDefElim.DDOut ρ' ρ'')
    (hx : Exit ρ'') : Exit ρ' := by
  obtain ⟨hp, p, q, r, ha, hb, hm, h1, h2⟩ := hx
  refine ⟨?_, p, q, r, holds_of_ddOut h ha, holds_of_ddOut h hb, holds_of_ddOut h hm, h1, h2⟩
  change ρ'.factory.factory = _
  rw [← h.1]
  exact hp

/-- `Exit` survives leaving the procedure block, which drops `d` and `sq`. -/
private theorem exit_postWF : Imperative.Logic.Hoare.PostWF maxBody Exit := by
  intro ρ ⟨hp, p, q, r, ha, hb, hm, h1, h2⟩
  have hdrop : ∀ x, x ∉ Block.definedVars (P := Core.Expression) (C := Core.Command) maxBody true →
      Imperative.dropVars
        (Block.definedVars (P := Core.Expression) (C := Core.Command) maxBody true) ρ.store x =
          ρ.store x := fun x hx => by simp only [Imperative.dropVars, ite_eq_right hx]
  refine ⟨hp, p, q, r, ?_, ?_, ?_, h1, h2⟩
  · exact (hdrop aId (by decide +kernel)).trans ha
  · exact (hdrop bId (by decide +kernel)).trans hb
  · exact (hdrop mId (by decide +kernel)).trans hm

/-- `Exit` gives the postconditions. -/
private theorem post_of_exit {ρ : Env Core.Expression} (hx : Exit ρ) :
    Core.Logic.Hoare.Procedure.contractPost Core.Factory maxProc ρ := by
  obtain ⟨hp, p, q, r, ha, hb, hm, h1, h2⟩ := hx
  intro label check hmem _ _
  refine .inl ⟨hp, ?_⟩
  change Core.Expression.eval ρ.factory ρ.store check.expr = some (HasBool.ttVal ρ.factory)
  rcases max_post_expr _ hmem with he | he <;> rw [he, ge_eval hp hm (by assumption)]
  · rw [decide_eq_true h1]; rfl
  · rw [decide_eq_true h2]; rfl

/-- **`Max` meets its contract**, from the triple of the body the Core pass returns
    (`Core.DeadDefElim.deadDefElim_triple`), inside the procedure block. -/
theorem max_meets_contract :
    Core.Logic.Hoare.Procedure.contractTriple maxPgmAST testParams "Max" := by
  have hfactory : maxPgmAST.factoryBeforeProcedure "Max" = Core.Factory :=
    Core.Program.factoryBeforeProcedure_eq_core_of_noFunctions (by decide +kernel)
  rw [Core.Logic.Hoare.Procedure.contractTriple, hfactory]
  refine ⟨maxProc, by native_decide, by native_decide, ?_⟩
  rw [max_body_eq]
  have hsrc := Core.DeadDefElim.deadDefElim_triple π testParams (ss := maxBody)
    (by decide +kernel)
    (by simp [Core.Statements.noCalls, Block.allSubstmts_cons, Stmt.allSubstmts_ite,
      Stmt.allSubstmts_cmd, Block.allSubstmts_nil, Core.Statement.isNotCall])
    (fun _ h => h.2.1) (fun _ _ h hx => exit_of_ddOut h hx) (max_dde ▸ maxTgt_triple)
  exact Core.Logic.Hoare.consequence π testParams
    (Core.Logic.Hoare.block π testParams hsrc exit_postWF) (fun _ h => h)
    (fun _ h => post_of_exit h)

end Strata.HoareAfterDeadDefElimTest
