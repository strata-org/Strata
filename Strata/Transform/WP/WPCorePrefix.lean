/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.WP.WPCoreDefs
public import Strata.DL.Imperative.Analysis.Definitions
public import Strata.Transform.Passive.CoreTyped
import Strata.DL.Imperative.Logic.TerminationProps
import Strata.Transform.WP.WPRestrict
import Strata.Transform.WP.WPProps
import Strata.Transform.WP.Adequacy
import Strata.Transform.WP.WPReads
import Strata.Transform.WP.WPReplay
import Strata.Transform.WP.WPOutSyntax
import Strata.Transform.DeadDefElimProps

/-! # The WP phase over-approximates the failing prefixes of Core statement lists

The runs of the output of the WP phase over-approximate those of its input, up to the reflection
of the last failure (`LastFailureReflected`), in the framework notion
`EventLang.RunsOverapproximate` over the Core event semantics of statement lists
(`EventLang.coreBlock`): a run of the input ending in a failing occurrence of an assertion
(resp. a cover) on a feasible path is matched by a run of the output ending in a failing
occurrence of an assertion (resp. a cover) with the same label and metadata on a feasible path
(`wp_prefix`).
The proof goes through the big-step semantics: the failure of the input is one from the store
restricted to the variables the input reads (`claimK_restrict`), the WP output fails from that
store (`wpEntry_overK`), and so from the full store (`claimK_widen`), since the two stores agree
on the identifiers of the output; each step keeps the kind of the failing check.

Key theorems: `wp_prefix`. -/

namespace Core
namespace WP

open Imperative Imperative.BigStep Imperative.WP Core.Logic Strata.Logic Core.DeadDefElim

public section

/-- Scope facts of a well-scoped loop-free list from scope `S`: no variable of `S` is defined
    by the list, every assigned variable is in `S` or defined by the list, every free variable
    is modified or read by the list (`Block.modifiedVars`, `Block.getVars`), and the list makes
    no call. -/
private theorem wfl_facts {Lc : List Expression.Ident} : ∀ {S : List Expression.Ident}
    {ss : Statements}, Block.WellScoped Lc S ss →
    (∀ x ∈ Block.definedVars ss false, x ∉ S) ∧
    (∀ x ∈ Block.assignedVars ss, x ∈ S ∨ x ∈ Block.definedVars ss false) ∧
    (∀ x ∈ Block.freeVars ss, x ∈ Block.modifiedVars ss ∨ x ∈ Block.getVars ss) ∧
    Statements.noCalls ss = true := by
  have ht (s : Statement) : ∀ x ∈ Stmt.topInits s, x ∈ Stmt.definedVars s false := by
    unfold Stmt.topInits; split <;>
      simp [Stmt.definedVars, HasVarsImp.definedVars, CmdExt.definedVars, Cmd.definedVars]
  intro S ss h
  induction S, ss using Block.WellScoped.induct (motive_2 := fun S s => Stmt.WellScoped Lc S s →
    (∀ x ∈ Stmt.definedVars s false, x ∉ S) ∧
    (∀ x ∈ Stmt.assignedVars s, x ∈ S ∨ x ∈ Stmt.definedVars s false) ∧
    (∀ x ∈ Stmt.freeVars s, x ∈ Stmt.modifiedVars s ∨ x ∈ Stmt.getVars s) ∧
    Stmt.allSubstmts Statement.isNotCall s = true)
  all_goals simp only [Block.definedVars, Stmt.definedVars, Block.getVars, Stmt.getVars,
    Block.modifiedVars, Stmt.modifiedVars, HasVarsImp.definedVars, HasVarsImp.modifiedVars,
    HasVarsImp.readVars, CmdExt.definedVars, CmdExt.modifiedVars, CmdExt.readVars,
    Cmd.definedVars, Cmd.modifiedVars, Cmd.getVars, Statements.noCalls, Block.allSubstmts,
    Stmt.allSubstmts, Statement.isNotCall, ExprOrNondet.getVars] at *
  all_goals grind [Block.WellScoped, Stmt.WellScoped, Block.assignedVars, Stmt.assignedVars,
    Stmt.freeVars, Block.freeVars, mem_stmtsFV_cons, mem_exprFV, Stmt.topInits]

/-- **The WP phase over-approximates the failing prefixes of a Core statement list.**  For the
    WP output `w` of a list `ss` meeting the syntactic precondition `WPPre`, and initial
    environments related by `EntryRel`, the source well formed (`BlockInitEnvWF`) and well
    typed under the types `tys` of its free variables (`Statements.WellTyped`, which holds of
    a type-checked procedure body), and the variables the output defines undefined,
    every bounded run of `ss` has a bounded run of
    `w.lay` reflecting its last failure (`LastFailureReflected`): a run ending in a failing
    occurrence of an assertion (resp. a cover), every assumption before it holding, is matched by
    a run of `w.lay` ending in a failing occurrence of an assertion (resp. a cover) with the same
    label and metadata, every assumption before it holding; any other run is matched by the empty
    run. -/
theorem wp_prefix (π : String → Option Procedure) (params : InitEnvWFParams)
    {G : IdSet Expression} {tys : Tys Expression} {ss : Statements} {w : WOut Expression}
    (h : wpEntry G tys ss = .ok w) (hpre : WPPre tys ss) {ρ₀ ρ₀' : Env Expression}
    (hR : EntryRel tys ρ₀ ρ₀') (hwf : BlockInitEnvWF params ss ρ₀)
    (htyp : Statements.WellTyped (fun x => tys.get? x) ss)
    (hdecl : ∀ y ∈ Block.definedVars w.lay false, ρ₀.store y = none) :
    (EventLang.coreBlock π).RunsOverapproximate LastFailureReflected (EventLang.coreBlock π)
      ((EventLang.coreBlock π).stmtCfg ss ρ₀) ((EventLang.coreBlock π).stmtCfg w.lay ρ₀') := by
  obtain ⟨rfl, hty, -⟩ := hR
  obtain ⟨hfv, hwfl, -⟩ := hpre
  obtain ⟨hS, hLc, hFV, hnc⟩ := wfl_facts hwfl
  have hB := hwf.toWellFormedSemanticEval
  intro n trace c hreach
  by_cases hcl : ∃ k a e, ClaimK k a e trace
  · obtain ⟨k, a, e, hk⟩ := hcl
    have hstar := star_evalE (EventLang.traceStar_iff_reachesWithin.2 ⟨n, hreach⟩) hnc
    have hb := star_breach hstar
      (by obtain ⟨_, _, rfl, -⟩ := hk; simp)
    obtain ⟨tr0, hb0, hk0⟩ := claimK_restrict hB.toWellFormedSemanticEvalBase hwfl hfv
      (fun x hx hxS => Option.isNone_iff_eq_none.1
        (hwf.defsUndefined x ((hLc x hx).resolve_left hxS)))
      hwf.storeWellDefined (shadowOK_of_initTysOK hwfl hwf.initTypesInhabited _ _ hb) hk
    generalize hr : (fun x => if (tys.map (·.1)).contains x && (contFV [ss]).contains x
      then ρ₀'.store x else none) = σr at hb0
    have hr' (x) : σr x = if (tys.map (·.1)).contains x && (contFV [ss]).contains x
        then ρ₀'.store x else none := hr ▸ rfl
    have hdef : ∀ x ∈ tys.map (·.1), x ∈ contFV [ss] → (σr x).isSome := fun x hx hc => by
      obtain ⟨_, hl, hfx⟩ := (mem_contFV (P := Expression)).1 hc
      have ht : x ∈ Block.touchedVars ss := by
        simp only [Block.touchedVars, Block.modifiedOrDefinedVars, List.mem_append]
        exact (hFV x (List.mem_singleton.1 hl ▸ hfx)).elim (fun h => .inl (.inl h)) .inr
      simpa [hr', hx, hc] using hwf.readWritesDefined x ht fun hd => hS x hd hx
    have hdom : SemanticStore.DomIn σr ((tys.map (·.1)).filter fun x => (contFV [ss]).contains x) :=
      fun x hx => by
        rw [hr'] at hx
        split at hx
        · rename_i hc
          exact List.mem_filter.2 (by simpa using hc)
        · cases hx
    have hC : WellFormedStore σr ρ₀'.factory := fun x v hv =>
      hwf.storeWellDefined x v (by rw [hr'] at hv; split at hv <;> first | exact hv | cases hv)
    obtain ⟨wsub, -, -, tr1, hb1, hk1⟩ := wpEntry_overK hB.var hB.val hB.exprCongr hB.rename h hwfl
      (fun x hx _ _ _ => hx) hdef (fun x _ hxS => by simp [hr', hxS]) hdom hC
      (fun x hx hc ty ht v hv => hty x hx hx ty ht v (by simpa [hr', hx, hc] using hv))
      (tE := typedEval) htyp.1 hb0 hk0
    have hagr : ∀ y ∈ Block.idents w.lay, ρ₀'.store y = σr y := fun y hy => by
      rcases List.mem_append.1 (idents_sub_fv_defs (wpBody_shape h).1 y hy) with hy | hy
      · have hy' := wpEntry_fv h hwfl y hy
        have hyc : y ∈ contFV [ss] := (mem_contFV (P := Expression)).2 ⟨ss, by simp, hy'⟩
        simp [hr', hfv y hy', hyc]
      · simp [hr', hdecl y hy]
    obtain ⟨tr2, hb2, hk2⟩ := claimK_widen (evCongr_of_congr hB.exprCongr) hC
      hwf.storeWellDefined hagr hb1 hk1
    obtain ⟨cfg, hrun⟩ := breach_star hB.bool hb2
    obtain ⟨m, hm⟩ := EventLang.traceStar_iff_reachesWithin.1 (star_core π hrun)
    refine ⟨m, tr2, cfg, hm, fun k' b _ ⟨evs2, e2, heq, _, hFb, _⟩ => ⟨substObl wsub e, ?_⟩⟩
    obtain ⟨evs, e1, rfl, -, hFa, -⟩ := hk
    obtain ⟨-, he⟩ := List.append_inj' heq rfl
    obtain ⟨evs3, a3, rfl, hA3, hF3, hc3⟩ := hk2
    cases k <;> cases k' <;> simp only [Bool.false_eq_true, ↓reduceIte, List.cons.injEq,
      reduceCtorEq, Event.assert.injEq, Event.cover.injEq, and_true, FailsAt] at he hFa hFb hF3
    all_goals
      subst he
      refine ⟨evs3, a3, rfl, hA3, ?_, hc3⟩
      simp only [Bool.false_eq_true, ↓reduceIte, FailsAt]
      exact ⟨hF3.1.trans (hFa.1.symm.trans hFb.1), hF3.2.1.trans (hFa.2.1.symm.trans hFb.2.1),
        hF3.2.2⟩
  · exact ⟨0, [], _, ⟨rfl, rfl⟩, fun k a e ha => (hcl ⟨k, a, e, ha⟩).elim⟩

end -- public section

end WP
end Core
