/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.WP.WPCoreCorrect
public import Strata.Transform.Passive.CoreTyped
import all Strata.Transform.WP.WPCoreProgram
import Strata.Transform.WP.WPCoreTyping
import Strata.Transform.WP.WPCoreProgramProps
import Strata.Util.ExceptProps
import Strata.Util.OrderedSetProps

/-! # The typing of the WP phase's output

The phases `--vcgen wp` runs after the WP phase need the procedure bodies of the WP phase's
output well typed (`Statements.WellTyped`) under a typing that agrees with the types of the
procedure's parameters on the free variables that are parameters or aliases
(`WPPipelineEntryWellTyped`). The WP phase establishes it (`wpPipelinePhase_entryWellTyped`) when
the contract-wrapped body of every procedure of its input other than an obligation unit is well
typed under the types of the procedure's parameters, which is what
`Core.WP.TypeCheckWPWellTyped` states of the programs `Core.typeCheck` accepts, and the body of
every obligation unit is well typed under some typing (`WPPhaseInputWellTyped`): the WP phase of
each procedure keeps the body well typed (`Core.WP.wpEntry_wellTyped`), and it keeps the
obligation units, whose contract is empty and which have no parameters.

Key definitions: `Core.ObligationExtraction.WPPhaseInputWellTyped`,
`Core.ObligationExtraction.WPPipelineEntryWellTyped`, `Core.ObligationExtraction.PhaseRuns`.

Key theorems: `Core.ObligationExtraction.wpProcsProgram_entryWellTyped`,
`Core.ObligationExtraction.wpPipelinePhase_entryWellTyped`. -/

public section

namespace Core.ObligationExtraction

open Lambda Imperative

/-- **The typing premise of the WP phase's input** `prog`: the contract-wrapped structured body
    of every procedure of `prog` that is not an obligation unit (`WP.isObligationUnit`) is well
    typed under the types of the procedure's parameters (`Statements.WellTyped`), the conclusion
    of `Core.WP.TypeCheckWPWellTyped` for `prog`; the body of an obligation unit, whose free
    variables are those of a lemma's obligation and not parameters, is well typed under some
    typing, which gives those variables the types of their annotations. -/
@[expose] def WPPhaseInputWellTyped (prog : Program) : Prop :=
  ∀ p md body opq, Decl.proc p md ∈ prog.decls → p.body = .structured body opq →
    if WP.isObligationUnit p then ∃ Γ, Statements.WellTyped Γ (p.contractWrapped body)
    else Statements.WellTyped (fun x => Imperative.WP.Tys.get? p.paramTys x)
      (p.contractWrapped body)

/-- **The typing of the WP phase's output** `mid`: every procedure of `mid` with a structured
    body `lay` has a typing `Γ` of the names in scope under which `lay` is well typed
    (`Statements.WellTyped`), and that gives each free variable of `lay` it types that is a
    parameter or an alias (`Procedure.entryParams`, `Procedure.oldAliases`) the type the
    procedure's parameter types record. -/
@[expose] def WPPipelineEntryWellTyped (mid : Program) : Prop :=
  ∀ q md lay opq, Decl.proc q md ∈ mid.decls → q.body = .structured lay opq →
    ∃ Γ, Statements.WellTyped Γ lay ∧ ∀ x ∈ Block.freeVars lay, ∀ T, Γ x = some T →
      x ∈ q.entryParams ∨ x ∈ q.oldAliases.map (·.1) →
      Imperative.WP.Tys.get? (P := Expression) q.paramTys x = some T

/-- **The WP phase of a program keeps its procedure bodies well typed.** When `wpProcsProgram`
    succeeds on `prog` with `mid`, and `prog` satisfies the typing premise
    `WPPhaseInputWellTyped`, every procedure body of `mid` is well typed under a typing that
    agrees with its parameter types on its parameters and aliases: a guarded procedure's body
    under the typing of the free variables of the contract-wrapped body by the parameter types,
    and an obligation unit, kept as is and without parameters, under the typing its premise
    gives. -/
theorem wpProcsProgram_entryWellTyped {reserved : List Expression.Ident} {prog mid : Program}
    (h : WP.wpProcsProgram reserved prog = .ok mid) (hin : WPPhaseInputWellTyped prog) :
    WPPipelineEntryWellTyped mid := by
  intro q md lay opq hq hb
  obtain ⟨decls, hm, he⟩ := (Except.bind_is_ok _ _ _).1 h
  cases he
  obtain ⟨od, hod, hodq⟩ := List.mem_filterMap.1 hq
  cases hodq
  obtain ⟨d, hd, hdq⟩ := mapM_except_mem_right _ _ _ hm _ hod
  rcases d with _ | _ | _ | _ | ⟨p, md'⟩ | _ <;>
    try (simp only [pure, Except.pure, Except.ok.injEq, reduceCtorEq, Option.some.injEq] at hdq
         done)
  dsimp only at hdq
  by_cases hu : WP.isObligationUnit p = true
  · simp only [hu, ↓reduceIte] at hdq
    cases hdq
    have hw := hin q md lay opq hd hb
    simp only [hu, ↓reduceIte] at hw
    obtain ⟨Γ, hw⟩ := hw
    simp only [WP.isObligationUnit] at hu
    split at hu <;> first | cases hu | skip
    all_goals
      refine ⟨Γ, by rwa [WP.contractWrapped_emptySpec q lay ‹_› ‹_›] at hw, fun _ _ _ _ hk => ?_⟩
      simp only [Procedure.entryParams, Strata.Util.OrderedSet.mem_eraseDups, Procedure.oldAliases,
        Procedure.Header.getInoutParams, getInoutParams, List.contains_eq_mem, List.filter_nil,
        List.map_nil, List.not_mem_nil, or_false, *] at hk
      exact nomatch hk
  · simp only [Bool.not_eq_true] at hu
    simp only [hu, Bool.false_eq_true, ↓reduceIte] at hdq
    rcases hpb : p.body with ⟨body, opq'⟩ | _ | _ <;>
      simp only [WP.wpProc, hpb, throw, throwThe, MonadExceptOf.throw, reduceCtorEq, pure,
        Except.pure, Except.ok.injEq] at hdq
    obtain ⟨w, hw, hdq⟩ := (Except.bind_is_ok _ _ _).1 hdq
    cases hdq
    cases hb
    have hin' := hin p _ body _ hd hpb
    simp only [hu, Bool.false_eq_true, ↓reduceIte] at hin'
    refine ⟨_, WP.wpEntry_wellTyped (WP.wpLoopFree_body hw) (WP.checkLoopFree_ok
      (((Except.bind_is_ok _ _ _).1 hw).elim fun _ h => h.1)) hin', fun x _ T hx _ => ?_⟩
    simp only [WP.fvTyping] at hx
    split at hx
    · exact hx
    · cases hx

/-- The phase `φ` has a successful run on `p` that returns `out`. -/
@[expose] def PhaseRuns (φ : PipelinePhase) (p out : Program) : Prop :=
  ∃ s s' b, (φ.transform p).run s = (.ok (b, out), s')

/-- **The WP pipeline phase establishes the typing of its output.** A successful run of
    `wpPipelinePhase` on a program satisfying the typing premise `WPPhaseInputWellTyped` returns a
    program satisfying `WPPipelineEntryWellTyped`. -/
theorem wpPipelinePhase_entryWellTyped {moreFns : Lambda.Factory CoreLParams} {prog mid : Program}
    (h : PhaseRuns (wpPipelinePhase moreFns) prog mid) (hin : WPPhaseInputWellTyped prog) :
    WPPipelineEntryWellTyped mid :=
  let ⟨_, _, _, h⟩ := h
  (WP.wpPipelinePhase_ok h).elim fun _ ⟨_, hw⟩ => wpProcsProgram_entryWellTyped hw hin

end Core.ObligationExtraction

end -- public section
