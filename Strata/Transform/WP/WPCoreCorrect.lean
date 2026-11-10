/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.WP.WPCoreDefs
public import Strata.DL.Imperative.Analysis.Definitions
public import Strata.Languages.Core.Verifier
public import Strata.Transform.WP.WPCoreProgram
public import Strata.Transform.DeadDefElimCoreCorrect
public import Strata.Transform.Passive.CoreTyped
import Strata.Transform.WP.WPCorePrefix
import Strata.Transform.WP.WPCoreGate
import Strata.Transform.WP.WPCoreProgramProps
import Strata.Transform.WP.WPOutTypes
import Strata.Transform.WP.WPOutDecls
import Strata.Transform.WP.WPCoreOps
import Strata.Util.ExceptProps
import all Strata.Languages.Core.Verifier
import all Strata.Languages.Core.PipelinePhase
import all Strata.Transform.CoreTransform

/-! # The WP phase over-approximates the failing prefixes of a Core statement list

Over Core's event language for statement lists (`EventLang.coreBlock`), for a loop-free list
`ss` meeting `WPPre` whose WP phase (`wpEntry`, and `wpLoopFree`, which the pipeline phase runs)
succeeds with the guarded program `w.lay`, and an initial environment `ρ₀` satisfying
`BlockInitEnvWF params ss` and `EntryRel tys`:

* every bounded run of `ss` from `ρ₀` has a bounded run of `w.lay` from `ρ₀` related by
  `LastFailureReflected` (`EventLang.RunsOverapproximate`; `wp_prefix`): a run ending in a
  failing occurrence of an assertion (resp. a cover), every assumption before it holding, is
  matched by a run ending in a failing occurrence of an assertion (resp. a cover) with the same
  label and metadata;
* `ss` has no exiting run (`wp_noExit`);
* `w.lay` satisfies `BlockInitEnvWF (wpTgtParams params)` at `ρ₀` (`wp_gate`).

These are the prefix clause, the exiting clause and the target gate of
`OverapproximatesTracesUptoWhen LastFailureReflected (EntryRel tys) (fun _ _ => True)`; its
terminal clause is not proved, because verification reads only prefixes.
Over-approximation justifies only verdicts that an assertion cannot fail or that a `cover` is
unreachable; a `cover` reached would need the under-approximation, which is not proved.

A successful run of the pipeline phase `wpPipelinePhase`, the second of the pipeline phases
`--vcgen wp` runs (`wpVCGenPhases`), runs the WP phase of the program (`wpPipelinePhase_ok`).

The over-approximation theorems take the typing premise `Statements.WellTyped`, which no
theorem yet derives from `Core.typeCheck`; `TypeCheckWPWellTyped` states that type checking
establishes it.

TODO: prove the terminal clause, and state the soundness of `wpPipelinePhase` as that
`OverapproximatesTracesUptoWhen` on each procedure body it rewrites.

Key definitions: `TypeCheckWPWellTyped`.

Key theorems: `wp_runsOverapproximate`, `wpLoopFree_runsOverapproximate`, `wp_noExit`,
`wpPipelinePhase_ok`. -/

namespace Core
namespace WP

open Imperative Imperative.BigStep Imperative.WP Imperative.DeadDefElim Core.DeadDefElim
  Core.Logic Strata.Logic

public section

/-- **No exiting run**: a statement list whose every `exit` targets an enclosing block has no
    run from any environment ending in an exiting configuration. -/
theorem wp_noExit (π : String → Option Procedure) {ss : Statements}
    (hcov : Block.exitsCoveredByBlocks [] ss) (ρ₀ : Imperative.Env Expression) :
    ∀ lbl ρ' trace, ¬ (EventLang.coreBlock π).traceStar ((EventLang.coreBlock π).stmtCfg ss ρ₀)
      trace ((EventLang.coreBlock π).exitingCfg lbl ρ') :=
  fun lbl ρ' _ h => stmts_exitsCoveredByBlocks_noEscapeE _ ss hcov ρ₀ lbl ρ' h

/-- **The WP phase over-approximates the failing prefixes of a Core statement list.**  For the
    global names `G` and the free-variable types `tys`, a Core statement list `ss` satisfying
    `WPPre tys ss` whose WP phase (`wpEntry`) succeeds with `w`, and every initial environment
    `ρ₀` satisfying `BlockInitEnvWF params ss` and `EntryRel tys`: every bounded run of `ss` from
    `ρ₀` has a bounded run of `w.lay` from `ρ₀` reflecting its last failure, and `w.lay`
    satisfies `BlockInitEnvWF (wpTgtParams params)` at `ρ₀`. -/
theorem wp_runsOverapproximate (π : String → Option Procedure) (params : InitEnvWFParams)
    {G : IdSet Expression} {tys : Tys Expression} {ss : Statements} {w : WOut Expression}
    (h : wpEntry G tys ss = .ok w) (hpre : WPPre tys ss) {ρ₀ : Imperative.Env Expression}
    (hR : EntryRel tys ρ₀ ρ₀) (hwf : BlockInitEnvWF params ss ρ₀)
    (htyp : Statements.WellTyped (fun x => tys.get? x) ss) :
    (EventLang.coreBlock π).RunsOverapproximate LastFailureReflected (EventLang.coreBlock π)
      ((EventLang.coreBlock π).stmtCfg ss ρ₀) ((EventLang.coreBlock π).stmtCfg w.lay ρ₀) ∧
    BlockInitEnvWF (wpTgtParams params) w.lay ρ₀ := by
  have hg := wp_gate h hpre hR hwf htyp (wpEntry_decls h)
    (wpEntry_initTypes h hpre.2.1 fun _ => id) (wpEntry_ops_core h)
  exact ⟨wp_prefix π params h hpre hR hwf htyp fun y hy => Option.isNone_iff_eq_none.1
    (hg.defsUndefined y hy), hg⟩

/-- **The executable WP phase of a procedure over-approximates failing prefixes**:
    `wp_runsOverapproximate` for `wpLoopFree G p`, which `wpPipelinePhase` runs on the
    contract-wrapped body of each procedure `p` (`Procedure.contractWrapped`), with the parameter
    types of `p`. For every loop-free list `ss` on which `wpLoopFree G p` succeeds with `w` (its
    check `checkLoopFree` establishes `WPPre`), and every initial environment `ρ₀` satisfying
    `EntryRel p.paramTys` and `BlockInitEnvWF params ss`: every bounded run of `ss` from `ρ₀` has a
    bounded run of `w.lay` from `ρ₀` reflecting its last failure, and `w.lay` satisfies
    `BlockInitEnvWF (wpTgtParams params)` at `ρ₀`. -/
theorem wpLoopFree_runsOverapproximate (π : String → Option Procedure)
    (params : InitEnvWFParams) {G : IdSet Expression} {p : Procedure} {ss : Statements}
    {w : WOut Expression} (h : wpLoopFree G p ss = .ok w)
    {ρ₀ : Imperative.Env Expression} (hR : EntryRel p.paramTys ρ₀ ρ₀)
    (hwf : BlockInitEnvWF params ss ρ₀)
    (htyp : Statements.WellTyped (fun x => Tys.get? p.paramTys x) ss) :
    (EventLang.coreBlock π).RunsOverapproximate LastFailureReflected (EventLang.coreBlock π)
      ((EventLang.coreBlock π).stmtCfg ss ρ₀) ((EventLang.coreBlock π).stmtCfg w.lay ρ₀) ∧
    BlockInitEnvWF (wpTgtParams params) w.lay ρ₀ :=
  wp_runsOverapproximate π params (wpLoopFree_body h)
    (checkLoopFree_ok (((Except.bind_is_ok _ _ _).1 h).elim fun _ h => h.1)) hR hwf htyp

/-- **Type checking establishes the typing premise of the WP phase.**  The premise `htyp` of
    `wpLoopFree_runsOverapproximate` asks of the statement list `p.contractWrapped body`, which
    `wpPipelinePhase` rewrites, `Statements.WellTyped` under the parameter types of `p`.  The
    statement: for a monomorphic program `Core.typeCheck` accepts, the contract-wrapped
    structured body of each of its procedures meets that premise.  This is the statement, not yet
    a theorem.  `Specification.Analysis.TypeCheckWellTypes` and `TypeCheckAnnotates` do not
    imply it: they type each expression under its own annotations, and say nothing of ground
    types, of the agreement of the annotations with the parameter types and the declarations, or
    of the types of the variables nondeterministic assignments write. -/
@[expose] def TypeCheckWPWellTyped : Prop :=
  ∀ (options : VerifyOptions) (program program' : Program)
    (factory : Lambda.Factory CoreLParams),
    Core.typeCheck options program factory = .ok program' →
    program'.noPolymorphicProcedures = Bool.true →
    ∀ p md body, Decl.proc p md ∈ program'.decls → p.body = .structured body →
      Statements.WellTyped (fun x => Tys.get? p.paramTys x) (p.contractWrapped body)

/-! ## The pipeline phase -/

/-- A successful run of `wpPipelinePhase` on `program` returns the guarded program of `program`
    for the names of the functions of the factory `moreFns` extends. -/
theorem wpPipelinePhase_ok {m : Lambda.Factory CoreLParams}
    {program out : Program} {s s' : Transform.CoreTransformState} {b : Bool}
    (h : ((wpPipelinePhase m).transform program).run s = (.ok (b, out), s')) :
    ∃ fac, Core.Factory.addFactory m = .ok fac ∧
      wpProcsProgram (fac.toArray.toList.map (·.name)) program = .ok out := by
  simp only [wpPipelinePhase, modelPreservingPipelinePhase, Transform.liftDiag] at h
  rcases hw : wpProgram program m with _ | mid <;> rw [hw] at h <;> cases h
  simp only [wpProgram, Bind.bind, Except.bind, throw, throwThe, MonadExceptOf.throw] at hw
  repeat (split at hw <;> try cases hw)
  exact ⟨_, ‹_›, by assumption⟩

end -- public section

end WP
end Core
