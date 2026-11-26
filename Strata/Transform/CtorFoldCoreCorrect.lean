/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.CtorFold
public import Strata.Transform.DefInlineCoreCorrect
public import Strata.Transform.WPLoopCorrect
import Strata.Transform.Passive.WPFactoryProps
import all Strata.Transform.CtorFold
import all Strata.Transform.DeadDefElim
import Strata.Transform.DeadDefElimProps
import all Strata.Languages.Core.PipelinePhase
import all Strata.Transform.CoreTransform

/-! # The constructor fold in the per-phase framework

`Core.CtorFold.ctorFold fac ss` is `Core.CtorFold.runSel fac (ctorFoldSel fac ss) ss`
(`ctorFold_eq`), that is the inlining of the names `ctorFoldSel fac ss` selects at the
normalization `ctorNorm fac`, followed by the erasure of the definitions it leaves unread.  Its
trace over-approximation is therefore `defInlineWith_deadDefElimH_overapproximatesTraces` at that
normalization and that choice of names, and nothing here depends on which names are selected:
that theorem holds for every choice, because substituting a name by the right-hand side its
`init` gave it keeps the value whatever the name's occurrence count is.  The size comparison of
`ctorFold` therefore has no part in the soundness argument; it only decides which of two sound
outputs the phase produces.

The normalization's laws come from those of `Core.DefInline.rwAllC`, the bottom-up rewrite at
`Core.DefInline.ctorRoot` (`rwAllWith_normLawT`, `rwAllWith_freeVars`, `rwAllWith_ops`,
`rwAllWith_typed` at `ctorRoot_laws`), and of `Core.DefInline.addFold`, exactly as
`Core.WPLoop.loopNorm`'s come from those of `Core.DefInline.rwAll`.

Key definitions: `ctorFoldSel`.

Key theorems: `ctorNorm_normLawT`, `ctorNorm_synLaws`, `ctorNorm_typed`, `ctorFold_eq`,
`ctorFold_overapproximatesTraces`, `ctorFold_passive`, `ctorFold_initsTyped`,
`ctorFold_condsTyped`, `ctorFoldPipelinePhase_ok`,
`ctorFoldProgram_over`. -/

namespace Core
namespace CtorFold

open Imperative Imperative.BigStep Imperative.DefInline Core.DefInline Lambda
  Imperative.DeadDefElim Core.DeadDefElim Core.Logic Strata.Logic
  Imperative.Specification Imperative.Specification.Transform

public section

/-! ## The laws of the normalization -/

/-- **The normalization of the constructor fold keeps the values of substituted expressions in
    typed stores**, under a factory whose functions are those of `fac` (`hF`), when `fac`
    resolves `Int.Add` and `Bool.Not` to Core's built-in addition and negation. -/
theorem ctorNorm_normLawT {fac : Lambda.Factory CoreLParams} {F : Expression.Factory}
    (hF : F.factory = fac)
    (hAdd : fac["Int.Add"]? = some (Lambda.intAddFunc (T := CoreLParams)).func)
    (hNot : fac["Bool.Not"]? = some (Lambda.boolNotFunc (T := CoreLParams)).func) :
    SubstNormLawT F (ctorNorm fac) := fun g e hC hσ =>
  (addFold_normLaw (hF ▸ hAdd) _ hC).trans
    (rwAllWith_normLawT (ctorRoot_laws fac) hF
      (coreEvaluator_WellFormedSemanticEvalBool F (hF ▸ hNot)) g e hC hσ)

/-- **The normalization of the constructor fold satisfies the syntax laws of the inlining**:
    neither `rwAllC fac` nor `addFold` adds a free variable, annotated occurrence or operator. -/
theorem ctorNorm_synLaws (fac : Lambda.Factory CoreLParams) :
    DefInlineSynLaws Expression (ctorNorm fac) :=
  coreDefInlineSynLaws
    (fun _ _ _ hp => rwAllWith_freeVars (ctorRoot_laws fac) (addFold_freeVars _ _ hp))
    fun _ _ _ ho => rwAllWith_ops (ctorRoot_laws fac) (addFold_ops _ _ ho)

/-- **The normalization of the constructor fold keeps types** (`Core.Expression.Typed`). -/
theorem ctorNorm_typed (fac : Lambda.Factory CoreLParams) :
    SubstNormTyped Expression.Typed (ctorNorm fac) :=
  fun h => addFold_typed (rwAllWith_typed (ctorRoot_laws fac) h)

/-! ## The trace over-approximation -/

/-- The names `ctorFold fac ss` substitutes: `ctorCands fac ss` when that set is empty or
    substituting it leaves the body no larger, and no name otherwise. -/
@[expose] def ctorFoldSel (fac : Lambda.Factory CoreLParams) (ss : Statements) :
    Std.HashMap Expression.Ident Nat :=
  let sel := ctorCands fac ss
  if sel.isEmpty then sel
  else if WPLoop.blockSize (runSel fac sel ss) ≤ WPLoop.blockSize ss then sel
  else (∅ : Std.HashMap Expression.Ident Nat)

/-- **The constructor fold is the inlining at one selection**, `ctorFoldSel fac ss`, followed by
    the erasure of the definitions it leaves unread. -/
theorem ctorFold_eq (fac : Lambda.Factory CoreLParams) (ss : Statements) :
    ctorFold fac ss = Imperative.DeadDefElim.deadDefElimH []
      (defInlineWith (ctorNorm fac) (ctorFoldSel fac ss) ss) := by
  simp only [ctorFold, ctorFoldSel]
  split
  · rfl
  · split <;> rfl

/-- **The constructor fold over-approximates the traces of a Core statement list in passive
    form.**  For `fac` the factory of the pipeline on a program `p` (`Core.wpFactory`), and a
    Core statement list `ss` in passive form without loops or calls: every finite trace of `ss`
    from an initial environment whose factory's functions are those of `fac` has a trace of
    `ctorFold fac ss` from it whose assumptions are weakened and whose events correspond up to
    the erasure of unread definitions, every terminating or exiting run has a corresponding run
    whose final environment agrees up to those definitions, and `ctorFold fac ss` is well formed
    from that environment.

    The relations and the shape of the statement are those of
    `defInlineWith_deadDefElimH_overapproximatesTraces`; this is that theorem at the
    normalization `ctorNorm fac` and the choice of names `ctorFoldSel fac` (`ctorFold_eq`). -/
theorem ctorFold_overapproximatesTraces (π : String → Option Procedure)
    (params : InitEnvWFParams) {moreFns fac : Lambda.Factory CoreLParams} {p : Program}
    (hfac : wpFactory moreFns p = .ok fac) :
    OverapproximatesTracesUptoWhen
      (RComp (Trace.WeakensAssumes evalInterp) (List.Rel₂ DDEventRel))
      (fun ρ ρ' : Imperative.Env Expression => ρ = ρ' ∧ ρ.factory.factory = fac)
      (RComp (· = ·) DDOut)
      (EventLang.coreBlock π) (EventLang.coreBlock π)
      (fun ss => some (ctorFold fac ss))
      (fun ss => Block.noLoops ss = true ∧ Statements.noCalls ss = true ∧
        Block.passiveForm ss = true) params params :=
  (funext fun ss => congrArg some (ctorFold_eq fac ss)).symm ▸
    defInlineWith_deadDefElimH_overapproximatesTraces π params (sel := ctorFoldSel fac)
      (fun _ hF => ctorNorm_normLawT hF (WPLoop.wpFactory_intAdd hfac)
        (WPLoop.wpFactory_boolNot hfac))
      (ctorNorm_synLaws _)

/-- **The output of the constructor fold is in passive form** (on a list in passive form). -/
theorem ctorFold_passive {fac : Lambda.Factory CoreLParams} {ss : Statements}
    (hp : Block.passiveForm ss = true) :
    Block.passiveForm (ctorFold fac ss) = true := by
  have hd := (defInlineWith_passive (norm := ctorNorm fac) (sel := ctorFoldSel fac ss) hp).2.2
  rw [ctorFold_eq]
  exact (Imperative.DeadDefElim.deadDefElimH_eq (P := Expression) [] _).symm ▸
    Imperative.DeadDefElim.deadDefElim_passive [] _ hd

/-- **The constructor fold keeps `init`s typed** (`Core.Expression.Typed` at their declared
    types) on a list in passive form whose annotations agree with a typing `Γ`. -/
theorem ctorFold_initsTyped {fac : Lambda.Factory CoreLParams} {ss : Statements}
    (hp : Block.passiveForm ss = true) {Γ : VarTyping Expression}
    (hf : Block.fvarTypesWellAnnotated Γ ss) (hT : Block.initsTyped Expression.Typed ss) :
    Block.initsTyped Expression.Typed (ctorFold fac ss) := by
  rw [ctorFold_eq, Imperative.DeadDefElim.deadDefElimH_eq (P := Expression)]
  exact deadDefElim_initsTyped _ _
    (defInlineWith_initsTyped (typedOpLaws fac) (ctorNorm_typed fac) hp hf hT)

/-- **The constructor fold keeps the conditions typed**: on a list in passive form whose
    annotations agree with a typing `Γ` and whose `init`s are typed, every `assume`, `assert` and
    `cover` condition of `ctorFold fac ss` has the Boolean type when every such condition of `ss`
    has. -/
theorem ctorFold_condsTyped {fac : Lambda.Factory CoreLParams} {ss : Statements}
    (hp : Block.passiveForm ss = true) {Γ : VarTyping Expression}
    (hf : Block.fvarTypesWellAnnotated Γ ss) (hT : Block.initsTyped Expression.Typed ss)
    (hc : Block.condsTyped Expression.Typed ss) :
    Block.condsTyped Expression.Typed (ctorFold fac ss) := by
  rw [ctorFold_eq, Imperative.DeadDefElim.deadDefElimH_eq (P := Expression)]
  exact Imperative.DeadDefElim.deadDefElim_condsTyped _ _
    (defInlineWith_condsTyped (typedOpLaws fac) (ctorNorm_typed fac) hp hf hT hc)

/-! ## The pipeline phase -/

/-- A run of `ctorFoldPipelinePhase` on `program`, when the pipeline's factory on `program`
    (`Core.wpFactory`) is `fac`, is a run of `ctorFoldProgram fac`. -/
theorem ctorFoldPipelinePhase_ok {moreFns fac : Lambda.Factory CoreLParams} {program : Program}
    (hfac : wpFactory moreFns program = .ok fac) (s : Transform.CoreTransformState) :
    ((ctorFoldPipelinePhase moreFns).transform program).run s =
      (ctorFoldProgram fac program).run s := by
  simp only [ctorFoldPipelinePhase, modelPreservingPipelinePhase, hfac,
    Transform.liftDiag, pure_bind]

/-- A successful run of `ctorFoldPipelinePhase` on `program` is a run of `ctorFoldProgram` at the
    pipeline's factory on `program`, which then succeeds. -/
theorem ctorFoldPipelinePhase_run_ok {moreFns : Lambda.Factory CoreLParams}
    {program out : Program} {s s' : Transform.CoreTransformState} {b : Bool}
    (h : ((ctorFoldPipelinePhase moreFns).transform program).run s = (.ok (b, out), s')) :
    ∃ fac, wpFactory moreFns program = .ok fac ∧
      (ctorFoldProgram fac program).run s = (.ok (b, out), s') := by
  cases hfac : wpFactory moreFns program with
  | error e =>
    simp only [ctorFoldPipelinePhase, modelPreservingPipelinePhase, Transform.liftDiag, hfac,
      ExceptT.bind_throw, ExceptT.run_throw, pure, StateT.pure] at h
    nomatch h
  | ok fac => exact ⟨fac, rfl, (ctorFoldPipelinePhase_ok hfac s).symm.trans h⟩

/-- **The constructor-fold transform rewrites each procedure body.**  Let a run of
    `ctorFoldProgram fac` on the program `prog` succeed with `out`, and let `q` be a procedure of
    `prog` with structured body `ss`.  Then `out` contains the procedure with body
    `ctorFold fac ss`, whose traces over-approximate those of `ss` when `ss` is in passive form
    without loops or calls (`ctorFold_overapproximatesTraces`). -/
theorem ctorFoldProgram_over {fac : Lambda.Factory CoreLParams} {prog out : Program}
    {s s' : Transform.CoreTransformState} {b : Bool}
    (h : (ctorFoldProgram fac prog).run s = (.ok (b, out), s')) {q : Procedure}
    {md : Imperative.MetaData Expression} {ss : Statements} (hq : Decl.proc q md ∈ prog.decls)
    {opq : Bool} (hb : q.body = .structured ss opq) :
    Decl.proc { q with body := .structured (ctorFold fac ss) opq } md ∈ out.decls := by
  cases h
  exact Program.mapStructuredBodies_mem hq hb

/-- **The constructor fold keeps procedure bodies in passive form, typed and def-use well
    formed.** Every procedure `q'` of a run of `ctorFoldProgram fac` on `p` comes from a
    procedure `q` of `p` with the same header and metadata; when `q'` has a structured body, so
    has `q`, and when the body of `q` is in passive form, the body of `q'` is in passive form, is
    def-use well formed and passes the annotation check wherever the body of `q` does, and has
    typed `init`s when the body of `q` does: the inlining at `ctorNorm fac` and the erasure of
    unread definitions keep each. -/
theorem ctorFoldProgram_proc_kept {fac : Lambda.Factory CoreLParams} {p out : Program}
    {s s' : Transform.CoreTransformState} {b : Bool}
    (h : (ctorFoldProgram fac p).run s = (.ok (b, out), s')) {q' : Procedure}
    {md : Imperative.MetaData Expression} (hq : Decl.proc q' md ∈ out.decls) :
    ∃ q, Decl.proc q md ∈ p.decls ∧ q'.header = q.header ∧
      ∀ ss' o, q'.body = .structured ss' o → ∃ ss, q.body = .structured ss o ∧
        (Block.passiveForm ss = true →
          Block.passiveForm ss' = true ∧
          (∀ D df Γ, Block.defUseWellFormed D df ss = true → Block.fvarTypesWellAnnotated Γ ss →
            Block.defUseWellFormed D df ss' = true ∧ Block.fvarTypesWellAnnotated Γ ss') ∧
          (∀ Γ, Block.fvarTypesWellAnnotated Γ ss → Block.initsTyped Core.Expression.Typed ss →
            Block.initsTyped Core.Expression.Typed ss')) := by
  cases h
  obtain ⟨q, hd, hh, hk⟩ := Program.mapStructuredBodies_proc hq
  refine ⟨q, hd, hh, fun ss' o hb' => ?_⟩
  obtain ⟨ss, hb, rfl⟩ := hk ss' o hb'
  refine ⟨ss, hb, fun hp => ?_⟩
  have hw3 := defInlineWith_passive (norm := ctorNorm fac) (sel := ctorFoldSel fac ss) hp
  have hdd : ctorFold fac ss = Imperative.DeadDefElim.deadDefElim [] (defInlineWith
      (ctorNorm fac) (ctorFoldSel fac ss) ss) :=
    (ctorFold_eq fac ss).trans (Imperative.DeadDefElim.deadDefElimH_eq (P := Expression) [] _)
  refine ⟨ctorFold_passive hp, fun D df Γ hdu hw => ?_, fun Γ hw hT => ?_⟩
  · have hg := Imperative.DefInline.walk_gate (ctorNorm_synLaws fac)
      ⟨ctorFoldSel fac ss, Std.HashSet.ofList (Block.assignedVarsH ss)⟩ df ss hp {} D Γ hdu hw
      fun _ _ h => by simp at h
    rw [hdd]
    exact Core.DeadDefElim.deadDefElim_defUse_fvarTypes hw3.1 hw3.2.1 hg.1 hg.2
  · rw [hdd]
    exact Imperative.DeadDefElim.deadDefElim_initsTyped _ _
      (Imperative.DefInline.defInlineWith_initsTyped (typedOpLaws fac) (ctorNorm_typed fac)
        hp hw hT)


end -- public section

end CtorFold
end Core
