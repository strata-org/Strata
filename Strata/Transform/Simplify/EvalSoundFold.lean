/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.Simplify.Precondition
public import Strata.DL.Lambda.Denote.LExprSemanticsConsistent
public import Strata.DL.Lambda.OperationalSemanticsProps
public import Strata.Transform.Simplify.FoldFactory
import all Strata.Transform.Simplify.Precondition
import all Strata.Transform.Simplify.FoldFactory
import all Strata.Transform.Simplify.Expr
import all Strata.DL.Lambda.Denote.Assumptions
import all Strata.DL.Lambda.FactoryWF
import all Strata.DL.Util.FuncAttr
import all Strata.DL.Lambda.Denote.LExprSemanticsConsistent

/-! # The conditions of evaluator soundness hold of the fold factory

Simplify folds with the factory whose `inline` attributes it weakened (`withoutInline`). The
conditions of evaluator soundness (`Lambda.Factory.EvalSoundWF`) read no attribute but one,
`shortCircuit`, which the weakening keeps, so they hold of the fold factory when they hold of
the factory (`evalSoundWF_withoutInline`). The weakening keeps every function's body,
evaluator and name, so the fold factory brings in only its own operators when the factory
does (`opsClosed_withoutInline`).
-/

namespace Core.Simplify

open Lambda

public section

/-- Weakening `inline` keeps whether a function short-circuits. -/
private theorem stripInline_hasShortCircuit (c : List String) (fn : LFunc CoreLParams) :
    Strata.DL.Util.FuncAttr.hasShortCircuit (stripInline c fn).attr =
      Strata.DL.Util.FuncAttr.hasShortCircuit fn.attr := by
  unfold stripInline stripInlineFunc
  split
  · rfl
  · simp only [Strata.DL.Util.FuncAttr.hasShortCircuit]
    split
    · rw [Array.toList_filter, List.any_filter]
      congr 1; funext a; cases a <;> simp <;> rfl
    · rw [Array.toList_push, List.any_append, Array.toList_filter, List.any_filter]
      simp only [List.any_cons, List.any_nil, Bool.or_false]
      congr 1; funext a; cases a <;> simp <;> rfl

/-- A well-formed function stays well-formed when its `inline` attribute is weakened. -/
private theorem lfuncWF_stripInline {c : List String} {fn : LFunc CoreLParams} (h : LFuncWF fn) :
    LFuncWF (stripInline c fn) := by
  have hs := stripInline_hasShortCircuit c fn
  unfold stripInline stripInlineFunc at hs ⊢
  split
  · exact h
  · rename_i hcond
    rw [ite_eq_right hcond] at hs
    exact {
      toFuncWF := ⟨h.arg_nodup, h.typeArgs_nodup, h.inputs_typevars_in_typeArgs,
        h.output_typevars_in_typeArgs, h.body_freevars, h.precond_freevars⟩
      constr_no_eval := h.constr_no_eval
      typeArgs_no_gen_prefix := h.typeArgs_no_gen_prefix
      concreteEval_argmatch := h.concreteEval_argmatch
      body_or_concreteEval := h.body_or_concreteEval
      concreteEval_eraseMetadata := h.concreteEval_eraseMetadata
      concreteEval_freeVars := h.concreteEval_freeVars
      shortCircuit_substFvars := fun hsc => h.shortCircuit_substFvars (hs ▸ hsc) }

section
variable {c : List String} {F : Lambda.Factory CoreLParams}

/-- The fold factory's function under a name is the factory's, with other attributes. -/
private theorem getElem_strip_eq (c : List String) (F : Lambda.Factory CoreLParams) (f : String)
    (hf : f ∈ withoutInline c F) :
    ∃ a, (withoutInline c F)[f] = { F[f]'((withoutInline_mem c F f).mp hf) with attr := a } := by
  rw [withoutInline_getElem c F f hf]
  exact stripInline_eq c _

/-- A constructor's function carries no attribute, so weakening `inline` leaves it alone. -/
private theorem stripInline_constrFunc (c : List String) (k : LConstr CoreLParams.IDMeta)
    (d : LDatatype CoreLParams.IDMeta) : stripInline c (constrFunc k d) = constrFunc k d := by
  unfold stripInline stripInlineFunc
  rw [ite_eq_left (by simp [constrFunc])]

/-- The fold factory of a well-formed factory is well-formed. -/
private theorem factoryWF_withoutInline (h : FactoryWF F) : FactoryWF (withoutInline c F) :=
  ⟨fun lf hlf => by
    obtain ⟨g, hg, rfl⟩ := withoutInline_mem_toArray hlf
    exact lfuncWF_stripInline (h.lfuncs_wf g hg)⟩

/-- The fold factory's constructors are well-formed when the factory's are. -/
private theorem constrWellFormed_withoutInline {tf : @TypeFactory CoreLParams.IDMeta}
    (h : Factory.ConstrWellFormed F tf) : Factory.ConstrWellFormed (withoutInline c F) tf := by
  intro f hf hc
  obtain ⟨g, hg, rfl⟩ := withoutInline_mem_toArray hf
  rw [stripInline_isConstr] at hc
  obtain ⟨d, hd, k, hk, rfl⟩ := h g hg hc
  exact ⟨d, hd, k, hk, stripInline_constrFunc c k d⟩

/-- The step conditions of evaluator soundness hold of the fold factory when they hold of the
    factory. -/
private theorem stepWFOn_withoutInline {tyMap : Map CoreIdent LMonoTy}
    (h : Factory.StepWFOn F tyMap) : Factory.StepWFOn (withoutInline c F) tyMap where
  wt := fun f hf body hb => by
    obtain ⟨a, he⟩ := getElem_strip_eq c F f hf
    rw [he] at hb ⊢
    exact h.wt f _ body hb
  evalWt := fun f hf ceval hc => by
    obtain ⟨a, he⟩ := getElem_strip_eq c F f hf
    rw [he] at hc ⊢
    exact h.evalWt f _ ceval hc
  bodyOps := fun f hf body callee args S hb hS => by
    obtain ⟨a, he⟩ := getElem_strip_eq c F f hf
    rw [he] at hb hS
    exact (opsConsistent_withoutInline c F _).mpr (h.bodyOps f _ body callee args S hb hS)
  evalOps := fun f hf ceval md opTy args result hc hr hargs => by
    obtain ⟨a, he⟩ := getElem_strip_eq c F f hf
    rw [he] at hc
    exact (opsConsistent_withoutInline c F _).mpr (h.evalOps f _ ceval md opTy args result hc hr
      fun x hx => (opsConsistent_withoutInline c F x).mp (hargs x hx))
  bodyAnnot := fun f hf body S args hb hlen hargs => by
    obtain ⟨a, he⟩ := getElem_strip_eq c F f hf
    rw [he] at hb hlen ⊢
    exact h.bodyAnnot f _ body S args hb hlen hargs
  evalAnnot := fun f hf ceval md opTy args result hc hr hargs => by
    obtain ⟨a, he⟩ := getElem_strip_eq c F f hf
    rw [he] at hc
    exact h.evalAnnot f _ ceval md opTy args result hc hr hargs

/-- **The conditions of evaluator soundness hold of the fold factory** when they hold of the
    factory. -/
theorem evalSoundWF_withoutInline (h : Factory.EvalSoundWF F) :
    Factory.EvalSoundWF (withoutInline c F) := by
  obtain ⟨⟨tf, hwf⟩, hstep⟩ := h
  exact ⟨⟨tf, ⟨factoryWF_withoutInline hwf.factoryWF,
      constrWellFormed_withoutInline hwf.constrWF, hwf.tfWF⟩⟩,
    fun tyMap => stepWFOn_withoutInline (hstep tyMap)⟩

/-- **The fold factory brings in only its own operators** when the factory does: weakening
    `inline` keeps every function's body, concrete evaluator and name. -/
theorem opsClosed_withoutInline (h : Factory.OpsClosed F) :
    Factory.OpsClosed (withoutInline c F) := by
  have hname : ∀ o : CoreIdent, o.name ∈ F → o.name ∈ withoutInline c F :=
    fun o ho => (withoutInline_mem c F _).mpr ho
  refine ⟨fun lf hlf body hb => ?_, fun lf hlf ceval hce md opTy args r hr => ?_⟩
  · obtain ⟨g, hg, rfl⟩ := withoutInline_mem_toArray hlf
    obtain ⟨a, he⟩ := stripInline_eq c g
    rw [he] at hb
    exact LExpr.OpsIn.mono hname (h.1 g hg body hb)
  · obtain ⟨g, hg, rfl⟩ := withoutInline_mem_toArray hlf
    obtain ⟨a, he⟩ := stripInline_eq c g
    rw [he] at hce
    exact LExpr.OpsIn.mono (fun o ho => ho.imp_left (hname o))
      (h.2 g hg ceval hce md opTy args r hr)

end

end -- public section

end Core.Simplify
