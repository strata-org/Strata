/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import Strata.Languages.Core.Expressions
import Strata.Transform.Simplify.Precondition
import Strata.DL.Lambda.TypeFactoryWFProps
import Strata.DL.Lambda.Denote.Assumptions
-- `import all` of `IntBoolFactory` is the one exception to importing the precondition's
-- vocabulary without `all`. It is used for three things: building `F₂` (its name check), the
-- bodies of `Int.Add`'s and `Int.Lt`'s concrete evaluators, and the factory lookup lemmas of
-- `FactoryProps` (`ofArray_mem`, `mem_iff_mem_names`, `mem_name_eq_getElem`,
-- `get?_ofArray_of_mem`, `getElem?_some_getElem`), which are not public. Through it the test
-- also computes Lambda's typing and substitution functions on concrete terms. Making those
-- lookup lemmas and computations public is planned as a separate change.
import all Strata.DL.Lambda.IntBoolFactory
import Strata.DL.Lambda.LTy
import Strata.DL.Lambda.TypeFactory
import Strata.DL.Lambda.FactoryProps
import Strata.DL.Lambda.LTyUnify
import Strata.Languages.Core.StatementProps
import Strata.DL.Imperative.StmtProps
import Strata.Transform.SimplifyCorrect
import all Strata.Languages.Core.FactoryEvalSoundWF
import Strata.Languages.Core.InstWellFormedSemanticsEval
import all Strata.DL.Lambda.FactoryProps
import all Strata.Transform.Simplify.Expr
meta import Strata.Transform.Simplify
meta import Strata.Transform.Simplify.Precondition
meta import Strata.Transform.Simplify.OutputGate
meta import Strata.DL.Lambda.IntBoolFactory

/-! # A small factory meeting the precondition of the Simplify theorem

`F₂` holds two Core operators with concrete evaluators, `Int.Add` and `Int.Lt`, and one
user function with a body, `inc (n : int) : int := Int.Add(n, 1)`. -/

namespace Core.Simplify.UserFuncTest

open Lambda

/-- `inc (n : int) : int := Int.Add(n, 1)`. -/
def incBody : LExpr CoreLParams.mono :=
  .app default (.app default (.op default ⟨"Int.Add", ()⟩ (some (.arrow .int (.arrow .int .int))))
    (.fvar default ⟨"n", ()⟩ (some .int))) (.intConst default 1)

/-- The user function `inc`, as the factory holds it, marked `inline` so that Simplify
    expands its calls. -/
def incLFunc : LFunc CoreLParams :=
  { name := ⟨"inc", ()⟩, typeArgs := [], inputs := [(⟨"n", ()⟩, .int)], output := .int,
    body := some incBody, attr := #[.inline] }

/-- `inc`, with the proof that it is well-formed. -/
def incFunc : WFLFunc CoreLParams where
  func := incLFunc
  wf := {
    toFuncWF := {
      arg_nodup := by decide
      typeArgs_nodup := by decide
      inputs_typevars_in_typeArgs := by
        intro ty hty
        simp only [incLFunc, ListMap.values, List.mem_cons, List.not_mem_nil, or_false] at hty
        subst hty; decide
      output_typevars_in_typeArgs := by decide
      body_freevars := by
        intro b hb
        simp only [incLFunc, Option.some.injEq] at hb
        subst hb
        decide
      precond_freevars := by intro p hp; simp [incLFunc] at hp }
    constr_no_eval := by simp [incLFunc]
    concreteEval_argmatch := by intro fn _ _ _ _ hfn; simp [incLFunc] at hfn
    body_or_concreteEval := by simp [incLFunc]
    concreteEval_eraseMetadata := by intro _ h; simp [incLFunc] at h
    concreteEval_freeVars := by intro _ h; simp [incLFunc] at h }

/-- The factory: `Int.Add` and `Int.Lt` with their concrete evaluators, and `inc`. -/
def fns₂ : Array (WFLFunc CoreLParams) := #[intAddFunc, intLtFunc, incFunc]

/-- The factory of `Int.Add`, `Int.Lt` and `inc`. -/
def F₂ : Lambda.Factory CoreLParams := (WFLFactory.ofArray fns₂).toFactory

/-- `F₂` is a well-formed factory. -/
theorem F₂_wf : FactoryWF F₂ := WFLFactory.toFactory_wf _

/-- `F₂` is the factory of its three functions. -/
theorem F₂_eq : F₂ = Factory.ofArray (fns₂.map (·.func)) := rfl

/-- The three functions of `F₂` have distinct names. -/
theorem F₂_nodup : ((fns₂.map (·.func)).toList.map (·.name.name)).Nodup := by
  rw [Array.toList_map, List.map_map]; decide

/-- A function of `F₂` is one of its three. -/
theorem F₂_mem {fn : LFunc CoreLParams} (h : fn ∈ F₂.toArray) :
    fn = (intAddFunc (T := CoreLParams)).func ∨ fn = (intLtFunc (T := CoreLParams)).func ∨
      fn = incLFunc := by
  rw [F₂_eq] at h
  obtain ⟨a, ha, rfl⟩ := Array.mem_map.mp (Factory.ofArray_mem h)
  have ha' : a ∈ [intAddFunc (T := CoreLParams), intLtFunc, incFunc] := Array.mem_def.mp ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ha'
  rcases ha' with rfl | rfl | rfl
  · exact .inl rfl
  · exact .inr (.inl rfl)
  · exact .inr (.inr rfl)

/-- `F₂` resolves `Int.Add` to its `Int.Add`. -/
theorem F₂_intAdd : F₂["Int.Add"]? = some (intAddFunc (T := CoreLParams)).func := by
  rw [F₂_eq]
  exact Factory.get?_ofArray_of_mem (Array.mem_map.mpr ⟨_, ⟨.head _⟩, rfl⟩) F₂_nodup

/-- Instantiating type variables leaves `inc`'s body alone: its annotations are ground. -/
theorem incBody_applyTypeSubst (S : Subst) : incBody.applyTypeSubst S = incBody := by
  unfold LExpr.applyTypeSubst
  split
  · rfl
  · simp only [incBody, LExpr.replaceUserProvidedType, Option.map_some, LMonoTy.subst_unfold,
      List.map_cons, List.map_nil, LExpr.app.injEq, LExpr.op.injEq, Option.some.injEq, true_and,
      LExpr.fvar.injEq]
    exact ⟨⟨rfl, rfl⟩, rfl⟩

/-! ## The theorem's precondition, discharged -/

/-- `F₂` resolves `Int.Lt` to its `Int.Lt`. -/
theorem F₂_intLt : F₂["Int.Lt"]? = some (intLtFunc (T := CoreLParams)).func := by
  rw [F₂_eq]
  exact Factory.get?_ofArray_of_mem (Array.mem_map.mpr ⟨_, ⟨.tail _ (.head _)⟩, rfl⟩) F₂_nodup

/-- `F₂` resolves `inc` to `inc`. -/
theorem F₂_inc : F₂["inc"]? = some incLFunc := by
  rw [F₂_eq]
  exact Factory.get?_ofArray_of_mem (Array.mem_map.mpr ⟨_, ⟨.tail _ (.tail _ (.head _))⟩, rfl⟩)
    F₂_nodup

/-- `inc` is a user function the conditions of evaluator soundness admit: no concrete
    evaluator, not a constructor, and a body that is well typed at `int`, annotates `n` with
    its declared type and is `OpsConsistent` at every instance. -/
theorem inc_userFuncWF : Core.UserFuncWF F₂ incLFunc := by
  refine ⟨rfl, rfl, fun body hb => ?_⟩
  simp only [incLFunc, Option.some.injEq] at hb
  subst hb
  have hs : LFunc.opTypeSubst (intAddFunc (T := CoreLParams)).func
      (.op default ⟨"Int.Add", ()⟩ (some (.arrow .int (.arrow .int .int)))) =
    some Subst.empty := by
    simp [LFunc.opTypeSubst, intAddFunc, binaryOp]
  have ht : LMonoTy.arrow .int (.arrow .int .int) =
      (LMonoTy.mkArrow' (intAddFunc (T := CoreLParams)).func.output
        ((intAddFunc (T := CoreLParams)).func.inputs.map Prod.snd)).subst Subst.empty := by
    simp [intAddFunc, binaryOp, LMonoTy.mkArrow', LMonoTy.subst_unfold, Subst.empty]
    rfl
  refine ⟨LExpr.typeCheck_to_HasTypeA (by rfl), ?_, fun _ _ S _ => ?_⟩
  · refine .app (.app .op (.fvar fun ty' h => ?_)) .const
    simp only [incLFunc, Map.find?, ↓reduceIte, Option.some.injEq] at h
    exact h
  · rw [incBody_applyTypeSubst]
    exact .app (.app (.op_in F₂_intAdd hs ht) .fvar) .const

/-- **`F₂` meets the conditions of evaluator soundness**: its operators are those of
    `Core.Factory`, and `inc` is a user function they admit. -/
theorem F₂_evalSoundWF : Factory.EvalSoundWF F₂ :=
  Core.programFactory_evalSoundWF F₂ F₂_wf fun fn h => by
    rcases F₂_mem h with rfl | rfl | rfl
    · exact .inl (Factory.getElem?_is_some_implies_mem Core.coreFactory_intAdd)
    · exact .inl (Factory.getElem?_is_some_implies_mem Core.coreFactory_intLt)
    · exact .inr inc_userFuncWF

/-- **`F₂` brings in only its own operators**: `inc`'s body calls `Int.Add`, a function of
    `F₂`. -/
theorem F₂_opsClosed : Factory.OpsClosed F₂ :=
  Core.programFactory_opsClosed F₂ (fun fn h => by
    rcases F₂_mem h with rfl | rfl | rfl
    · exact .inl (Factory.getElem?_is_some_implies_mem Core.coreFactory_intAdd)
    · exact .inl (Factory.getElem?_is_some_implies_mem Core.coreFactory_intLt)
    · exact .inr inc_userFuncWF) fun fn h body hb => by
    rcases F₂_mem h with rfl | rfl | rfl
    · cases hb
    · cases hb
    · simp only [incLFunc, Option.some.injEq] at hb
      subst hb
      intro o ho
      simp only [incBody, LExpr.getOps, List.append_nil, List.mem_singleton] at ho
      subst ho
      exact Factory.getElem?_some_implies_mem F₂_intAdd

/-- The body: `var a : int := inc(m); assert [lt]: Int.Lt(m, a);`. It declares a local
    that a later assertion reads, and calls the user function and a Core operator. Its free
    variables carry their types, as the type checker writes them. -/
def body₂ : List Statement :=
  [Statement.init ⟨"a", ()⟩ (.forAll [] .int)
      (.det (.app default (.op default ⟨"inc", ()⟩ (some (.arrow .int .int)))
        (.fvar default ⟨"m", ()⟩ (some .int))))
      .empty,
   Statement.assert "lt"
      (.app default
        (.app default (.op default ⟨"Int.Lt", ()⟩ (some (.arrow .int (.arrow .int .bool))))
        (.fvar default ⟨"m", ()⟩ (some .int)))
        (.fvar default ⟨"a", ()⟩ (some .int))) .empty]

/-- The entry typing: the body's one entry variable `m` is an `int`. -/
def Γ₂ : Imperative.VarTyping Expression :=
  fun x => if x = ⟨"m", ()⟩ then some (LTy.forAll [] .int) else none

/-- **`BodyWF` holds of `body₂`.** -/
theorem body₂_wf : BodyWF F₂ Γ₂ body₂ := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simp only [body₂, noCalls_eq_cons, noCalls_nil, Statement.noCalls,
      Imperative.Stmt.allSubstmts_cmd]
    rfl
  · simp only [body₂, Imperative.Block.noLoops_cons, Imperative.Block.noLoops_nil,
      Imperative.Stmt.noLoops_cmd, Bool.and_self]
  simp only [body₂, Block.exprsOKIn, Stmt.exprsOKIn, ExprOK, Expression.HasType, and_true,
    Statement.init, Imperative.Stmt.typedDefinedVars, Imperative.HasTypedVarsImp.typedDefinedVars,
    Imperative.CmdExt.typedDefinedVars, Imperative.Cmd.typedDefinedVars]
  refine ⟨⟨⟨.int, rfl, by decide, ?_, LExpr.typeCheck_to_HasTypeA ?_⟩, ?_, ?_⟩,
    ⟨⟨.bool, rfl, by decide, ?_, LExpr.typeCheck_to_HasTypeA ?_⟩, ?_, ?_⟩⟩
  · intro x hx
    simp only [LExpr.LExpr.getVars, List.mem_append, List.mem_singleton, List.not_mem_nil,
      false_or] at hx
    subst hx; simp [Γ₂]
  · simp only [LExpr.annotateFvars, Γ₂, ite_true, Option.bind_some, LTy.toMonoType?]
    rfl
  · exact .app (.op_in (tySubst := Subst.empty) F₂_inc (by simp [LFunc.opTypeSubst, incLFunc])
      (by simp [incLFunc, LMonoTy.mkArrow', LMonoTy.subst_unfold]; rfl)) .fvar
  · simp [LExpr.annotateFvars, Γ₂, LTy.toMonoType?]
  · intro x hx
    simp only [LExpr.LExpr.getVars, List.mem_append, List.mem_singleton, List.not_mem_nil,
      false_or] at hx
    rcases hx with rfl | rfl <;> simp [Γ₂, Imperative.VarTyping.extend]
  · simp [LExpr.annotateFvars, Γ₂, Imperative.VarTyping.extend, LTy.toMonoType?]
    rfl
  · have hs : LFunc.opTypeSubst (intLtFunc (T := CoreLParams)).func
        (.op default ⟨"Int.Lt", ()⟩ (some (.arrow .int (.arrow .int .bool)))) =
      some Subst.empty := by
      simp [LFunc.opTypeSubst, intLtFunc, binaryOp]
    have ht : LMonoTy.arrow .int (.arrow .int .bool) =
        (LMonoTy.mkArrow' (intLtFunc (T := CoreLParams)).func.output
          ((intLtFunc (T := CoreLParams)).func.inputs.map Prod.snd)).subst Subst.empty := by
      simp [intLtFunc, binaryOp, LMonoTy.mkArrow', LMonoTy.subst_unfold, Subst.empty]
      rfl
    exact .app (.app (.op_in F₂_intLt hs ht) .fvar) .fvar
  · simp [LExpr.annotateFvars, Γ₂, Imperative.VarTyping.extend, LTy.toMonoType?]


/-! ## The Simplify theorem's hypotheses hold of `body₂`

Simplified from `Ctx.ofFactory F₂ []`, as `runSimplify` builds its context, `body₂` meets every
hypothesis of `checkedBody_overapproximatesTraces`: the context is fresh, its factory
meets the conditions of evaluator soundness, and the body is in the fragment with typed
expressions. -/

/-- The context the phase builds from `F₂` is fresh. -/
theorem base₂_fresh : (Ctx.ofFactory F₂ []).Fresh := Ctx.ofFactory_fresh _ _

/-- The declared functions: those of the factory, as the phase declares them. -/
def params₂ : Core.Logic.InitEnvWFParams :=
  { prefixIdents := [], declaredFuncs := fun f => decide (f.name ∈ F₂) }

/-- A procedure without parameters or contract: its live names are none, and Simplify
    assumes no input defined. -/
def proc₂ : Procedure := default

-- `body₂` is rewritten: the call `inc(m)` is expanded to its body.
/--
info: [var a : int := int.add(m, 1);, assert [lt]: int.lt(m, a);]
-/
#guard_msgs in
#eval (sweptBody (Ctx.ofFactory F₂ []) proc₂ body₂).map Std.format

-- The phase installs that rewritten body: it passes the def-use check, so the checked form
-- is the same. This is checked by running the compiled code, not proved: the kernel cannot
-- run Simplify's folding on the body.
/--
info: [var a : int := int.add(m, 1);, assert [lt]: int.lt(m, a);]
-/
#guard_msgs in
#eval (checkedBody (Ctx.ofFactory F₂ []) proc₂ body₂).map Std.format

/-- **The phase's theorem applies to `body₂`**, with every hypothesis discharged. -/
theorem body₂_over (π : String → Option Procedure) :
    Imperative.Specification.Transform.OverapproximatesTracesUptoWhen
      (Imperative.Trace.WeakensAssumes Imperative.BigStep.evalInterp)
      (EntryRel (Ctx.ofFactory F₂ []).factory Γ₂ body₂) (EnvAgreeOnLive (procLive proc₂))
      (Core.Logic.EventLang.coreBlock π) (Core.Logic.EventLang.coreBlock π)
      (fun ss => some (checkedBody (Ctx.ofFactory F₂ []) proc₂ ss))
      (fun ss => ss = body₂ ∧ BodyWF (Ctx.ofFactory F₂ []).factory Γ₂ ss) params₂ params₂ :=
  checkedBody_overapproximatesTraces π params₂ (Ctx.ofFactory F₂ []) proc₂ Γ₂
    base₂_fresh F₂_evalSoundWF body₂

/-- **The theorem on the swept body applies to `body₂`**: `F₂` brings in only its own
    operators, so the simplified body is well-formed without the phase's check. -/
theorem body₂_swept_over (π : String → Option Procedure) :
    Imperative.Specification.Transform.OverapproximatesTracesUptoWhen
      (Imperative.Trace.WeakensAssumes Imperative.BigStep.evalInterp)
      (EntryRel (Ctx.ofFactory F₂ []).factory Γ₂ body₂) (EnvAgreeOnLive (procLive proc₂))
      (Core.Logic.EventLang.coreBlock π) (Core.Logic.EventLang.coreBlock π)
      (fun ss => some (sweptBody (Ctx.ofFactory F₂ []) proc₂ ss))
      (fun ss => ss = body₂ ∧ BodyWF (Ctx.ofFactory F₂ []).factory Γ₂ ss) params₂ params₂ :=
  sweptBody_overapproximatesTraces π params₂ (Ctx.ofFactory F₂ []) proc₂ Γ₂
    base₂_fresh F₂_evalSoundWF F₂_opsClosed body₂

/-! ## A local named like a formal of an inlined function

`body₃` declares `n : bool` before calling `inc`, whose formal is `n : int`. Expanding
`inc(m)` substitutes `m` for the formal, so the local is not captured and keeps its type. -/

/-- `var n : bool; var a : int := inc(m); assert [lt]: Int.Lt(m, a);`. -/
def body₃ : List Statement :=
  Statement.init ⟨"n", ()⟩ (.forAll [] .bool) .nondet .empty :: body₂

-- The call is expanded and the local `n` is left alone.
/--
info: [var n : bool;, var a : int := int.add(m, 1);, assert [lt]: int.lt(m, a);]
-/
#guard_msgs in
#eval (checkedBody (Ctx.ofFactory F₂ []) proc₂ body₃).map Std.format

/-- **`BodyWF` holds of `body₃`.** -/
theorem body₃_wf : BodyWF F₂ Γ₂ body₃ := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · simp only [body₃, body₂, noCalls_eq_cons, noCalls_nil, Statement.noCalls,
      Imperative.Stmt.allSubstmts_cmd]
    rfl
  · simp only [body₃, body₂, Imperative.Block.noLoops_cons, Imperative.Block.noLoops_nil,
      Imperative.Stmt.noLoops_cmd, Bool.and_self]
  simp only [body₃, body₂, Block.exprsOKIn, Stmt.exprsOKIn, ExprOK, Expression.HasType,
    and_true, true_and, Statement.init, Imperative.Stmt.typedDefinedVars,
    Imperative.HasTypedVarsImp.typedDefinedVars, Imperative.CmdExt.typedDefinedVars,
    Imperative.Cmd.typedDefinedVars]
  refine ⟨⟨⟨.int, rfl, by decide, ?_, LExpr.typeCheck_to_HasTypeA ?_⟩, ?_, ?_⟩,
    ⟨⟨.bool, rfl, by decide, ?_, LExpr.typeCheck_to_HasTypeA ?_⟩, ?_, ?_⟩⟩
  · intro x hx
    simp only [LExpr.LExpr.getVars, List.mem_append, List.mem_singleton, List.not_mem_nil,
      false_or] at hx
    subst hx; simp [Γ₂, Imperative.VarTyping.extend]
  · simp [LExpr.annotateFvars, Γ₂, Imperative.VarTyping.extend, LTy.toMonoType?]
    rfl
  · exact .app (.op_in (tySubst := Subst.empty) F₂_inc (by simp [LFunc.opTypeSubst, incLFunc])
      (by simp [incLFunc, LMonoTy.mkArrow', LMonoTy.subst_unfold]; rfl)) .fvar
  · simp [LExpr.annotateFvars, Γ₂, Imperative.VarTyping.extend, LTy.toMonoType?]
  · intro x hx
    simp only [LExpr.LExpr.getVars, List.mem_append, List.mem_singleton, List.not_mem_nil,
      false_or] at hx
    rcases hx with rfl | rfl <;> simp [Γ₂, Imperative.VarTyping.extend]
  · simp [LExpr.annotateFvars, Γ₂, Imperative.VarTyping.extend, LTy.toMonoType?]
    rfl
  · have hs : LFunc.opTypeSubst (intLtFunc (T := CoreLParams)).func
        (.op default ⟨"Int.Lt", ()⟩ (some (.arrow .int (.arrow .int .bool)))) =
      some Subst.empty := by
      simp [LFunc.opTypeSubst, intLtFunc, binaryOp]
    have ht : LMonoTy.arrow .int (.arrow .int .bool) =
        (LMonoTy.mkArrow' (intLtFunc (T := CoreLParams)).func.output
          ((intLtFunc (T := CoreLParams)).func.inputs.map Prod.snd)).subst Subst.empty := by
      simp [intLtFunc, binaryOp, LMonoTy.mkArrow', LMonoTy.subst_unfold, Subst.empty]
      rfl
    exact .app (.app (.op_in F₂_intLt hs ht) .fvar) .fvar
  · simp [LExpr.annotateFvars, Γ₂, Imperative.VarTyping.extend, LTy.toMonoType?]

/-- **The phase's theorem applies to `body₃`.** -/
theorem body₃_over (π : String → Option Procedure) :
    Imperative.Specification.Transform.OverapproximatesTracesUptoWhen
      (Imperative.Trace.WeakensAssumes Imperative.BigStep.evalInterp)
      (EntryRel (Ctx.ofFactory F₂ []).factory Γ₂ body₃) (EnvAgreeOnLive (procLive proc₂))
      (Core.Logic.EventLang.coreBlock π) (Core.Logic.EventLang.coreBlock π)
      (fun ss => some (checkedBody (Ctx.ofFactory F₂ []) proc₂ ss))
      (fun ss => ss = body₃ ∧ BodyWF (Ctx.ofFactory F₂ []).factory Γ₂ ss) params₂ params₂ :=
  checkedBody_overapproximatesTraces π params₂ (Ctx.ofFactory F₂ []) proc₂ Γ₂
    base₂_fresh F₂_evalSoundWF body₃

/--
info:
'_private.StrataTest.Transform.SimplifyUserFuncTest.0.Core.Simplify.UserFuncTest.body₂_over'
depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms body₂_over

/-! ## The theorems rest on the standard axioms only -/

/--
info: 'Core.Simplify.sweptBody_overapproximatesTraces' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms sweptBody_overapproximatesTraces

/--
info: 'Core.Simplify.sweptBody_assertValid' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms sweptBody_assertValid

/--
info: 'Core.Simplify.simplifyPhase_over' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms simplifyPhase_over

/--
info: 'Core.Simplify.checkedBody_assertValid' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms checkedBody_assertValid

end Core.Simplify.UserFuncTest
