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
import Strata.Transform.Simplify.LawsFold
import Strata.Transform.SimplifyCorrect
-- `import all` of the precondition module, for the body of `Block.clashesWithFormals`.
import all Strata.Transform.Simplify.Precondition
meta import Strata.Transform.Simplify
meta import Strata.Transform.Simplify.Precondition
meta import Strata.Transform.Simplify.TargetGate
meta import Strata.DL.Lambda.IntBoolFactory

/-! # A small factory satisfying the precondition of the Simplify theorem

`F₂` holds two Core operators with concrete evaluators, `Int.Add` and `Int.Lt`, and one
user function with a body, `inc (n : int) : int := Int.Add(n, 1)`. -/

namespace Core.Simplify.LawsTest

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

/-- A function `F₂` resolves a name to is one of its three. -/
theorem F₂_getElem (f : String) (hf : f ∈ F₂) :
    F₂[f] = (intAddFunc (T := CoreLParams)).func ∨ F₂[f] = (intLtFunc (T := CoreLParams)).func ∨
      F₂[f] = incLFunc := by
  have hn := (Factory.mem_iff_mem_names F₂ f).mp hf
  obtain ⟨g, hg, hgn⟩ := Array.mem_map.mp hn
  obtain ⟨hs, hget⟩ := Factory.mem_name_eq_getElem hg hgn
  have : F₂[f]'hf = g := hget
  rw [this]
  exact F₂_mem hg

/-- What the concrete evaluators of `F₂` return: `Int.Add`'s an integer constant, `Int.Lt`'s
    a Boolean one. `inc` has none. -/
theorem F₂_ceval {fn : LFunc CoreLParams}
    (hfn : fn = (intAddFunc (T := CoreLParams)).func ∨ fn = (intLtFunc (T := CoreLParams)).func ∨
      fn = incLFunc)
    {ceval} (hc : fn.concreteEval = some ceval) {md : CoreLParams.Metadata}
    {opTy : Option LMonoTy} {args : List (LExpr CoreLParams.mono)}
    {r : LExpr CoreLParams.mono} (h : ceval md opTy args = some r) :
    (fn = (intAddFunc (T := CoreLParams)).func ∧ ∃ i, r = .intConst md i) ∨
      (fn = (intLtFunc (T := CoreLParams)).func ∧ ∃ b, r = .boolConst md b) := by
  rcases hfn with rfl | rfl | rfl
  · refine .inl ⟨rfl, ?_⟩
    simp only [intAddFunc, binaryOp, Option.some.injEq] at hc
    subst hc
    simp only at h
    repeat (split at h)
    all_goals first
      | exact ⟨_, (Option.some.inj h).symm⟩
      | exact absurd h (by simp)
  · refine .inr ⟨rfl, ?_⟩
    simp only [intLtFunc, binaryOp, Option.some.injEq] at hc
    subst hc
    simp only at h
    repeat (split at h)
    all_goals first
      | exact ⟨_, (Option.some.inj h).symm⟩
      | exact absurd h (by simp)
  · simp [incLFunc] at hc

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

/-- The one body of `F₂` is `inc`'s. -/
theorem F₂_body (f : String) (hf : f ∈ F₂) {body} (hb : (F₂[f]).body = some body) :
    F₂[f] = incLFunc ∧ body = incBody := by
  rcases F₂_getElem f hf with h | h | h <;> rw [h] at hb ⊢
  · simp [intAddFunc, binaryOp] at hb
  · simp [intLtFunc, binaryOp] at hb
  · simp only [incLFunc, Option.some.injEq] at hb
    exact ⟨rfl, hb.symm⟩

/-- **`F₂` satisfies the step well-formedness conditions** at every typing that leaves `inc`'s
    formal `n` untyped or types it `int`. -/
theorem F₂_stepWF (tyMap : Map CoreIdent LMonoTy)
    (hn : ∀ ty, Map.find? tyMap ⟨"n", ()⟩ = some ty → ty = .int) :
    Factory.StepWF F₂ tyMap where
  wt := .intro <| by
    intro f hf body hb
    obtain ⟨hf', rfl⟩ := F₂_body f hf hb
    rw [hf']
    refine ⟨LExpr.typeCheck_to_HasTypeA (by rfl), ?_⟩
    refine .app (.app .op (.fvar fun ty' h => ?_)) .const
    simp only [incLFunc, Map.find?, ↓reduceIte, Option.some.injEq] at h
    exact h
  evalWt := .intro <| by
    intro f hf ceval hc md args r tyS h _
    rcases F₂_ceval (F₂_getElem f hf) hc h with ⟨hf', i, rfl⟩ | ⟨hf', b, rfl⟩ <;> rw [hf']
    · simp only [intAddFunc, binaryOp, LMonoTy.int, LMonoTy.subst_unfold, List.map_nil]
      exact LExpr.typeCheck_to_HasTypeA (by rfl)
    · simp only [intLtFunc, binaryOp, LMonoTy.subst_bool]
      exact LExpr.typeCheck_to_HasTypeA (by rfl)
  bodyOps := .intro <| by
    intro f hf body S hb
    obtain ⟨-, rfl⟩ := F₂_body f hf hb
    rw [incBody_applyTypeSubst]
    have hs : LFunc.opTypeSubst (intAddFunc (T := CoreLParams)).func
        (.op default ⟨"Int.Add", ()⟩ (some (.arrow .int (.arrow .int .int)))) =
      some Subst.empty := by
      simp [LFunc.opTypeSubst, intAddFunc, binaryOp]
    have ht : LMonoTy.arrow .int (.arrow .int .int) =
        (LMonoTy.mkArrow' (intAddFunc (T := CoreLParams)).func.output
          ((intAddFunc (T := CoreLParams)).func.inputs.map Prod.snd)).subst Subst.empty := by
      simp [intAddFunc, binaryOp, LMonoTy.mkArrow', LMonoTy.subst_unfold, Subst.empty]
      rfl
    exact .app (.app (.op_in F₂_intAdd hs ht) .fvar) .const
  evalOps := .intro <| by
    intro f hf ceval md opTy args r hc h
    rcases F₂_ceval (F₂_getElem f hf) hc h.symm with ⟨-, i, rfl⟩ | ⟨-, b, rfl⟩ <;>
      exact .const
  bodyAnnot := .intro <| by
    intro f hf body S hb
    obtain ⟨-, rfl⟩ := F₂_body f hf hb
    rw [incBody_applyTypeSubst]
    exact .app (.app .op (.fvar fun ty' h => (hn ty' h).symm)) .const
  evalAnnot := .intro <| by
    intro f hf ceval md opTy args r hc h
    rcases F₂_ceval (F₂_getElem f hf) hc h.symm with ⟨-, i, rfl⟩ | ⟨-, b, rfl⟩ <;>
      exact .const

/-- **`F₂` is well-formed against the default type factory**: it declares no constructor. -/
theorem F₂_factWF :
    Factory.WF F₂ (TypeFactory.default : @TypeFactory CoreLParams.IDMeta) where
  factoryWF := F₂_wf
  constrWF := .intro <| by
    intro f hf hc
    rcases F₂_mem hf with rfl | rfl | rfl <;> exact absurd hc (by decide)
  tfWF := TypeFactoryWF.default

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

/-- **`Laws` holds of `F₂`.** -/
theorem F₂_laws : Laws F₂ := by
  refine ⟨⟨_, F₂_factWF⟩, fun tyMap hagree => F₂_stepWF tyMap fun ty hty => ?_⟩
  have hget := Factory.getElem?_some_getElem F₂_inc
  exact (hagree "inc" _ (by rw [hget]; rfl) ⟨"n", ()⟩ .int
    (by rw [hget]; exact List.Mem.head _) ty hty).1

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
hypothesis of `simplifyBody_overapproximatesTraces`: the context is fresh, the laws hold of
its fold factory, the body is in the fragment with typed expressions, the entry typing types no
variable the body declares, no variable clashes with a formal, and the simplified body passes
the target gate. -/

/-- The context the phase builds from `F₂` is fresh. -/
theorem base₂_fresh : (Ctx.ofFactory F₂ []).Fresh := Ctx.ofFactory_fresh _ _

/-- The laws hold of that context's fold factory. -/
theorem base₂_laws : Laws (Ctx.ofFactory F₂ []).foldFactory := Ctx.ofFactory_laws _ F₂_laws

/-- The entry typing types no variable `body₂` declares. -/
theorem body₂_declsUntyped :
    ∀ x ∈ Imperative.Block.definedVars (P := Expression) (C := Command) body₂ false,
      Γ₂ x = none := by
  intro x hx
  simp only [body₂, Imperative.Block.definedVars, Imperative.Stmt.definedVars,
    Imperative.HasVarsImp.definedVars, Imperative.CmdExt.definedVars, Imperative.Cmd.definedVars,
    List.mem_append, List.mem_singleton, List.not_mem_nil, or_false] at hx
  subst hx
  simp [Γ₂]

/-- No variable of `body₂` is named like a formal of `inc` at another type: `inc` is the one
    function of `F₂` with a body, its formal is `n`, and the body's variables are `m` and
    `a`. -/
theorem body₂_noClash :
    Block.clashesWithFormals (Ctx.ofFactory F₂ []).foldFactory Γ₂ body₂ = false := by
  unfold Block.clashesWithFormals
  rw [List.any_eq_false]
  intro ⟨x, ty⟩ hx
  rw [Bool.not_eq_true, List.any_eq_false]
  intro ⟨y, fty⟩ hy
  simp only [List.mem_flatMap, List.mem_filter, Array.mem_toList_iff] at hy
  obtain ⟨g, ⟨hg, hb⟩, hyin⟩ := hy
  obtain ⟨fn, hfn, rfl⟩ := withoutInline_mem_toArray (c := []) (F := F₂) hg
  obtain ⟨attr, he⟩ := stripInline_eq [] fn
  rw [he] at hb hyin
  rcases F₂_mem hfn with rfl | rfl | rfl
  · simp [intAddFunc, binaryOp] at hb
  · simp [intLtFunc, binaryOp] at hb
  · have hyin' : (y, fty) = (⟨"n", ()⟩, LMonoTy.int) := List.mem_singleton.mp hyin
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hyin'
    have hxn : x ≠ ⟨"n", ()⟩ := by
      simp only [typeList, List.mem_append, List.mem_filterMap, Option.map_eq_some_iff] at hx
      rcases hx with ⟨z, -, w, hw, hzw⟩ | hd
      · simp only [Prod.mk.injEq] at hzw
        obtain ⟨rfl, -⟩ := hzw
        unfold Γ₂ at hw
        split at hw
        · rename_i h; rw [h]; simp
        · cases hw
      · simp only [body₂, Imperative.Block.declaredTypes, Imperative.Stmt.declaredTypes,
          Imperative.HasTypedVarsImp.typedDefinedVars, Imperative.CmdExt.typedDefinedVars,
          Imperative.Cmd.typedDefinedVars, Statement.init, Statement.assert, List.append_nil,
          List.mem_singleton, Prod.mk.injEq] at hd
        rw [hd.1]; simp
    simp only [Bool.and_eq_true, beq_iff_eq, not_and]
    exact fun h => absurd h.symm hxn

/-- The declared functions: those of the factory, as the phase declares them. -/
def params₂ : Core.Logic.InitEnvWFParams := factoryParams (Ctx.ofFactory F₂ []).factory

/-- The live names: none, as for a procedure without outputs or contract. -/
def live₂ : Std.HashSet String := {}

-- `body₂` is rewritten: the call `inc(m)` is expanded to its body.
/--
info: (some [var a : int := int.add(m, 1);, assert [lt]: int.lt(m, a);])
-/
#guard_msgs in
#eval (simplifyBody (Ctx.ofFactory F₂ []) [] live₂ body₂).map (·.map Std.format)

-- The phase installs that rewritten body: it passes the def-use check, so the checked form
-- is the same. This is checked by running the compiled code, not proved: the kernel cannot
-- run Simplify's folding on the body.
/--
info: (some [var a : int := int.add(m, 1);, assert [lt]: int.lt(m, a);])
-/
#guard_msgs in
#eval (simplifyBodyChecked (Ctx.ofFactory F₂ []) [] live₂ body₂).map (·.map Std.format)

/-- **The phase's theorem applies to `body₂`**, with every hypothesis discharged. -/
theorem body₂_over (π : String → Option Procedure) :
    Imperative.Specification.Transform.OverapproximatesTracesUptoWhen
      (Imperative.Trace.WeakensAssumes Imperative.BigStep.evalInterp)
      (EntryRel (Ctx.ofFactory F₂ []).factory Γ₂ body₂) (EnvAgreeOnLive live₂)
      (Core.Logic.EventLang.coreBlock π) (Core.Logic.EventLang.coreBlock π)
      (simplifyBodyChecked (Ctx.ofFactory F₂ []) [] live₂)
      (fun ss => ss = body₂ ∧ BodyWF (Ctx.ofFactory F₂ []).factory Γ₂ ss) params₂ params₂ :=
  simplifyBodyChecked_overapproximatesTraces π params₂ (Ctx.ofFactory F₂ []) [] live₂ Γ₂
    base₂_fresh base₂_laws body₂ body₂_noClash body₂_declsUntyped (fun _ h => h)

/--
info:
'_private.StrataTest.Transform.SimplifyLawsTest.0.Core.Simplify.LawsTest.body₂_over'
depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms body₂_over

/-! ## The theorems rest on the standard axioms only -/

/--
info: 'Core.Simplify.simplifyBody_overapproximatesTraces' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms simplifyBody_overapproximatesTraces

/--
info: 'Core.Simplify.simplifyBody_assertValid' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms simplifyBody_assertValid

/--
info: 'Core.Simplify.simplifyPhase_over' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms simplifyPhase_over

/--
info: 'Core.Simplify.simplifyBodyChecked_assertValid' depends on axioms:
[propext, Classical.choice, Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms simplifyBodyChecked_assertValid

/-! ## A function with a polymorphic formal

`pid <a> (x : a) : a := x` reads its formal at a type variable. Each instantiation of `a`
annotates `x` differently, so no typing that types `x` agrees with every instance of the body.
`AgreesOnFormals` leaves such a formal untyped, so the body is annotated by every typing it
admits; and the clash check rejects a body that declares a variable named like it. -/

/-- `pid <a> (x : a) : a := x`. -/
def pidLFunc : LFunc CoreLParams :=
  { name := ⟨"pid", ()⟩, typeArgs := ["a"], inputs := [(⟨"x", ()⟩, .ftvar "a")],
    output := .ftvar "a", body := some (.fvar default ⟨"x", ()⟩ (some (.ftvar "a"))) }

/-- The one-function factory. -/
def Fp : Lambda.Factory CoreLParams := Factory.ofArray #[pidLFunc]

/-- `Fp` resolves every name it holds to `pid`. -/
theorem Fp_getElem (f : String) (hf : f ∈ Fp) : Fp[f] = pidLFunc := by
  obtain ⟨g, hg, hgn⟩ := Array.mem_map.mp ((Factory.mem_iff_mem_names Fp f).mp hf)
  obtain ⟨_, hget⟩ := Factory.mem_name_eq_getElem hg hgn
  have : Fp[f]'hf = g := hget
  rw [this]
  have := Factory.ofArray_mem hg
  simpa using this

/-- **`pid`'s body is annotated by every typing that agrees with the formals**, at every
    instantiation of its type variable. -/
theorem Fp_bodyAnnotated (tyMap : Map CoreIdent LMonoTy) (h : AgreesOnFormals Fp tyMap) :
    Factory.BodyAnnotated Fp tyMap := .intro <| by
  intro f hf body S hb
  have hf' := Fp_getElem f hf
  have hun : ∀ τ, Map.find? tyMap ⟨"x", ()⟩ ≠ some τ := fun τ hτ => by
    have := (h f hf (by rw [hf']; rfl) ⟨"x", ()⟩ (.ftvar "a")
      (by rw [hf']; exact List.Mem.head _) τ hτ).2
    simp [LMonoTy.freeVars] at this
  rw [hf'] at hb
  simp only [pidLFunc, Option.some.injEq] at hb
  subst hb
  unfold LExpr.applyTypeSubst
  split
  · exact .fvar fun ty' hτ => absurd hτ (hun ty')
  · simp only [LExpr.replaceUserProvidedType]
    exact .fvar fun ty' hτ => absurd hτ (hun ty')

/-- The entry typing of the clash tests: nothing is typed. -/
private def Γp : Imperative.VarTyping Expression := fun _ => none

-- A body declaring a variable named like `pid`'s polymorphic formal is a clash, at any type.
#guard Block.clashesWithFormals Fp Γp
  [Statement.init ⟨"x", ()⟩ (.forAll [] .int) .nondet .empty]
#guard !Block.clashesWithFormals Fp Γp
  [Statement.init ⟨"y", ()⟩ (.forAll [] .int) .nondet .empty]

end Core.Simplify.LawsTest
