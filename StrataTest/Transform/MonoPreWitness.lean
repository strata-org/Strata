/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

import all Strata.Transform.MonomorphizeInstances
import Strata.Transform.MonomorphizeFunctionsCorrect
import Strata.DL.Lambda.FactoryProps
meta import Strata.Transform.MonomorphizeFunctions

/-! # `MonoPre` is satisfiable

`monomorphizeFunctions_reflectsLemmas` assumes `MonoPre`. This file exhibits a state and a
program that meet it, so the theorem is not vacuous: a factory of the operations the
same-theory fragment reads, each without body or evaluator, and a program that declares the
polymorphic identity function and a lemma that uses it at `int`, so the pass changes it.
-/

namespace Core.MonomorphizeFunctions.MonoPreWitness

open Lambda

/-- A monomorphic Boolean constant named `n`, with no body and no evaluator. -/
def fragFn (n : String) : LFunc CoreLParams :=
  { name := ⟨n, ()⟩, inputs := [], output := .bool }

/-- The factory: one such function for each name the same-theory fragment reads. -/
def witnessFactory : Lambda.Factory CoreLParams :=
  .ofArray (fragmentOpNames.map fragFn).toArray

/-- `id<a>(x : a) : a := x`. -/
def idFn : Function :=
  { name := ⟨"id", ()⟩, typeArgs := ["a"], inputs := [(⟨"x", ()⟩, .ftvar "a")],
    output := .ftvar "a", body := some (.fvar Core.coreLoc ⟨"x", ()⟩ (some (.ftvar "a"))) }

/-- `id`, as an operator annotated with its instance at `int`. -/
def idAtInt : Expression.Expr :=
  .op Core.coreLoc ⟨"id", ()⟩ (some (Lambda.LMonoTy.mkArrow' .int [.int]))

/-- `lemma l : forall x : int :: id(x) == x`, which uses `id` at `int`, so the pass adds the
    copy `$__mono#id#int` and renames the operator to it. -/
def idLemma : Lemma :=
  { name := "l", e := .quant Core.coreLoc .all "x" (some .int) (.bvar Core.coreLoc 0)
      (.eq Core.coreLoc (.app Core.coreLoc idAtInt (.bvar Core.coreLoc 0)) (.bvar Core.coreLoc 0)) }

/-- The program: the polymorphic identity and the lemma. -/
def witnessProgram : Program :=
  { decls := [.func idFn .empty, .lemma idLemma .empty] }

/-- The state the phase starts in, over the factory. -/
def witnessState : Transform.CoreTransformState :=
  { Transform.CoreTransformState.emp with factory := witnessFactory }

/-- The names the pass's output declares. -/
def witnessOutputNames : Except String (List String) :=
  match Transform.run witnessProgram monomorphizeFunctions witnessState with
  | .ok (_, p') => .ok (p'.decls.map (·.name.name))
  | .error e => .error (toString e)

-- The pass changes this program: it adds the copy `$__mono#id#int` and drops `id`, which
-- nothing uses afterwards.
/-- info: Except.ok ["$__mono#id#int", "l"] -/
#guard_msgs in
#eval witnessOutputNames

/-- Every function of the factory is one of the fragment's constants. -/
theorem mem_witnessFactory {f : LFunc CoreLParams} (h : f ∈ witnessFactory.toArray) :
    ∃ n ∈ fragmentOpNames, f = fragFn n := by
  have := Lambda.Factory.ofArray_mem h
  simpa [List.mem_map, eq_comm] using this

/-- Each fragment constant is well formed: no inputs, no type parameters, no body. -/
theorem fragFn_wf (n : String) : LFuncWF (fragFn n) where
  arg_nodup := by simp [fragFn]
  typeArgs_nodup := by simp [fragFn]
  inputs_typevars_in_typeArgs := by simp [fragFn, ListMap.values]
  output_typevars_in_typeArgs := by simp [fragFn, LMonoTy.freeVars, LMonoTys.freeVars]
  body_freevars := by simp [fragFn]
  precond_freevars := by simp [fragFn]
  constr_no_eval := by simp [fragFn]
  typeArgs_no_gen_prefix := by simp [fragFn]
  concreteEval_argmatch := by simp [fragFn]
  body_or_concreteEval := by simp [fragFn]
  concreteEval_eraseMetadata := by simp [fragFn]
  concreteEval_freeVars := by simp [fragFn]
  shortCircuit_substFvars := by simp [fragFn]

/-- **`MonoPre` holds of the witness.** -/
theorem monoPre_witness : MonoPre witnessState witnessProgram := by
  have hF : ∀ f ∈ witnessFactory.toArray, ∃ n ∈ fragmentOpNames, f = fragFn n :=
    fun _ h => mem_witnessFactory h
  have hP : witnessProgram.decls.flatMap progFns = [idFn] := rfl
  have hC : ∀ f ∈ contributed witnessState.factory witnessProgram.decls,
      (∃ n ∈ fragmentOpNames, f = fragFn n) ∨ f = idFn.toLFunc := by
    intro f hf
    simp only [contributed, List.mem_append, Array.mem_toList_iff] at hf
    rcases hf with h | h
    · exact .inl (hF f h)
    · right; simpa [witnessProgram, declFns] using h
  have hD : ((contributed witnessState.factory witnessProgram.decls).map (·.name.name)).Nodup := by
    simp only [contributed, List.map_append, List.nodup_append]
    refine ⟨Lambda.Factory.name_nodup _, by simp [witnessProgram, declFns, idFn], ?_⟩
    intro a ha b hb
    simp only [List.mem_map, Array.mem_toList_iff] at ha
    obtain ⟨f, hf, rfl⟩ := ha
    obtain ⟨n, hn, rfl⟩ := hF f hf
    simp only [witnessProgram, idFn, List.flatMap_cons, declFns, LFuncDefined.toLFunc,
      List.flatMap_nil, List.append_nil, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hb
    subst hb
    simp only [fragmentOpNames, List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [fragFn]
  refine ⟨?noProcs, ?distinct, ?unmangled, ?typed, ?evals, ?noConstr, ?fragOps, ?ground,
    ?sigTypeArgs, ?plainAnnots, ?fragment, ?baseEvalSound, ?datatypesProvable,
    ?monoOpsAnnotated⟩
  case noProcs => simp [Specification.Analysis.NoProcedures, witnessProgram, Decl.kind]
  case unmangled =>
    intro f hf
    rcases hC f hf with ⟨n, hn, rfl⟩ | rfl
    · simp only [fragmentOpNames, List.mem_cons, List.not_mem_nil, or_false] at hn
      rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact ⟨by decide, by simp [fragFn]⟩
    · refine ⟨by decide, ?_⟩
      intro e he
      simp only [LFuncDefined.toLFunc, idFn, Option.toList_some, List.append_nil, List.mem_cons,
        List.not_mem_nil, or_false] at he
      subst he
      intro o ho
      simp [LExpr.getOps] at ho
  case typed =>
    refine ⟨fun f hf => ?_, fun f hf => ?_⟩
    · obtain ⟨n, -, rfl⟩ := hF f hf
      exact ⟨by simp [fragFn], by simp [fragFn]⟩
    · rw [hP, List.mem_singleton] at hf
      subst hf
      refine ⟨fun b hb => ?_, by simp [idFn, LFuncDefined.toLFunc]⟩
      simp only [LFuncDefined.toLFunc, idFn, Option.some.injEq] at hb
      subst hb
      exact .fvar
  case evals =>
    intro f hf c hc
    rcases hC f hf with ⟨n, -, rfl⟩ | rfl
    · simp [fragFn] at hc
    · simp [idFn, LFuncDefined.toLFunc] at hc
  case noConstr =>
    refine ⟨fun f hf => ?_, fun f hf => ?_⟩
    · obtain ⟨n, -, rfl⟩ := hF f hf
      rfl
    · rw [hP, List.mem_singleton] at hf
      subst hf
      rfl
  case fragOps =>
    intro n hn
    refine ⟨fragFn n, ?_, rfl, rfl⟩
    have hmem : fragFn n ∈ (fragmentOpNames.map fragFn).toArray := by
      simpa using ⟨n, hn, rfl⟩
    exact Lambda.Factory.getElem?_is_some_implies_mem
      (Lambda.Factory.get?_ofArray_of_mem hmem (by decide))
  case ground =>
    simp only [groundInstantiationsB, Bool.and_eq_true, List.all_eq_true]
    refine ⟨by decide, fun f hf => ?_⟩
    obtain ⟨n, -, rfl⟩ := hF f (Array.mem_toList_iff.mp hf)
    rfl
  case sigTypeArgs =>
    simp only [sigTypeArgsB, Bool.and_eq_true, List.all_eq_true]
    refine ⟨by decide, fun f hf => ?_⟩
    obtain ⟨n, -, rfl⟩ := hF f (Array.mem_toList_iff.mp hf)
    rfl
  case plainAnnots =>
    simp only [plainAnnotsB, Bool.and_eq_true, List.all_eq_true]
    refine ⟨by decide, fun f hf => ?_⟩
    obtain ⟨n, -, rfl⟩ := hF f (Array.mem_toList_iff.mp hf)
    rfl
  case datatypesProvable => decide
  case fragment =>
    refine ⟨fun fn hfn => ?_, fun fn hfn ceval hc => ?_, fun fn hfn _ => ?_⟩ <;>
      obtain ⟨n, -, rfl⟩ := hF fn hfn
    · rfl
    · simp [fragFn] at hc
    · rfl
  case baseEvalSound =>
    intro fn hfn
    obtain ⟨n, hn, rfl⟩ := hF fn hfn
    refine ⟨⟨fun c hc => by simp [fragFn] at hc, fun c hc => by simp [fragFn] at hc⟩, ?_, rfl, rfl⟩
    simp only [fragmentOpNames, List.mem_cons, List.not_mem_nil, or_false] at hn
    exact fragFn_wf n
  case distinct => exact hD
  case monoOpsAnnotated =>
    refine ⟨fun a md h => ?_, fun l md h => ?_, fun f md b h hb => ?_⟩
    · simp [witnessProgram] at h
    · simp only [witnessProgram, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h <;> cases h
      have hid : idFn.toLFunc ∈ contributed witnessState.factory witnessProgram.decls := by
        simp [contributed, witnessProgram, declFns]
      have hR : (Specification.Analysis.runtimeFactoryOf witnessState.factory
          witnessProgram.decls)["id"]? = some idFn.toLFunc :=
        getElem?_runtimeFactoryOf_of_contributed hD hid
      refine ⟨trivial, ⟨⟨?_, trivial⟩, trivial⟩⟩
      show MonoOpsAnnotated _ (.op Core.coreLoc ⟨"id", ()⟩ _)
      unfold MonoOpsAnnotated
      rw [hR]
      simp [idFn, LFuncDefined.toLFunc]
    · simp only [witnessProgram, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with h | h <;> cases h
      simp only [idFn, Option.some.injEq] at hb
      subst hb
      trivial

end Core.MonomorphizeFunctions.MonoPreWitness
