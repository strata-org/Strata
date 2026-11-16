/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Factory
public import Strata.DL.Lambda.LExprTypeEnv
import all Strata.Languages.Core.Factory
import all Strata.DL.Lambda.LExprTypeEnv
import all Strata.DL.Lambda.TypeFactory
import all Strata.DL.Lambda.FactoryWF
import Strata.DL.Lambda.FactoryProps
import Strata.Util.Tactics

/-! # Properties of the Core factory and the builtin known-type table

Key theorems: `Factory_opTypes_wellKinded` (every `Core.Factory` operator type
is well kinded under the builtin table), `wellKinded_of_knownArityOkB`, and
`Factory_all_of_WFFactoryArray` (a check holding on the builtin array holds on
`Core.Factory`), and `mapConstFunc_eval_ground` / `seqEmptyFunc_eval_ground` (the
evaluators that read the operator's type annotation evaluate only at a ground one). -/

public section

namespace Core

open Lambda

/-- The name/arity pairs of `Core.KnownLTys`, last entry first, so that the
    first pair for a name is the one `Core.KnownTypes` keeps. -/
def knownArities : List (String × Nat) :=
  ((KnownLTys.map (·.toKnownType!)).map (fun x => (x.name, x.arity))).reverse

/-- Depth-bounded check that every type constructor in `ty` is applied at the
    arity `knownArities` lists for it. A `true` result means every constructor
    is applied at its listed arity; `false` can also mean that `ty` nests
    constructors more than `depth` deep. The check recurses on `depth` because
    `getTypeConsArities` does not reduce in the kernel, so `decide` could not
    evaluate a check built on it. -/
def knownArityOkB (depth : Nat) (ty : LMonoTy) : Bool :=
  match depth, ty with
  | _, .ftvar _ => true
  | _, .bitvec _ => true
  | 0, .tcons _ _ => false
  | d + 1, .tcons name args =>
    (List.findSome? (fun q => if q.1 == name then some q.2 else none)
        knownArities == some args.length) &&
      args.all (knownArityOkB d)

/-- Looking a name up in the builtin known-types table is the same as scanning
    the name/arity list it is built from. -/
theorem knownTypes_getElem? (nm : String) :
    (Core.KnownTypes : Lambda.KnownTypes)[nm]? =
      List.findSome? (fun p => if p.1 == nm then some p.2 else none)
        knownArities := by
  show (Std.HashMap.ofList
    ((Core.KnownLTys.map (fun ty => ty.toKnownType!)).map
      (fun x => (x.name, x.arity))))[nm]? = _
  rw [Std.HashMap.ofList_eq_insertMany_empty,
    Std.HashMap.getElem?_insertMany_list, Std.HashMap.getElem?_empty,
    Option.or_none, List.findSomeRev?_eq_findSome?_reverse, knownArities]

/-- Only the names the builtin table is built from are registered in it. -/
theorem mem_knownArities_of_mem_knownTypes {nm : String}
    (h : nm ∈ (Core.KnownTypes : Lambda.KnownTypes)) :
    nm ∈ knownArities.map Prod.fst := by
  rw [Std.HashMap.mem_iff_isSome_getElem?, knownTypes_getElem?] at h
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h
  obtain ⟨p, hp, hpe⟩ := List.exists_of_findSome?_eq_some hv
  elim_err hpe with hbeq
  rw [← beq_iff_eq.mp hbeq]
  exact List.mem_map_of_mem hp

/-- A type passing the depth-bounded check applies every type constructor it
    mentions at the arity the builtin table registers that constructor at. -/
theorem wellKinded_of_knownArityOkB (depth : Nat) :
    ∀ ty : LMonoTy, knownArityOkB depth ty = true →
      LMonoTy.WellKinded (fun n => Core.KnownTypes[n]?) ty := by
  induction depth with
  | zero =>
    intro ty h
    match ty with
    | .ftvar _ | .bitvec _ =>
      intro ref n hmem; simp [Lambda.getTypeConsArities] at hmem
    | .tcons _ _ => simp [knownArityOkB] at h
  | succ d ih =>
    intro ty h
    match ty with
    | .ftvar _ | .bitvec _ =>
      intro ref n hmem; simp [Lambda.getTypeConsArities] at hmem
    | .tcons name args =>
      simp only [knownArityOkB, Bool.and_eq_true, List.all_eq_true] at h
      obtain ⟨hhead, hargs⟩ := h
      intro ref n hmem
      simp only [Lambda.getTypeConsArities, List.mem_cons] at hmem
      rcases hmem with heq | hmem
      · simp only [Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl⟩ := heq
        show Core.KnownTypes[ref]? = some args.length
        rw [knownTypes_getElem?]
        exact beq_iff_eq.mp hhead
      · rw [List.mem_flatMap] at hmem
        obtain ⟨arg, harg, hmem'⟩ := hmem
        exact ih arg (hargs arg harg) ref n hmem'

/-- A Boolean check that holds on every entry of the built-in function array
    holds on every function of `Core.Factory`. -/
theorem Factory_all_of_WFFactoryArray (p : LFunc CoreLParams → Bool)
    (hall : (WFFactoryArray.toList.all fun wf => p wf.func) = true) :
    ∀ f ∈ Core.Factory.toArray, p f = true := by
  intro f hf
  have hfArr :
      f ∈ (Lambda.Factory.ofArray (WFFactoryArray.map (·.func))).toArray :=
    hf
  obtain ⟨wf, hwf, rfl⟩ := Array.mem_map.mp (Lambda.Factory.ofArray_mem hfArr)
  exact List.all_eq_true.mp hall wf (Array.mem_toList_iff.mpr hwf)

/-- In a context whose known types are Core's builtin table, the type of every
    `Core.Factory` operator, as the arrow from its inputs to its output, is well
    kinded. -/
theorem Factory_opTypes_wellKinded {T : LExprParams} (C : LContext T)
    (hC : C.knownTypes = Core.KnownTypes) :
    ∀ f ∈ Core.Factory.toArray,
      C.WellKindedTy (LMonoTy.mkArrow' f.output (f.inputs.map Prod.snd)) := by
  have hall : (WFFactoryArray.toList.all fun wf =>
      knownArityOkB 16
        (LMonoTy.mkArrow' wf.func.output (wf.func.inputs.map Prod.snd))) =
        true := by
    simp only [WFFactoryArray, Array.toList_appendList]
    decide +kernel
  intro f hf
  have hwk := wellKinded_of_knownArityOkB 16 _
    (Factory_all_of_WFFactoryArray
      (fun f =>
        knownArityOkB 16 (LMonoTy.mkArrow' f.output (f.inputs.map Prod.snd)))
      hall f hf)
  simp only [LContext.WellKindedTy, hC]
  exact hwk

/-! ### Evaluators that read the operator's type annotation

`mapConst` and `Sequence.empty` read their sorts from the annotation, so, following the
convention of `ConcreteEval`, they evaluate only at a ground annotation. -/

/-- The literal evaluator of `mapConst` returns a literal only at a ground annotation. -/
private theorem AggregateLitEval.mapConst_ground {ty : Option LMonoTy} {cs : List LConst}
    {r : LConst} (h : AggregateLitEval.mapConst ty cs = some r) :
    ∃ t s, ty = some t ∧ t.toSort? = some s := by
  unfold AggregateLitEval.mapConst at h
  split at h
  · rename_i t _
    split at h
    · rename_i hts
      exact ⟨t, _, rfl, hts⟩
    · cases h
  · cases h

/-- The literal evaluator of `Sequence.empty` returns a literal only at a ground annotation. -/
private theorem AggregateLitEval.seqEmpty_ground {ty : Option LMonoTy} {cs : List LConst}
    {r : LConst} (h : AggregateLitEval.seqEmpty ty cs = some r) :
    ∃ t s, ty = some t ∧ t.toSort? = some s := by
  unfold AggregateLitEval.seqEmpty at h
  split at h
  · rename_i t
    split at h
    · rename_i hts
      exact ⟨t, _, rfl, hts⟩
    · cases h
  · cases h

/-- A `polyLitOp` evaluator returns a result only where its literal evaluator does, at the
    same annotation. -/
private theorem polyLitOp_eval_some {n : CoreLParams.Identifier} {ta inputs output ev axs pre}
    {h1 h2 h3 h4 h5 h6} {ceval : ConcreteEval CoreLParams}
    (hce : (polyLitOp n ta inputs output ev axs pre h1 h2 h3 h4 h5 h6).func.concreteEval =
      some ceval)
    {md : CoreLParams.Metadata} {ty : Option LMonoTy} {args : List (LExpr CoreLParams.mono)}
    {r : LExpr CoreLParams.mono} (h : ceval md ty args = some r) :
    ∃ cs c, ev ty cs = some c := by
  cases hce
  simp only at h
  split at h
  · obtain ⟨c, hc, -⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨cs, -, hev⟩ := Option.bind_eq_some_iff.mp hc
    exact ⟨cs, c, hev⟩
  · cases h

/-- **`mapConst` evaluates only at a ground annotation**: its concrete evaluator returns a
    result only when the operator's annotation is a type without type variables. -/
theorem mapConstFunc_eval_ground {ceval : ConcreteEval CoreLParams}
    (hce : mapConstFunc.func.concreteEval = some ceval) {md : CoreLParams.Metadata}
    {ty : Option LMonoTy} {args : List (LExpr CoreLParams.mono)} {r : LExpr CoreLParams.mono}
    (h : ceval md ty args = some r) : ∃ t s, ty = some t ∧ t.toSort? = some s := by
  obtain ⟨cs, c, hev⟩ := polyLitOp_eval_some hce h
  exact AggregateLitEval.mapConst_ground hev

/-- **`Sequence.empty` evaluates only at a ground annotation**: its concrete evaluator returns
    a result only when the operator's annotation is a type without type variables. -/
theorem seqEmptyFunc_eval_ground {ceval : ConcreteEval CoreLParams}
    (hce : seqEmptyFunc.func.concreteEval = some ceval) {md : CoreLParams.Metadata}
    {ty : Option LMonoTy} {args : List (LExpr CoreLParams.mono)} {r : LExpr CoreLParams.mono}
    (h : ceval md ty args = some r) : ∃ t s, ty = some t ∧ t.toSort? = some s := by
  obtain ⟨cs, c, hev⟩ := polyLitOp_eval_some hce h
  exact AggregateLitEval.seqEmpty_ground hev

end Core

end -- public section
