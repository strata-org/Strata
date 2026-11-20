/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Procedure
public import Strata.DL.Imperative.StmtCFGCallSemantics
import all Strata.Languages.Core.Procedure
import all Strata.Languages.Core.StatementSemanticsProps
import Strata.Util.OrderedSetProps
import Strata.Languages.Core.StatementProps
import Strata.DL.Lambda.LExprWFProps
import Strata.DL.Lambda.LTyUnifyProps

/-! # Properties of Core procedures

Key results:

- `Procedure.mapExprs_id` — `Procedure.mapExprs` with the identity is the
  identity (the procedure-level analog of `Statements.mapExprs_id`).
- `Procedure.Header.keys_getInoutParams`, `Procedure.Header.keys_getOutputOnlyParams` —
  the keys of Core's inout and output-only formals are the generic
  `Calls.inoutParams` / `Calls.outputOnlyParams`.
- `Procedure.renameTypeArgs_names` — renaming type parameters keeps a
  procedure's name and parameter names.
- `Procedure.oldAliases_mem` — every alias `(old x, x)` has `x` among the parameters.
- `Procedure.instantiateTypes_of_typeArgs_nil` — a monomorphic procedure's only instance is
  itself, at `[]`, and `Procedure.instantiateTypes_of_typeArgs_singleton` (with
  `_singleton_inv`) gives the instances of a procedure with one type parameter;
  `Procedure.instantiateTypes_own_typeArgs` gives a
  procedure's instance at its own type parameters, the procedure without them
  (`Procedure.mapTys_id`); `Procedure.forall_instance_of_typeArgs_nil` and
  `Procedure.forall_instance_of_typeArgs_singleton` turn a property of the procedure
  into one of all its instances, `Procedure.typeInstantiatedCallee_of_typeArgs_nil` and
  `Procedure.typeInstantiatedCallee_of_typeArgs_singleton` give the procedure a call to it runs,
  and `Procedure.forall_typeInstantiatedCallee_of_typeArgs_nil` does
  the same for every procedure of a table without polymorphic procedures.
-/

public section

namespace Core

/-- The keys of Core's inout formals are the generic `Calls.inoutParams`. -/
theorem Procedure.Header.keys_getInoutParams (h : Procedure.Header) :
    ListMap.keys h.getInoutParams = Imperative.Calls.inoutParams (P := Expression) h :=
  listMap_keys_filter _ _

/-- A name is an in-out parameter exactly when it is both an input and an output. -/
theorem Procedure.Header.mem_keys_getInoutParams (h : Procedure.Header) (g : CoreIdent) :
    g ∈ h.getInoutParams.keys ↔ g ∈ h.inputs.keys ∧ g ∈ h.outputs.keys := by
  unfold Procedure.Header.getInoutParams Core.getInoutParams
  rw [listMap_keys_filter _ h.inputs]
  simp only [List.mem_filter, List.contains_iff_mem]

/-- The keys of Core's output-only formals are the generic `Calls.outputOnlyParams`. -/
theorem Procedure.Header.keys_getOutputOnlyParams (h : Procedure.Header) :
    ListMap.keys h.getOutputOnlyParams = Imperative.Calls.outputOnlyParams (P := Expression) h :=
  listMap_keys_filter (fun _ => !_) _

/-- Renaming type parameters keeps a procedure's name and parameter names. -/
theorem Procedure.renameTypeArgs_names (proc : Procedure) (ren : List (String × String)) :
    (proc.renameTypeArgs ren).header.name = proc.header.name ∧
    (proc.renameTypeArgs ren).header.inputs.keys = proc.header.inputs.keys ∧
    (proc.renameTypeArgs ren).header.outputs.keys = proc.header.outputs.keys :=
  ⟨rfl, ListMap.keys_map_values _ _, ListMap.keys_map_values _ _⟩

/-- `Procedure.mapExprs` with the identity is the identity. -/
theorem Procedure.mapExprs_id (p : Procedure) : Procedure.mapExprs id p = p := by
  have hmap : ∀ (lm : ListMap CoreLabel Procedure.Check),
      lm.map (fun (l, c) => (l, { c with expr := id c.expr })) = lm := by
    intro lm
    have : ∀ x : CoreLabel × Procedure.Check,
        (fun (l, c) => (l, { c with expr := id c.expr })) x = x := by
      rintro ⟨l, c⟩; rfl
    exact (List.map_congr_left (fun x _ => this x)).trans (List.map_id lm)
  cases p with
  | mk header spec body =>
    cases spec with
    | mk pre post =>
      simp only [Procedure.mapExprs, hmap]
      cases body with
      | structured ss =>
        simp only [Imperative.Procedure.mk.injEq, Imperative.Body.structured.injEq, true_and]
        exact Statements.mapExprs_id ss
      | cfg c => rfl

/-- A structured body calls exactly the procedures called by its statements. -/
@[simp] theorem Procedure.Body.calledProcedureNames_structured (ss : Statements) :
    Procedure.Body.calledProcedureNames (.structured ss)
      = Statements.calledProcedureNames ss := by
  rw [Procedure.Body.calledProcedureNames]

/-- A control-flow-graph body has no called procedure names. -/
@[simp] theorem Procedure.Body.calledProcedureNames_cfg (g : DetCFG) :
    Procedure.Body.calledProcedureNames (.cfg g) = [] := by
  rw [Procedure.Body.calledProcedureNames]

/-- A procedure's callees are exactly the callees of its body. -/
@[simp] theorem Procedure.calledProcedureNames_eq_body (p : Procedure) :
    Procedure.calledProcedureNames p = Procedure.Body.calledProcedureNames p.body := by
  rw [Procedure.calledProcedureNames]

/-- Every alias `(old x, x)` of `p` has `x` among the parameters of `p`
    (`Procedure.entryParams`). -/
theorem Procedure.oldAliases_mem (p : Procedure) :
    ∀ q ∈ Procedure.oldAliases p, q.2 ∈ Procedure.entryParams p := fun _ hq => by
  obtain ⟨⟨x, _⟩, hx, rfl⟩ := List.mem_map.1 hq
  have hk := ((p.header.mem_keys_getInoutParams x).1
    (ListMap.keys_eq_map_fst _ ▸ List.mem_map_of_mem (f := Prod.fst) hx)).1
  obtain ⟨⟨y, ty⟩, hy, rfl⟩ := List.mem_map.1 (ListMap.keys_eq_map_fst _ ▸ hk)
  exact Strata.Util.OrderedSet.mem_eraseDups.2
    (List.mem_map.2 ⟨(y, ty), List.mem_append_left _ hy, rfl⟩)

/-- A procedure without type parameters has exactly one instance: itself, at `[]`. -/
theorem Procedure.instantiateTypes_of_typeArgs_nil {proc inst : Procedure}
    {tys : List Expression.Ty}
    (h : proc.header.typeArgs = []) :
    proc.instantiateTypes tys = some inst ↔ tys = [] ∧ inst = proc := by
  cases tys <;> simp [Procedure.instantiateTypes, h, eq_comm]

/-- Every instance of a procedure with one type parameter `a` is the procedure with some
    monotype `T` substituted for `a` throughout and no type parameters, at `[T]`. -/
theorem Procedure.instantiateTypes_of_typeArgs_singleton_inv {proc inst : Procedure}
    {a : Lambda.TyIdentifier} {tys : List Expression.Ty} (h : proc.header.typeArgs = [a])
    (hi : proc.instantiateTypes tys = some inst) :
    ∃ T, tys = [.forAll [] T] ∧
      inst = proc.mapTys (Lambda.LMonoTy.subst (Lambda.Subst.singleton a T)) [] := by
  have hS : ∀ T, Strata.Util.HMaps.ofScopes [[(a, T)]] = Lambda.Subst.singleton a T :=
    fun T => by
      simp [Strata.Util.HMaps.ofScopes, Strata.Util.HMap.ofList_singleton,
        Lambda.Subst.singleton]
  match tys, hi with
  | [], hi => simp [Procedure.instantiateTypes, h] at hi
  | [.forAll [] T], hi =>
    simp only [Procedure.instantiateTypes, h, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte,
      List.length_cons, List.length_nil, Nat.zero_add, ne_eq, not_true_eq_false,
      Bool.not_eq_eq_eq_not, Bool.not_true, List.mapM_cons, Lambda.LTy.toMonoType?, List.mapM_nil,
      Option.pure_def, Option.bind_eq_bind, Option.bind_some, Option.map_some, List.zip_cons_cons,
      List.zip_nil_right, hS, Option.ite_none_left_eq_some, Bool.not_eq_false,
      Option.some.injEq] at hi
    exact ⟨T, rfl, hi.2.symm⟩
  | [.forAll (_ :: _) _], hi =>
    simp [Procedure.instantiateTypes, h, Lambda.LTy.toMonoType?] at hi
  | _ :: _ :: _, hi => simp [Procedure.instantiateTypes, h] at hi

/-- A procedure with one type parameter `a`, whose body declares variables only at monotypes,
    has an instance at each monotype `T` and no other: the procedure with `T` substituted for
    `a` throughout and no type parameters. -/
theorem Procedure.instantiateTypes_of_typeArgs_singleton {proc inst : Procedure}
    {a : Lambda.TyIdentifier} {tys : List Expression.Ty} (h : proc.header.typeArgs = [a])
    (hm : proc.initTypesMono = true) :
    proc.instantiateTypes tys = some inst ↔
      ∃ T, tys = [.forAll [] T] ∧
        inst = proc.mapTys (Lambda.LMonoTy.subst (Lambda.Subst.singleton a T)) [] := by
  have hS : ∀ T, Strata.Util.HMaps.ofScopes [[(a, T)]] = Lambda.Subst.singleton a T :=
    fun T => by
      simp [Strata.Util.HMaps.ofScopes, Strata.Util.HMap.ofList_singleton,
        Lambda.Subst.singleton]
  refine ⟨Procedure.instantiateTypes_of_typeArgs_singleton_inv h, ?_⟩
  rintro ⟨T, rfl, rfl⟩
  simp [Procedure.instantiateTypes, h, hm, Lambda.LTy.toMonoType?, hS]

/-- Mapping the types of a procedure by the identity changes only its type parameters, to
    `typeArgs`. -/
theorem Procedure.mapTys_id (proc : Procedure) (typeArgs : List Lambda.TyIdentifier) :
    proc.mapTys id typeArgs =
      { proc with header := { proc.header with typeArgs := typeArgs } } := by
  have hcmd : mapCmdTys id = id := funext mapCmdTys_id
  obtain ⟨⟨name, ta, inputs, outputs, lemmas⟩, ⟨pre, post⟩, body⟩ := proc
  cases body with
  | structured ss =>
    simp only [Procedure.mapTys, id_eq, List.map_id_fun', Lambda.mapExprTys_id, mapStmtsTys_id,
      Imperative.Procedure.mk.injEq, and_true]
    exact ⟨rfl, rfl⟩
  | cfg c =>
    have hcfg : DetCFG.mapCmdsGuards c (mapCmdTys id) id = c := by
      obtain ⟨entry, blocks⟩ := c
      simp only [DetCFG.mapCmdsGuards, hcmd, List.map_id_fun, id_eq]
      congr 1
      exact List.map_id'' (fun ⟨l, b⟩ => by cases b with
        | mk cmds tr => cases tr <;> rfl) blocks
    simp only [Procedure.mapTys, id_eq, List.map_id_fun', Lambda.mapExprTys_id, hcfg,
      Imperative.Procedure.mk.injEq, and_true]
    exact ⟨rfl, rfl⟩

/-- A procedure whose body declares variables only at monotypes, instantiated at its own type
    parameters read as type variables, is the procedure without type parameters. -/
theorem Procedure.instantiateTypes_own_typeArgs (proc : Procedure)
    (hm : proc.initTypesMono = true) :
    proc.instantiateTypes (proc.header.typeArgs.map fun a => .forAll [] (.ftvar a)) =
      some { proc with header := { proc.header with typeArgs := [] } } := by
  have hmapM : ∀ as : List Lambda.TyIdentifier,
      (as.map fun a => Lambda.LTy.forAll [] (.ftvar a)).mapM Lambda.LTy.toMonoType? =
        some (as.map .ftvar) := by
    intro as
    induction as with
    | nil => rfl
    | cons a as ih => simp [List.mapM_cons, ih, Lambda.LTy.toMonoType?]
  by_cases h : proc.header.typeArgs = []
  · obtain ⟨⟨name, ta, inputs, outputs, lemmas⟩, spec, body⟩ := proc
    simp only at h
    subst h
    simp [Procedure.instantiateTypes]
  · have hsubst : Lambda.LMonoTy.subst
        (Strata.Util.HMaps.ofScopes [proc.header.typeArgs.zip (proc.header.typeArgs.map .ftvar)]) =
        id := funext (Lambda.LMonoTy.subst_ofScopes_self _)
    simp [Procedure.instantiateTypes, h, hm, hmapM, hsubst, Procedure.mapTys_id]

/-- A property of a procedure without type parameters holds of every instance of it. -/
theorem Procedure.forall_instance_of_typeArgs_nil {proc : Procedure} {Q : Procedure → Prop}
    (h : proc.header.typeArgs = []) (hq : Q proc) :
    ∀ tys inst, proc.instantiateTypes tys = some inst → Q inst := by
  intro tys inst hinst
  obtain ⟨-, rfl⟩ := (Procedure.instantiateTypes_of_typeArgs_nil h).1 hinst
  exact hq

/-- A property of a procedure with one type parameter `a` holds of every instance of it when it
    holds of `mk T` for every monotype `T`, where `mk T` is the procedure with `T` substituted for
    `a`. -/
theorem Procedure.forall_instance_of_typeArgs_singleton {proc : Procedure}
    {a : Lambda.TyIdentifier} {mk : Lambda.LMonoTy → Procedure} {Q : Procedure → Prop}
    (h : proc.header.typeArgs = [a])
    (hmk : ∀ T, proc.mapTys (Lambda.LMonoTy.subst (Lambda.Subst.singleton a T)) [] = mk T)
    (hq : ∀ T, Q (mk T)) :
    ∀ tys inst, proc.instantiateTypes tys = some inst → Q inst := by
  intro tys inst hinst
  obtain ⟨T, -, rfl⟩ := Procedure.instantiateTypes_of_typeArgs_singleton_inv h hinst
  exact hmk T ▸ hq T

/-- A call at the one type argument `T` to a procedure with one type parameter `a`, whose body
    declares variables only at monotypes, runs `mk T`, the procedure with `T` substituted for
    `a`. -/
theorem Procedure.typeInstantiatedCallee_of_typeArgs_singleton {π : String → Option Procedure}
    {n : String} {proc : Procedure} {a : Lambda.TyIdentifier} {mk : Lambda.LMonoTy → Procedure}
    (hπ : π n = some proc) (h : proc.header.typeArgs = [a]) (hm : proc.initTypesMono = true)
    (hmk : ∀ T, proc.mapTys (Lambda.LMonoTy.subst (Lambda.Subst.singleton a T)) [] = mk T)
    (T : Lambda.LMonoTy) :
    Imperative.Calls.typeInstantiatedCallee π n (some [.forAll [] T]) = some (mk T) := by
  simp only [Imperative.Calls.typeInstantiatedCallee, hπ, Option.bind_some, Option.getD_some]
  exact (Procedure.instantiateTypes_of_typeArgs_singleton h hm).2 ⟨T, rfl, (hmk T).symm⟩

/-- A call to a procedure without type parameters runs that procedure exactly when the call has
    no type arguments (`none` or `some []`). -/
theorem Procedure.typeInstantiatedCallee_of_typeArgs_nil {π : String → Option Procedure}
    {n : String} {proc inst : Procedure} {tyArgs : Option (List Expression.Ty)}
    (hπ : π n = some proc) (h : proc.header.typeArgs = []) :
    Imperative.Calls.typeInstantiatedCallee π n tyArgs = some inst ↔
      tyArgs.getD [] = [] ∧ inst = proc := by
  simp only [Imperative.Calls.typeInstantiatedCallee, hπ, Option.bind_some]
  exact Procedure.instantiateTypes_of_typeArgs_nil h

/-- A property of every procedure of a table without polymorphic procedures holds of every
    procedure a call can run in it. -/
theorem Procedure.forall_typeInstantiatedCallee_of_typeArgs_nil {π : String → Option Procedure}
    {Q : Procedure → Prop} (hmono : ∀ n p, π n = some p → p.header.typeArgs = [])
    (h : ∀ n p, π n = some p → Q p) :
    ∀ n tyArgs p, Imperative.Calls.typeInstantiatedCallee π n tyArgs = some p → Q p := by
  intro n tyArgs p hp
  obtain ⟨p₀, hp₀, hinst⟩ := Option.bind_eq_some_iff.1 hp
  obtain ⟨-, rfl⟩ := (Procedure.instantiateTypes_of_typeArgs_nil (hmono n p₀ hp₀)).1 hinst
  exact h n _ hp₀

end Core

end -- public section
