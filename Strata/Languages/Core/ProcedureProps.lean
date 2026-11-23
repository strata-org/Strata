/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Procedure
public import Strata.DL.Imperative.StmtCFGCallSemantics
import all Strata.Languages.Core.Procedure
import all Strata.Languages.Core.StatementSemanticsProps
import Strata.Languages.Core.StatementProps
import Strata.DL.Lambda.LTyUnifyProps
import Strata.Util.ListUtilsProps
import Strata.Util.OrderedSetProps
import Strata.DL.Imperative.MetaDataProps
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
- `DetCFG.CmdsRel.flatMap_eq` — control-flow graphs whose commands correspond one to one agree
  on every per-command list, such as the variables the commands modify or define.
- `DetCFG.mapCmdsGuards_eq_of_blocksRel` — control-flow graphs with related blocks agree after
  mapping their commands, guards and block metadata expressions by functions that identify
  related ones.
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

open Lambda

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

/-! ### Control-flow graphs with corresponding commands -/

/-- `c'` has the blocks of `c` with the same labels in the same order, and each command of `c'`
    is related by `R` to the command of `c` at the same position. -/
def DetCFG.CmdsRel (R : Command → Command → Prop) (c c' : DetCFG) : Prop :=
  List.Rel₂ (fun lb lb' => lb.1 = lb'.1 ∧ List.Rel₂ R lb.2.cmds lb'.2.cmds) c.blocks c'.blocks

/-- Two block transfers branch or finish alike: the same targets and metadata, and guards related
    by `G`. -/
def DetTransferRel (G : Expression.Expr → Expression.Expr → Prop) :
    Imperative.DetTransferCmd String Expression → Imperative.DetTransferCmd String Expression →
    Prop
  | .condGoto p lt lf md, .condGoto p' lt' lf' md' => G p p' ∧ lt = lt' ∧ lf = lf' ∧ md = md'
  | .finish md, .finish md' => md = md'
  | _, _ => False

/-- `c'` has the blocks of `c` with the same labels in the same order and the same entry; each
    command of `c'` is related by `R` to the command of `c` at the same position, each transfer
    by `G` on its guard, and each block's metadata by `G` on its expressions. -/
def DetCFG.BlocksRel (R : Command → Command → Prop)
    (G : Expression.Expr → Expression.Expr → Prop) (c c' : DetCFG) : Prop :=
  c'.entry = c.entry ∧
  List.Rel₂ (fun lb lb' => lb.1 = lb'.1 ∧ List.Rel₂ R lb.2.cmds lb'.2.cmds ∧
    DetTransferRel G lb.2.transfer lb'.2.transfer ∧ Imperative.MetaData.Rel G lb.2.md lb'.2.md)
    c.blocks c'.blocks

/-- Control-flow graphs whose blocks are related by `BlocksRel` agree after mapping their
    commands by `fc` and their guards and block metadata expressions by `fe`, when `fc`
    identifies related commands and `fe` identifies related expressions. -/
theorem DetCFG.mapCmdsGuards_eq_of_blocksRel {R : Command → Command → Prop}
    {G : Expression.Expr → Expression.Expr → Prop} {c c' : DetCFG}
    (fc : Command → Command) (fe : Expression.Expr → Expression.Expr)
    (hR : ∀ x y, R x y → fc y = fc x) (hG : ∀ p q, G p q → fe q = fe p)
    (h : DetCFG.BlocksRel R G c c') :
    DetCFG.mapCmdsGuards c' fc fe = DetCFG.mapCmdsGuards c fc fe := by
  obtain ⟨hentry, hblocks⟩ := h
  simp only [DetCFG.mapCmdsGuards, hentry]
  congr 1
  refine (List.Rel₂.map_eq ?_ hblocks).symm
  intro lb lb' hq
  rcases lb with ⟨l, ⟨cs, tr, bmd⟩⟩
  rcases lb' with ⟨l', ⟨cs', tr', bmd'⟩⟩
  obtain ⟨hl, hcs, htr, hmd⟩ := hq
  simp only at hl hcs htr hmd
  have hmdEq : bmd'.mapExprs fe = bmd.mapExprs fe :=
    Imperative.MetaData.mapExprs_eq_of_rel fe hG hmd
  have hcmds : cs.map fc = cs'.map fc :=
    List.Rel₂.map_eq (fun _ _ hxy => (hR _ _ hxy).symm) hcs
  subst hl
  cases tr with
  | condGoto p lt lf md =>
    cases tr' with
    | condGoto p' lt' lf' md' =>
      obtain ⟨hguard, rfl, rfl, rfl⟩ := htr
      simp only [hcmds, hG p p' hguard, hmdEq]
    | finish md' => exact htr.elim
  | finish md =>
    cases tr' with
    | condGoto p' lt' lf' md' => exact htr.elim
    | finish md' =>
      simp only [DetTransferRel] at htr
      subst htr
      simp only [hcmds, hmdEq]

/-- Mapping the commands and branch guards of a control-flow graph relates each command to its
    image. -/
theorem DetCFG.cmdsRel_mapCmdsGuards (c : DetCFG) (fc : Command → Command)
    (fe : Expression.Expr → Expression.Expr) :
    DetCFG.CmdsRel (fun x y => y = fc x) c (DetCFG.mapCmdsGuards c fc fe) := by
  unfold DetCFG.CmdsRel DetCFG.mapCmdsGuards
  refine List.Rel₂.map_right _ ?_ (List.Rel₂.refl (R := Eq) (fun _ => rfl) c.blocks)
  intro lb lb' heq
  subst heq
  exact ⟨rfl, List.Rel₂.map_right (R := Eq) (S := fun x y => y = fc x) fc
    (fun _ _ hab => congrArg fc hab.symm) (List.Rel₂.refl (R := Eq) (fun _ => rfl) _)⟩

/-- Mapping functions that fix every command and every guard over a control-flow graph changes
    nothing. -/
theorem DetCFG.mapCmdsGuards_id {fc : Command → Command}
    {fe : Expression.Expr → Expression.Expr} (hfc : ∀ c, fc c = c) (hfe : ∀ e, fe e = e)
    (c : DetCFG) : DetCFG.mapCmdsGuards c fc fe = c := by
  obtain ⟨entry, blocks⟩ := c
  simp only [DetCFG.mapCmdsGuards]
  congr 1
  refine List.map_id'' (fun x => ?_) blocks
  obtain ⟨l, ⟨cmds, tr, md⟩⟩ := x
  have hcmds : cmds.map fc = cmds := List.map_id'' hfc cmds
  have hmd : md.mapExprs fe = md := by
    rw [show fe = id from funext hfe]; exact Imperative.MetaData.mapExprs_id md
  cases tr <;> simp only [hcmds, hfe, hmd]

/-- A command relation that implies another lifts to control-flow graphs. -/
theorem DetCFG.CmdsRel.imp {R S : Command → Command → Prop} (hRS : ∀ x y, R x y → S x y)
    {c c' : DetCFG} (h : DetCFG.CmdsRel R c c') : DetCFG.CmdsRel S c c' :=
  List.Rel₂.imp (fun _ _ hlb => ⟨hlb.1, List.Rel₂.imp hRS hlb.2⟩) h

/-- Command correspondences between control-flow graphs compose. -/
theorem DetCFG.CmdsRel.comp {R S : Command → Command → Prop} {c₁ c₂ c₃ : DetCFG}
    (h₁₂ : DetCFG.CmdsRel R c₁ c₂) (h₂₃ : DetCFG.CmdsRel S c₂ c₃) :
    DetCFG.CmdsRel (fun x z => ∃ y, R x y ∧ S y z) c₁ c₃ :=
  List.Rel₂.imp (fun _ _ ⟨_, ⟨hl₁, hc₁⟩, ⟨hl₂, hc₂⟩⟩ => ⟨hl₁.trans hl₂, List.Rel₂.comp hc₁ hc₂⟩)
    (List.Rel₂.comp h₁₂ h₂₃)

/-- Control-flow graphs whose commands correspond agree on a per-command list that corresponding
    commands agree on. -/
theorem DetCFG.CmdsRel.flatMap_eq {α : Type} {R : Command → Command → Prop} {c c' : DetCFG}
    (f : Command → List α) (hf : ∀ x y, R x y → f y = f x) (h : DetCFG.CmdsRel R c c') :
    c'.blocks.flatMap (fun lb => lb.2.cmds.flatMap f)
      = c.blocks.flatMap (fun lb => lb.2.cmds.flatMap f) :=
  (List.Rel₂.flatMap_eq (fun _ _ hlb => (List.Rel₂.flatMap_eq
    (fun x y hxy => (hf x y hxy).symm) hlb.2)) h).symm

/-- Every command of the second of two control-flow graphs with corresponding commands
    corresponds to a command of the first. -/
theorem DetCFG.CmdsRel.exists_of_mem {R : Command → Command → Prop} {c c' : DetCFG}
    (h : DetCFG.CmdsRel R c c') {lb' : String × Imperative.DetBlock String Command Expression}
    (hlb : lb' ∈ c'.blocks) {y : Command} (hy : y ∈ lb'.2.cmds) : ∃ x, R x y := by
  obtain ⟨lb, -, -, hcmds⟩ := List.Rel₂.exists_of_mem_right h hlb
  obtain ⟨x, -, hxy⟩ := List.Rel₂.exists_of_mem_right hcmds hy
  exact ⟨x, hxy⟩

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
        | mk cmds tr md => cases tr <;> rw [Imperative.MetaData.mapExprs_id]) blocks
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

/-- Renaming no type parameter leaves a procedure unchanged. -/
theorem Procedure.renameTypeArgs_nil (proc : Procedure) : proc.renameTypeArgs [] = proc := by
  have hta : renameTyArgList [] proc.header.typeArgs = proc.header.typeArgs :=
    List.map_id'' (fun a => by simp only [List.lookup_nil, Option.getD_none]) _
  unfold Procedure.renameTypeArgs
  rw [LMonoTy.subst_ofRenaming_nil, hta, Procedure.mapTys_id]

/-- Renaming type parameters renames the type variables of a procedure's parameter types. -/
theorem Procedure.renameTypeArgs_values (proc : Procedure) (ren : List (String × String)) :
    (proc.renameTypeArgs ren).header.inputs.values =
        proc.header.inputs.values.map (LMonoTy.subst (Subst.ofRenaming ren)) ∧
      (proc.renameTypeArgs ren).header.outputs.values =
        proc.header.outputs.values.map (LMonoTy.subst (Subst.ofRenaming ren)) := by
  have hmap : ∀ sig : @LMonoTySignature Unit, ListMap.values
      (sig.map fun p => (p.1, LMonoTy.subst (Subst.ofRenaming ren) p.2)) =
      sig.values.map (LMonoTy.subst (Subst.ofRenaming ren)) := by
    intro sig
    induction sig with
    | nil => rfl
    | cons p rest ih =>
      simp only [List.map_cons, ListMap.values, ih]
  exact ⟨hmap _, hmap _⟩

end Core

end -- public section
