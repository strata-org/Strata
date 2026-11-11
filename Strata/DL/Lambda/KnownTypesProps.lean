/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Lambda.LExprTypeEnv
public import Strata.DL.Lambda.TypeFactory
public import Strata.DL.Lambda.LExprAnnotRel
import all Strata.DL.Lambda.LExprTypeEnvProps
import Strata.DL.Lambda.TypeFactoryProps
import Strata.DL.Lambda.DatatypeFactoryWFProps

/-! # Registered type constructors

Facts about `KnownTypesExtends`, `TableAgree`, `LContext.KnownTypesAll`,
`Subst.RangeKnown`, `Constraints.Known`, `FactorySigsKnown` and
`LContext.DatatypesKnown`. They live in a separate file so that
`LExprTypeEnvProps` does not grow.

Key theorems: `knownInstance_mono`, `knownInstance_subst` and
`Constraints.unify_RangeKnown` (registered types survive table growth,
substitution and unification); `knownInstance_congr` (tables that record the
same arities, `TableAgree`, have the same registered instances);
`KnownTypesAll_addKnownTypeWithError` and `KnownTypesAll_addMutualBlock`
(registering types keeps a property of every registered name);
`LFunc.type_eq_mkArrow'` (the type scheme of a function with a registered output
type is the arrow from its inputs to its output); `FactorySigsKnown.tryAddAll`
(adding functions keeps signatures registered);
`tablesKnown_foldl_addFactoryFunction` (adding functions with registered
signature types keeps every signature and datatype registered);
`LFunc.body_knownInstance` (the body of such a function's type scheme is a
registered instance); `genBlockFactory_sigsKnown` (every signature a block
generates uses only registered constructors); and `knownTypes_foldlM_add_mem`
and `datatypesKnown_addMutualBlock` (registering a datatype block records each
datatype at its arity). -/

namespace Lambda

open Strata.Util (HMap HMaps)

public section

/-! ### Growth of the registered-type table (`KnownTypesExtends`) -/

/-- Every table extends itself: each name keeps its arity. -/
theorem KnownTypesExtends.refl (ks : KnownTypes) : KnownTypesExtends ks ks :=
  fun _ _ h => h

/-- If `ks'` extends `ks` and `ks''` extends `ks'`, then `ks''` extends `ks`:
    each name `ks` registers keeps its arity in `ks''`. -/
private theorem KnownTypesExtends.trans {ks ks' ks'' : KnownTypes}
    (h1 : KnownTypesExtends ks ks') (h2 : KnownTypesExtends ks' ks'') :
    KnownTypesExtends ks ks'' :=
  fun n a h => h2 n a (h1 n a h)

/-- Registering the datatype names of a mutual block extends the table. -/
private theorem KnownTypesExtends.of_add_foldlM {IDMeta : Type}
    (ks ks' : KnownTypes) (block : List (LDatatype IDMeta))
    (h : block.foldlM (fun ks (d : LDatatype IDMeta) => ks.add d.toKnownType)
      ks = .ok ks') :
    KnownTypesExtends ks ks' := by
  induction block generalizing ks with
  | nil =>
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h
    exact KnownTypesExtends.refl ks
  | cons d rest ih =>
    simp only [List.foldlM_cons, bind, Except.bind] at h
    elim_err h with ks1 hks1
    refine KnownTypesExtends.trans ?_ (ih ks1 h)
    intro n a hn
    exact Identifiers.addWithError_getElem?_mono ks ks1
      ⟨d.toKnownType.name, d.toKnownType.metadata⟩ _ hks1 n a hn

/-- Registering a mutual block extends the table. -/
theorem KnownTypesExtends.of_addMutualBlock {T : LExprParams}
    [Inhabited T.Metadata] [Inhabited T.IDMeta] [Std.ToFormat T.IDMeta]
    [DecidableEq T.IDMeta]
    (C C' : LContext T) (block : MutualDatatype T.IDMeta)
    (h : C.addMutualBlock block = .ok C') :
    KnownTypesExtends C.knownTypes C'.knownTypes := by
  obtain ⟨-, _, _, _, ks, -, -, -, hks, rfl⟩ :=
    LContext.addMutualBlock_ok_eq C C' block h
  exact KnownTypesExtends.of_add_foldlM C.knownTypes ks block hks

/-- If every name in `C`'s known-types table satisfies `p` and `k`'s name does
    too, every name in the table after registering `k` satisfies `p`. -/
theorem KnownTypesAll_addKnownTypeWithError {T : LExprParams}
    {p : String → Prop} (C C' : LContext T) (k : KnownType)
    (msg : Strata.Message) (hname : p k.name)
    (h : C.addKnownTypeWithError k msg = .ok C')
    (hall : LContext.KnownTypesAll p C) : LContext.KnownTypesAll p C' := by
  simp only [LContext.addKnownTypeWithError, bind, Except.bind] at h
  split at h
  · simp only [reduceCtorEq] at h
  · rename_i v hv
    simp only [Except.ok.injEq] at h
    subst h
    intro n hn
    rcases Identifiers.addWithError_mem_inv hv n hn with rfl | hmem
    · exact hname
    · exact hall n hmem

/-- Adding a datatype block whose names satisfy `p` to a table whose names
    satisfy `p` gives a table whose names satisfy `p`. -/
private theorem knownTypes_foldlM_add_all {IDMeta : Type} {p : String → Prop}
    (ks ks' : KnownTypes) (block : List (LDatatype IDMeta))
    (hnames : ∀ d ∈ block, p d.name)
    (h : block.foldlM (fun ks (d : LDatatype IDMeta) => ks.add d.toKnownType)
      ks = .ok ks')
    (hks : ∀ n : String, n ∈ ks → p n) :
    ∀ n : String, n ∈ ks' → p n := by
  induction block generalizing ks with
  | nil =>
    simp only [List.foldlM_nil, pure, Except.pure, Except.ok.injEq] at h
    subst h; exact hks
  | cons d rest ih =>
    simp only [List.foldlM_cons, bind, Except.bind] at h
    elim_err h with ks1 hks1
    refine ih ks1 (fun d' hd' => hnames d' (List.mem_cons_of_mem d hd')) h ?_
    intro n hn
    rcases Identifiers.addWithError_mem_inv hks1 n hn with rfl | hmem
    · exact hnames d (List.mem_cons_self ..)
    · exact hks n hmem

/-- If every name in `C`'s known-types table and every datatype name of `block`
    satisfies `p`, every name in the table after registering `block` satisfies
    `p`. -/
theorem KnownTypesAll_addMutualBlock {T : LExprParams} [Inhabited T.Metadata]
    [Inhabited T.IDMeta] [Std.ToFormat T.IDMeta] [DecidableEq T.IDMeta]
    {p : String → Prop}
    (C C' : LContext T) (block : MutualDatatype T.IDMeta)
    (hnames : ∀ d ∈ block, p d.name)
    (h : C.addMutualBlock block = .ok C')
    (hall : LContext.KnownTypesAll p C) : LContext.KnownTypesAll p C' := by
  obtain ⟨-, _, _, _, ks, -, -, -, hks, rfl⟩ :=
    LContext.addMutualBlock_ok_eq C C' block h
  exact knownTypes_foldlM_add_all C.knownTypes ks block hnames hks hall

/-- A registered instance of `ks` is a registered instance of any table
    extending `ks`. -/
theorem knownInstance_mono (mty : LMonoTy) (ks ks' : KnownTypes)
    (hext : KnownTypesExtends ks ks')
    (h : LMonoTy.knownInstance mty ks = true) :
    LMonoTy.knownInstance mty ks' = true := by
  rw [LMonoTy.knownInstance_iff_wellKinded] at h ⊢
  exact fun ref n hmem => hext ref n (h ref n hmem)

/-- A table extending another registers every name the other does. -/
theorem KnownTypesExtends.mem {ks ks' : KnownTypes} (h : KnownTypesExtends ks ks')
    (n : String) (hn : n ∈ ks) : n ∈ ks' := by
  obtain ⟨a, ha⟩ := Option.isSome_iff_exists.mp (Std.HashMap.mem_iff_isSome_getElem?.mp hn)
  have h_some : ks'[n]?.isSome = true := by rw [h n a ha]; rfl
  exact Std.HashMap.mem_iff_isSome_getElem?.mpr h_some

/-- Registering one type constructor extends the table. -/
theorem KnownTypesExtends.of_addKnownTypeWithError {T : LExprParams}
    (C C' : LContext T) (k : KnownType) (msg : Strata.Message)
    (h : C.addKnownTypeWithError k msg = .ok C') :
    KnownTypesExtends C.knownTypes C'.knownTypes := by
  intro ref n hn
  simp only [LContext.addKnownTypeWithError, bind, Except.bind] at h
  split at h
  · simp only [reduceCtorEq] at h
  · rename_i v hv
    simp only [Except.ok.injEq] at h
    subst h
    exact Identifiers.addWithError_getElem?_mono C.knownTypes v k msg hv ref n hn

/-- A table extends any equal table. -/
theorem KnownTypesExtends.of_knownTypes_eq {T : LExprParams} (C C' : LContext T)
    (h : C'.knownTypes = C.knownTypes) : KnownTypesExtends C.knownTypes C'.knownTypes :=
  fun n a hn => by rw [h]; exact hn

/-! ### Substitution and unification keep constructor references registered -/

/-- A one-binding substitution to a registered instance has a registered
    range. -/
private theorem Subst.RangeKnown_singleton (ks : KnownTypes)
    (tv : TyIdentifier) (ty : LMonoTy)
    (h : LMonoTy.knownInstance ty ks = true) :
    Subst.RangeKnown (Subst.singleton tv ty) ks := by
  intro mty hmty
  have hmty' : mty ∈ (HMap.single tv ty).values := by
    simpa [Subst.singleton, HMaps.values] using hmty
  rw [(HMap.mem_values_single_iff tv ty mty).mp hmty']
  exact h

mutual
/-- Substitution with a registered range preserves registered instances. -/
theorem knownInstance_subst (ks : KnownTypes) (S : Subst) (mty : LMonoTy)
    (hS : Subst.RangeKnown S ks)
    (h : LMonoTy.knownInstance mty ks = true) :
    LMonoTy.knownInstance (LMonoTy.subst S mty) ks = true := by
  match mty with
  | .ftvar x =>
    match hfind : HMaps.find? S x with
    | some sty =>
      have hval : LMonoTy.subst S (.ftvar x) = sty := by
        rw [LMonoTy.subst_unfold]; simp only [hfind]
      rw [hval]
      exact hS sty (HMaps.find?_mem_values S hfind)
    | none =>
      have hval : LMonoTy.subst S (.ftvar x) = .ftvar x := by
        rw [LMonoTy.subst_unfold]; simp only [hfind]
      rw [hval]; simp only [LMonoTy.knownInstance]
  | .bitvec _ => rw [LMonoTy.subst_bitvec]; simp only [LMonoTy.knownInstance]
  | .tcons name args =>
    simp only [LMonoTy.knownInstance, Bool.and_eq_true] at h
    rw [LMonoTy.subst_tcons]
    simp only [LMonoTy.knownInstance, Bool.and_eq_true]
    refine ⟨?_, knownInstances_subst ks S args hS h.2⟩
    rw [LMonoTys.subst_eq_map, List.length_map]
    exact h.1

/-- Substitution with a registered range preserves lists of registered
    instances. -/
private theorem knownInstances_subst (ks : KnownTypes) (S : Subst)
    (mtys : LMonoTys)
    (hS : Subst.RangeKnown S ks)
    (h : LMonoTys.knownInstances mtys ks = true) :
    LMonoTys.knownInstances (LMonoTys.subst S mtys) ks = true := by
  match mtys with
  | [] => rw [LMonoTys.subst_nil]; simp only [LMonoTys.knownInstances]
  | t :: rest =>
    simp only [LMonoTys.knownInstances] at h
    elim_err h with ht
    rw [LMonoTys.subst_eq_map, List.map_cons]
    simp only [LMonoTys.knownInstances]
    rw [ite_eq_left (knownInstance_subst ks S t hS ht), ← LMonoTys.subst_eq_map]
    exact knownInstances_subst ks S rest hS h
end

/-- Composing one registered binding onto `S` keeps the range registered. -/
private theorem Subst.RangeKnown_apply (ks : KnownTypes) (new : SubstOne)
    (S : Subst)
    (hnew : Subst.RangeKnown [new] ks) (hS : Subst.RangeKnown S ks) :
    Subst.RangeKnown (Subst.apply new S) ks := by
  intro mty hmty
  rw [Subst.apply, HMaps.mem_values_mapValues] at hmty
  obtain ⟨v, hv, rfl⟩ := hmty
  exact knownInstance_subst ks [new] v hnew (hS v hv)

/-- Adding a registered binding keeps the range registered. -/
private theorem Subst.RangeKnown_insert (ks : KnownTypes) (S : Subst)
    (id : TyIdentifier) (ty : LMonoTy)
    (hty : LMonoTy.knownInstance ty ks = true) (hS : Subst.RangeKnown S ks) :
    Subst.RangeKnown (HMaps.insert S id ty) ks := by
  intro mty hmty
  rcases List.mem_cons.mp (HMaps.insert_values_subset S id ty mty hmty) with
    rfl | hold
  · exact hty
  · exact hS mty hold

/-- `unifyOne` and `unifyCore` keep the range registered on constraints with
    registered sides. -/
private theorem unify_RangeKnown_both (ks : KnownTypes) :
    (∀ (c : Constraint) (S : SubstInfo) (relS : ValidSubstRelation [c] S),
      Constraint.unifyOne c S = .ok relS → Subst.RangeKnown S.subst ks →
      Constraint.Known c ks → Subst.RangeKnown relS.newS.subst ks) ∧
    (∀ (cs : Constraints) (S : SubstInfo) (relS : ValidSubstRelation cs S),
      Constraints.unifyCore cs S = .ok relS → Subst.RangeKnown S.subst ks →
      Constraints.Known cs ks → Subst.RangeKnown relS.newS.subst ks) := by
  have hempty : Subst.RangeKnown [] ks := by
    intro mty hmty
    simp [HMaps.values] at hmty
  have hlty : ∀ (S : Subst) (id : TyIdentifier) (orig_lty : LMonoTy),
      Subst.RangeKnown S ks →
      Constraint.Known (.ftvar id, orig_lty) ks ∨
        Constraint.Known (orig_lty, .ftvar id) ks →
      LMonoTy.knownInstance (LMonoTy.subst S orig_lty) ks = true := by
    intro S id orig_lty hS hc
    have horig : LMonoTy.knownInstance orig_lty ks = true :=
      hc.elim (·.2) (·.1)
    exact knownInstance_subst ks S orig_lty hS horig
  refine Constraint.unify_preserves (Subst.RangeKnown · ks)
    (Constraint.Known · ks) hempty ?_ ?_ ?_
  · intro S id orig_lty hS hc
    have h_lty := hlty S id orig_lty hS hc
    exact Subst.RangeKnown_insert ks _ id _ h_lty
      (Subst.RangeKnown_apply ks _ S
        (Subst.RangeKnown_singleton ks id _ h_lty) hS)
  · intro S id orig_lty sty hS hc h_some
    exact ⟨hS sty (HMaps.find?_mem_values S h_some), hlty S id orig_lty hS hc⟩
  · intro name1 name2 args1 args2 hc p hp
    have h1 := hc.1
    have h2 := hc.2
    simp only [LMonoTy.knownInstance, Bool.and_eq_true] at h1 h2
    have hpair := List.of_mem_zip (l₁ := args1) (l₂ := args2) hp
    exact ⟨LMonoTys.knownInstances_iff_forall.mp h1.2 p.1 hpair.1,
      LMonoTys.knownInstances_iff_forall.mp h2.2 p.2 hpair.2⟩

/-- Unification keeps the range registered when every constraint side is
    registered. -/
theorem Constraints.unify_RangeKnown (ks : KnownTypes) (cs : Constraints)
    (S S' : SubstInfo)
    (h : Constraints.unify cs S = .ok S')
    (hS : Subst.RangeKnown S.subst ks)
    (hcs : Constraints.Known cs ks) :
    Subst.RangeKnown S'.subst ks := by
  simp only [Constraints.unify, bind, Except.bind] at h
  elim_err h with relS h_core
  simp only [Except.ok.injEq] at h; subst h
  exact (unify_RangeKnown_both ks).2 cs S relS h_core hS hcs

/-! ### Tables recording the same arities (`TableAgree`) -/

/-- `TableAgree` is symmetric. -/
private theorem TableAgree.symm {ks1 ks2 : KnownTypes} (h : TableAgree ks1 ks2) :
    TableAgree ks2 ks1 :=
  TableAgree.of_getElem? fun n => (h.getElem?_eq n).symm

/-- Agreeing tables extend each other. -/
private theorem TableAgree.extends {ks1 ks2 : KnownTypes} (h : TableAgree ks1 ks2) :
    KnownTypesExtends ks1 ks2 := by
  intro n a ha
  rw [← h.getElem?_eq n]
  exact ha

/-- Adding the same registration to agreeing tables keeps them agreeing. -/
theorem TableAgree.insert {ks1 ks2 : KnownTypes} (h : TableAgree ks1 ks2)
    (n : String) (a : Nat) : TableAgree (ks1.insert n a) (ks2.insert n a) := by
  refine TableAgree.of_getElem? ?_
  intro m
  rw [Std.HashMap.getElem?_insert, Std.HashMap.getElem?_insert, h.getElem?_eq m]

/-- Agreeing tables have the same registered instances. -/
theorem knownInstance_congr (mty : LMonoTy) {ks1 ks2 : KnownTypes} (h : TableAgree ks1 ks2) :
    LMonoTy.knownInstance mty ks1 = LMonoTy.knownInstance mty ks2 := by
  cases h1 : LMonoTy.knownInstance mty ks1 with
  | true => exact (knownInstance_mono mty ks1 ks2 h.extends h1).symm
  | false =>
    cases h2 : LMonoTy.knownInstance mty ks2 with
    | true =>
      rw [knownInstance_mono mty ks2 ks1 h.symm.extends h2] at h1
      exact absurd h1 (by simp)
    | false => rfl

/-- Registering one type constructor agrees with inserting it into the table. -/
theorem addKnownTypeWithError_tableAgree {T : LExprParams}
    (C C' : LContext T) (k : KnownType) (msg : Strata.Message)
    (h : C.addKnownTypeWithError k msg = .ok C') :
    TableAgree C'.knownTypes (C.knownTypes.insert k.name k.arity) := by
  refine TableAgree.of_getElem? ?_
  intro n
  simp only [LContext.addKnownTypeWithError, bind, Except.bind] at h
  split at h
  · simp only [reduceCtorEq] at h
  · rename_i v hv
    simp only [Except.ok.injEq] at h
    subst h
    simp only [KnownTypes.addWithError, Identifiers.addWithError,
      Std.HashMap.containsThenInsertIfNew_fst, Std.HashMap.containsThenInsertIfNew_snd] at hv
    split at hv
    · simp only [reduceCtorEq] at hv
    · rename_i hc
      simp only [Except.ok.injEq] at hv
      subst hv
      have hnm : ¬ (k.name ∈ C.knownTypes) := fun hm =>
        hc (Std.HashMap.contains_iff_mem.mpr hm)
      show (C.knownTypes.insertIfNew k.name k.arity)[n]?
        = (C.knownTypes.insert k.name k.arity)[n]?
      rw [Std.HashMap.getElem?_insertIfNew, Std.HashMap.getElem?_insert]
      simp [hnm]

/-! ### Substitution ranges under scope operations -/

/-- Dropping a binding keeps the range registered. -/
theorem Subst.RangeKnown_remove (ks : KnownTypes) (S : Subst) (id : TyIdentifier)
    (hS : Subst.RangeKnown S ks) :
    Subst.RangeKnown (HMaps.remove S id) ks :=
  fun mty hmty => hS mty (HMaps.values_remove_subset S id mty hmty)

/-- The empty substitution has a registered range. -/
theorem Subst.RangeKnown_empty (ks : KnownTypes) : Subst.RangeKnown Subst.empty ks := by
  intro mty hmty
  have h_not_mem : mty ∉ HMaps.values (Subst.empty : Subst) := by
    simp [HMaps.values]
  exact absurd hmty h_not_mem

/-- Dropping the newest scope keeps the range registered. -/
private theorem Subst.RangeKnown_pop (ks : KnownTypes) (S : Subst)
    (hS : Subst.RangeKnown S ks) :
    Subst.RangeKnown (HMaps.pop S) ks := by
  intro mty hmty
  refine hS mty ?_
  cases S with
  | nil =>
    have h_not_mem : mty ∉ HMaps.values (HMaps.pop ([] : Subst)) := by
      simp [HMaps.pop, HMaps.values]
    exact absurd hmty h_not_mem
  | cons m rest =>
    simp only [HMaps.pop] at hmty
    simp only [HMaps.values, List.mem_append]
    exact Or.inr hmty

/-- Pushing a scope of registered types keeps the range registered. -/
private theorem Subst.RangeKnown_push (ks : KnownTypes) (S : Subst) (m : SubstOne)
    (hm : ∀ mty ∈ m.values, LMonoTy.knownInstance mty ks = true)
    (hS : Subst.RangeKnown S ks) :
    Subst.RangeKnown (HMaps.push S m) ks := by
  intro mty hmty
  simp only [HMaps.push, HMaps.values, List.mem_append] at hmty
  rcases hmty with hmty | hmty
  · exact hm mty hmty
  · exact hS mty hmty

/-- Pushing a scope that binds nothing keeps the range registered. -/
theorem Subst.RangeKnown_push_empty (ks : KnownTypes) (S : Subst)
    (hS : Subst.RangeKnown S ks) :
    Subst.RangeKnown (HMaps.push S (HMap.empty : SubstOne)) ks :=
  have h_empty : ∀ mty ∈ (HMap.empty : SubstOne).values,
      LMonoTy.knownInstance mty ks = true := by
    intro mty hmty
    rw [HMap.values_empty] at hmty
    exact absurd hmty List.not_mem_nil
  Subst.RangeKnown_push ks S HMap.empty h_empty hS

/-- A registered range stays registered in any extending table. -/
theorem Subst.RangeKnown_mono (ks ks' : KnownTypes) (S : Subst)
    (hext : KnownTypesExtends ks ks')
    (hS : Subst.RangeKnown S ks) :
    Subst.RangeKnown S ks' :=
  fun mty hmty => knownInstance_mono mty ks ks' hext (hS mty hmty)

section RangeKnownEnv

variable {IDMeta : Type} [DecidableEq IDMeta] [Hashable IDMeta]

/-- Opening a substitution scope keeps the range registered. -/
theorem TEnv.RangeKnown_pushEmptySubstScope (Env : TEnv IDMeta) (ks : KnownTypes)
    (hS : Subst.RangeKnown Env.stateSubstInfo.subst ks) :
    Subst.RangeKnown Env.pushEmptySubstScope.stateSubstInfo.subst ks := by
  simp only [TEnv.pushEmptySubstScope]
  exact Subst.RangeKnown_push_empty ks _ hS

/-- Closing the newest substitution scope keeps the range registered. -/
theorem TEnv.RangeKnown_popSubstScope (Env : TEnv IDMeta) (ks : KnownTypes)
    (hS : Subst.RangeKnown Env.stateSubstInfo.subst ks) :
    Subst.RangeKnown Env.popSubstScope.stateSubstInfo.subst ks := by
  simp only [TEnv.popSubstScope]
  exact Subst.RangeKnown_pop ks _ hS

/-- Opening a variable scope keeps the range registered. -/
theorem TEnv.RangeKnown_pushEmptyContext (Env : TEnv IDMeta) (ks : KnownTypes)
    (hS : Subst.RangeKnown Env.stateSubstInfo.subst ks) :
    Subst.RangeKnown Env.pushEmptyContext.stateSubstInfo.subst ks := by
  rw [TEnv.pushEmptyContext_stateSubstInfo]
  exact hS

/-- Closing the newest variable scope keeps the range registered. -/
theorem TEnv.RangeKnown_popContext (Env : TEnv IDMeta) (ks : KnownTypes)
    (hS : Subst.RangeKnown Env.stateSubstInfo.subst ks) :
    Subst.RangeKnown Env.popContext.stateSubstInfo.subst ks := by
  rw [TEnv.popContext_stateSubstInfo]
  exact hS

end RangeKnownEnv

/-! ### Registered-type tables for factory signatures and datatypes -/

/-- A registered instance named `arrow` has two arguments when `ks` registers
    `arrow` at arity 2. -/
private theorem knownInstance_arrow_length {ks : KnownTypes}
    (h_arrow : ks["arrow"]? = some 2) {args : LMonoTys}
    (h : LMonoTy.knownInstance (.tcons "arrow" args) ks = true) :
    args.length = 2 := by
  simp only [LMonoTy.knownInstance, Bool.and_eq_true, KnownTypes.contains,
    Identifiers.contains, KnownType.arity, h_arrow, beq_iff_eq] at h
  exact h.1

/-- `destructArrow` splits a registered instance into components that
    `mkArrow` rebuilds it from, when `ks` registers `arrow` at arity 2. -/
private theorem LMonoTy.destructArrow_mkArrow {ks : KnownTypes}
    (h_arrow : ks["arrow"]? = some 2) :
    ∀ out : LMonoTy, LMonoTy.knownInstance out ks = true →
      ∃ d ds, LMonoTy.destructArrow out = d :: ds ∧
        LMonoTy.mkArrow d ds = out := by
  intro out
  induction out with
  | ftvar v => intro _; exact ⟨.ftvar v, [], rfl, rfl⟩
  | bitvec n => intro _; exact ⟨.bitvec n, [], rfl, rfl⟩
  | tcons name args ih =>
    intro hk
    by_cases hn : name = "arrow"
    · subst hn
      have hlen := knownInstance_arrow_length h_arrow hk
      match args, hlen, ih, hk with
      | [a, b], _, ih, hk =>
        simp only [LMonoTy.knownInstance, LMonoTys.knownInstances,
          Bool.and_eq_true] at hk
        have hb : LMonoTy.knownInstance b ks = true := by
          by_cases ha : LMonoTy.knownInstance a ks = true
          · simpa [ha] using hk.2
          · simp [ha] at hk
        obtain ⟨d, ds, hd, hm⟩ := ih b (by simp) hb
        refine ⟨a, d :: ds, ?_, ?_⟩
        · simp [LMonoTy.destructArrow, LMonoTys.destructArrow, hd]
        · simp only [LMonoTy.mkArrow, hm]
          rfl
    · rcases destructArrow_eq_self_or_arrow (.tcons name args) with
        hd | ⟨t1, trest, heq⟩
      · exact ⟨.tcons name args, [], hd, rfl⟩
      · simp only [LMonoTy.tcons.injEq] at heq
        exact absurd heq.1 hn

/-- When `ks` registers `arrow` at arity 2, `mkArrow` over `i :: is` followed
    by the arrow components of a registered instance `out` is
    `mkArrow' out (i :: is)`. -/
private theorem LMonoTy.mkArrow_append_destructArrow {ks : KnownTypes}
    (h_arrow : ks["arrow"]? = some 2)
    {out : LMonoTy} (hout : LMonoTy.knownInstance out ks = true) :
    ∀ (i : LMonoTy) (is : LMonoTys),
      LMonoTy.mkArrow i (is ++ LMonoTy.destructArrow out) =
        LMonoTy.mkArrow' out (i :: is) := by
  intro i is
  induction is generalizing i with
  | nil =>
    obtain ⟨d, ds, hd, hm⟩ := LMonoTy.destructArrow_mkArrow h_arrow out hout
    rw [List.nil_append, hd, LMonoTy.mkArrow'_cons, LMonoTy.mkArrow'_nil]
    simp only [LMonoTy.mkArrow, hm]
  | cons j js ih =>
    rw [List.cons_append, LMonoTy.mkArrow'_cons]
    simp only [LMonoTy.mkArrow, ih j]

/-- When `ks` registers `arrow` with two arguments and `f`'s output type uses
    only constructors `ks` registers at their arities, the type scheme
    `LFunc.type` computes for `f` quantifies `f`'s type parameters over the
    arrow from its input types to its output type. -/
theorem LFunc.type_eq_mkArrow' {T : LExprParams} [DecidableEq T.IDMeta]
    {ks : KnownTypes} (h_arrow : ks["arrow"]? = some 2) {f : LFunc T}
    {ty : LTy} (h : f.type = .ok ty)
    (hout : LMonoTy.knownInstance f.output ks = true) :
    ty = .forAll f.typeArgs
      (LMonoTy.mkArrow' f.output (f.inputs.map Prod.snd)) := by
  unfold LFunc.type LFuncDefined.type at h
  simp only [Bind.bind, Except.bind] at h
  elim_errs h
  rw [← ListMap.values_eq_map_snd]
  generalize h_vals : f.inputs.values = vals at h
  cases vals with
  | nil =>
    simp only [Except.ok.injEq] at h
    subst h
    rfl
  | cons i is =>
    simp only [Except.ok.injEq] at h
    subst h
    rw [LMonoTy.mkArrow_append_destructArrow h_arrow hout]

/-- Factory signatures registered in `ks` stay registered in any table
    extending `ks`. -/
theorem FactorySigsKnown.mono {T : LExprParams} {ks ks' : KnownTypes}
    {F : Factory T} (hext : KnownTypesExtends ks ks')
    (h : FactorySigsKnown ks F) : FactorySigsKnown ks' F :=
  ⟨hext _ _ h.1,
    fun f hf ty hty => knownInstance_mono ty ks ks' hext (h.2 f hf ty hty)⟩

/-- Adding a function whose input and output types are registered instances
    preserves `FactorySigsKnown`. -/
theorem FactorySigsKnown.addFactoryFunction {T : LExprParams} {ks : KnownTypes}
    {C : LContext T}
    {fn : LFunc T} (hC : FactorySigsKnown ks C.functions)
    (hfn : ∀ ty ∈ fn.output :: fn.inputs.values,
      LMonoTy.knownInstance ty ks = true) :
    FactorySigsKnown ks (C.addFactoryFunction fn).functions := by
  refine ⟨hC.1, fun lf hlf => ?_⟩
  rcases mem_addFactoryFunction C fn lf hlf with hold | rfl
  · exact hC.2 lf hold
  · exact hfn

/-- Appending functions whose input and output types are registered instances
    preserves `FactorySigsKnown`. -/
theorem FactorySigsKnown.tryAddAll {T : LExprParams} [Inhabited T.Metadata]
    [Std.ToFormat T.IDMeta] {ks : KnownTypes} {F F' : Factory T}
    {fs : Array (LFunc T)}
    (h : F.tryAddAll fs = .ok F') (hF : FactorySigsKnown ks F)
    (hfs : ∀ f ∈ fs, ∀ ty ∈ f.output :: f.inputs.values,
      LMonoTy.knownInstance ty ks = true) :
    FactorySigsKnown ks F' := by
  refine ⟨hF.1, fun g hg => ?_⟩
  simp only [Factory.tryAddAll] at h
  rw [← Array.foldlM_toList] at h
  rcases Factory.mem_foldlM_tryPush fs.toList F F' h g hg with hold | hnew
  · exact hF.2 g hold
  · exact hfs g (Array.mem_toList_iff.mp hnew)

/-- Registering a block of datatypes one after another records each at its
    number of type parameters. -/
theorem knownTypes_foldlM_add_mem {IDMeta : Type} (ks ks' : KnownTypes)
    (block : List (LDatatype IDMeta))
    (h : block.foldlM (fun ks (d : LDatatype IDMeta) => ks.add d.toKnownType)
      ks = .ok ks') :
    ∀ d ∈ block, ks'[d.name]? = some d.typeArgs.length := by
  induction block generalizing ks with
  | nil => intro d hd; exact absurd hd List.not_mem_nil
  | cons d0 rest ih =>
    simp only [List.foldlM_cons, bind, Except.bind] at h
    elim_err h with ks1 hks1
    intro d hd
    rcases List.mem_cons.mp hd with rfl | hrest
    · refine KnownTypesExtends.of_add_foldlM ks1 ks' rest h _ _ ?_
      have hnm : d.name ∉ ks := by
        intro hmem
        have hc : Std.HashMap.contains ks d.toKnownType.name = true :=
          Std.HashMap.mem_iff_contains.mp hmem
        simp only [Identifiers.add, Identifiers.addWithError,
          Std.HashMap.containsThenInsertIfNew_fst, hc, ↓reduceIte,
          reduceCtorEq] at hks1
      rw [Identifiers.addWithError_ok_eq hks1]
      show (ks.insertIfNew d.name d.typeArgs.length)[d.name]? =
        some d.typeArgs.length
      rw [Std.HashMap.getElem?_insertIfNew]
      simp [hnm]
    · exact ih ks1 h d hrest

/-- Every input and output type of every function a mutual block generates
    uses only constructors `ks` registers at their arities, when `ks`
    registers `arrow` at arity 2, `bool` at arity 0 and each datatype of the
    block at its number of type parameters, and every constructor argument type
    uses only constructors `ks` registers at their arities. -/
theorem genBlockFactory_sigsKnown {T : LExprParams} [Inhabited T.Metadata]
    [Inhabited T.IDMeta] [Std.ToFormat T.IDMeta] [BEq T.Identifier]
    (block : MutualDatatype T.IDMeta) (fac : Factory T)
    {ks : KnownTypes} (h_arrow : ks["arrow"]? = some 2)
    (h_bool : ks["bool"]? = some 0)
    (hnames : ∀ d ∈ block, ks[d.name]? = some d.typeArgs.length)
    (hargs : ∀ d ∈ block, ∀ c ∈ d.constrs, ∀ arg ∈ c.args,
      LMonoTy.knownInstance arg.2 ks = true)
    (hgen : genBlockFactory block = .ok fac) :
    ∀ f ∈ fac.toArray, ∀ ty ∈ f.output :: f.inputs.values,
      LMonoTy.knownInstance ty ks = true := by
  refine genBlockFactory_sigs_of (fun ty => LMonoTy.knownInstance ty ks = true)
    (fun _ => by simp only [LMonoTy.knownInstance])
    (fun a b ha hb => knownInstance_arrow ks a b h_arrow ha hb)
    ?_ ?_ block fac ?_ hargs hgen
  · intro a b h
    have h_ab := LMonoTys.knownInstances_iff_forall.mp
      (knownInstance_tcons_inv ks "arrow" [a, b] h).2.2
    exact ⟨h_ab a (by simp), h_ab b (by simp)⟩
  · exact knownInstance_nullary ks "bool" h_bool
  · intro d hd
    refine knownInstance_tcons_of_getElem? ?_ ?_
    · simp only [List.length_map]
      exact hnames d hd
    · intro t ht
      obtain ⟨v, -, rfl⟩ := List.mem_map.mp ht
      simp only [LMonoTy.knownInstance]

/-- Registering a mutual block keeps every datatype registered in the
    known-types table at its number of type parameters. -/
theorem datatypesKnown_addMutualBlock {T : LExprParams}
    [Inhabited T.Metadata] [Inhabited T.IDMeta] [Std.ToFormat T.IDMeta]
    [DecidableEq T.IDMeta] {C C' : LContext T}
    {block : MutualDatatype T.IDMeta}
    (h : C.addMutualBlock block = .ok C') (hC : C.DatatypesKnown) :
    C'.DatatypesKnown := by
  obtain ⟨-, ds, -, -, ks, hds, -, -, hks, rfl⟩ :=
    LContext.addMutualBlock_ok_eq C _ block h
  obtain rfl := TypeFactory.addMutualBlock_ok_eq _ _ block _ hds
  intro d hd
  simp only [TypeFactory.allDatatypes, Array.toList_push (xs := C.datatypes),
    List.flatten_append, List.flatten_cons, List.flatten_nil, List.append_nil,
    List.mem_append] at hd
  rcases hd with hold | hnew
  · exact KnownTypesExtends.of_add_foldlM C.knownTypes ks block hks _ _
      (hC d hold)
  · exact knownTypes_foldlM_add_mem C.knownTypes ks block hks d hnew

/-- An iterated arrow from registered instances to a registered instance is a registered instance
    when `ks` registers `arrow` at arity 2. -/
private theorem knownInstance_mkArrow' {ks : KnownTypes} (h_arrow : ks["arrow"]? = some 2)
    (out : LMonoTy) (ms : LMonoTys) (hout : LMonoTy.knownInstance out ks = true)
    (hms : ∀ t ∈ ms, LMonoTy.knownInstance t ks = true) :
    LMonoTy.knownInstance (LMonoTy.mkArrow' out ms) ks = true :=
  LMonoTy.mkArrow'_of_arrow (fun ty => LMonoTy.knownInstance ty ks = true)
    (fun a b ha hb => knownInstance_arrow ks a b h_arrow ha hb) out ms hout hms

/-- Adding a function whose input and output types are registered instances keeps every
    signature and every datatype registered. -/
theorem tablesKnown_addFactoryFunction {T : LExprParams} {C : LContext T} {fn : LFunc T}
    (hfn : ∀ ty ∈ fn.output :: fn.inputs.values, LMonoTy.knownInstance ty C.knownTypes = true)
    (hs : FactorySigsKnown C.knownTypes C.functions) (hd : C.DatatypesKnown) :
    FactorySigsKnown (C.addFactoryFunction fn).knownTypes (C.addFactoryFunction fn).functions ∧
      (C.addFactoryFunction fn).DatatypesKnown := by
  rw [addFactoryFunction_knownTypes C fn]
  refine ⟨hs.addFactoryFunction hfn, ?_⟩
  unfold LContext.addFactoryFunction
  split <;> exact hd

/-- Adding functions whose input and output types are registered instances keeps every signature
    and every datatype registered. -/
theorem tablesKnown_foldl_addFactoryFunction {T : LExprParams} {α : Type} (l : List α)
    (g : α → LFunc T) (C : LContext T)
    (hs : FactorySigsKnown C.knownTypes C.functions) (hd : C.DatatypesKnown)
    (hg : ∀ a ∈ l, ∀ ty ∈ (g a).output :: (g a).inputs.values,
      LMonoTy.knownInstance ty C.knownTypes = true) :
    FactorySigsKnown (l.foldl (fun C a => C.addFactoryFunction (g a)) C).knownTypes
        (l.foldl (fun C a => C.addFactoryFunction (g a)) C).functions ∧
      (l.foldl (fun C a => C.addFactoryFunction (g a)) C).DatatypesKnown := by
  induction l generalizing C with
  | nil => exact ⟨hs, hd⟩
  | cons a rest ih =>
    rw [List.foldl_cons]
    obtain ⟨hs', hd'⟩ := tablesKnown_addFactoryFunction (hg a List.mem_cons_self) hs hd
    refine ih _ hs' hd' fun b hb ty hty => ?_
    rw [addFactoryFunction_knownTypes C (g a)]
    exact hg b (List.mem_cons_of_mem a hb) ty hty

/-- When `ks` registers `arrow` at arity 2 and every input and output type of `f` is a registered
    instance, so is the body of `f`'s type scheme. -/
theorem LFunc.body_knownInstance {T : LExprParams} [DecidableEq T.IDMeta]
    {ks : KnownTypes} {f : LFunc T} (harrow : ks["arrow"]? = some 2)
    (hsigf : ∀ ty ∈ f.output :: f.inputs.values, LMonoTy.knownInstance ty ks = true)
    {xs : List TyIdentifier} {body : LMonoTy}
    (hty : f.type = .ok (.forAll xs body)) : LMonoTy.knownInstance body ks = true := by
  have hout := hsigf f.output List.mem_cons_self
  have hbody := LFunc.type_eq_mkArrow' harrow hty hout
  simp only [LTy.forAll.injEq] at hbody
  rw [hbody.2]
  refine knownInstance_mkArrow' harrow _ _ hout fun t ht => ?_
  rw [← ListMap.values_eq_map_snd] at ht
  exact hsigf t (List.mem_cons_of_mem _ ht)

/-- Signatures registered in a table that names no alias of `A` are fixed for `A`. -/
theorem FactorySigsKnown.sigsFixed {T : LExprParams} {ks : KnownTypes} {F : Factory T}
    {A : List TypeAlias} (h : FactorySigsKnown ks F)
    (hfresh : ∀ al ∈ A, ks.containsName al.name = false) : FactorySigsFixed A F :=
  fun f hf => ⟨ks, h.1, hfresh, h.2 f hf⟩

/-- `DatatypesKnown` survives growing the registered-type table with the datatypes unchanged. -/
theorem LContext.DatatypesKnown.of_extends {T : LExprParams} {C C' : LContext T}
    (hds : C'.datatypes = C.datatypes) (hext : KnownTypesExtends C.knownTypes C'.knownTypes)
    (h : C.DatatypesKnown) : C'.DatatypesKnown := by
  intro d hd
  rw [hds] at hd
  exact hext _ _ (h d hd)

end -- public section

end Lambda
