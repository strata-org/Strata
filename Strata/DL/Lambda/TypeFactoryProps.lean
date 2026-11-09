/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Lambda.TypeFactory
public import Strata.DL.Lambda.LExprTypeEnv
public import Strata.DL.Lambda.DatatypeWF
public import Strata.DL.Lambda.FactoryWF
import all Strata.DL.Lambda.TypeFactory
import all Strata.DL.Lambda.LExprTypeEnv
import all Strata.DL.Lambda.DatatypeWF
import Strata.Util.ExceptProps
import Strata.Util.ListMapProps
import Strata.Util.ListUtilsProps
import Strata.Util.StateMProps
import all Strata.DL.Lambda.Factory
import all Strata.DL.Lambda.FactoryProps

/-! ## Properties of mutual-datatype validation

Key theorems: `TypeFactory.addMutualBlock_ok_inv` and `LContext.addMutualBlock_ok_inv` (adding
a block means every check it runs passed), `validateMutualBlock_sound` (a validated block's names
are distinct and its datatypes share their type parameters),
`checkConstructorArgVarsScoped_sound` and `validateTypeReferences_arities` (field types use only
datatype parameters and registered arities), `checkConstructorArgsWF_sound` (the constructor-field
check establishes `ConstrArgWF` for every field), and `checkMutualBlockInhab_sound` (the
inhabitance check establishes `TySymInhab` for every datatype).

## Properties of the factories generated from datatype declarations

The only constructors (`isConstr = true` functions) `genBlockFactory` generates are the
`constrFunc`s of the block's datatypes, whose output is the datatype's type constructor
applied to its parameters (`dataDefault`).  So no generated constructor produces a
Boolean when no datatype of the block is named `bool`.

Key theorems: `genBlockFactory_constrsNotBool`, `Factory.ConstrsNotBool.addFactory`,
`Factory.ConstrsNotBool.addFactory_genBlockFactory`, `TypeFactory.genFactory_constrsNotBool`.
-/

namespace Lambda

open Std (ToFormat Format format)

public section

/-! ### Inverting the checks on a mutual block -/

/-- If the duplicate check on type parameters succeeds, each datatype of the block has distinct
    type parameters. -/
private theorem checkTypeParamsNodup_sound {IDMeta : Type} (block : MutualDatatype IDMeta)
    (h : checkTypeParamsNodup block = .ok ()) :
    ∀ d ∈ block, d.typeArgs.Nodup := by
  intro d hd
  simp only [checkTypeParamsNodup] at h
  have hcheck := foldlM_check_ok _ block () h d hd
  elim_err hcheck
  assumption

/-- If the reserved-name check succeeds, no type parameter of the block starts with a reserved
    prefix. -/
private theorem checkTypeParamsNotReserved_sound {IDMeta : Type} (block : MutualDatatype IDMeta)
    (h : checkTypeParamsNotReserved block = .ok ()) :
    ∀ d ∈ block, ∀ v ∈ d.typeArgs, isAllowedName v = true := by
  intro d hd v hv
  simp only [checkTypeParamsNotReserved] at h
  have hcheck := foldlM_check_ok _ block () h d hd
  elim_err hcheck with hnone
  have hnot := List.find?_eq_none.mp hnone v hv
  simpa only [Bool.not_eq_true, Bool.not_eq_false'] using hnot

/-- If the agreement check succeeds, all datatypes of the block declare the same type
    parameters, up to order and repetition. -/
private theorem checkTypeParamsAgree_sound {IDMeta : Type} (block : MutualDatatype IDMeta)
    (h : checkTypeParamsAgree block = .ok ()) :
    ∀ d ∈ block, ∀ d' ∈ block, ∀ v, v ∈ d.typeArgs ↔ v ∈ d'.typeArgs := by
  simp only [checkTypeParamsAgree] at h
  split at h
  · intro d hd; exact absurd hd (by simp)
  rename_i hd0 rest
  elim_err h with hnone
  have hhead : ∀ e ∈ hd0 :: rest, ∀ v, v ∈ e.typeArgs ↔ v ∈ hd0.typeArgs := by
    intro e he v
    rcases List.mem_cons.mp he with rfl | he'
    · exact Iff.rfl
    · have hbad := List.find?_eq_none.mp hnone e he'
      have hsame : e.typeArgs.mergeSort (· ≤ ·) = hd0.typeArgs.mergeSort (· ≤ ·) := by
        have hbad' : sameTypeParams e.typeArgs hd0.typeArgs = true := by simpa using hbad
        simpa only [sameTypeParams, beq_iff_eq] using hbad'
      rw [← List.mem_mergeSort (le := (· ≤ ·)), hsame, List.mem_mergeSort]
  intro d hd d' hd' v
  exact (hhead d hd v).trans (hhead d' hd' v).symm

/-- If the scoping check succeeds, every type variable of a constructor field type is a
    parameter of its datatype. -/
theorem checkConstructorArgVarsScoped_sound {IDMeta : Type} (block : MutualDatatype IDMeta)
    (h : checkConstructorArgVarsScoped block = .ok ()) :
    ∀ d ∈ block, ∀ c ∈ d.constrs, ∀ arg ∈ c.args,
      ∀ v ∈ LMonoTy.freeVars arg.2, v ∈ d.typeArgs := by
  intro d hd c hc arg harg v hv
  simp only [checkConstructorArgVarsScoped] at h
  have hd' := foldlM_check_ok _ block () h d hd
  have hc' := foldlM_check_ok _ d.constrs () hd' c hc
  have harg' := foldlM_check_ok _ c.args () hc' arg harg
  have hv' := foldlM_check_ok _ (LMonoTy.freeVars arg.2) () harg' v hv
  split at hv'
  · assumption
  · exact absurd hv' (by simp)

/-- Success of the mutual-block validation means each of its five checks succeeded. -/
private theorem validateMutualBlock_ok_inv {IDMeta : Type}
    (block : MutualDatatype IDMeta) (h : validateMutualBlock block = .ok ()) :
    checkMutualBlockNonempty block = .ok () ∧ checkDatatypeNamesNodup block = .ok () ∧
      checkTypeParamsNodup block = .ok () ∧ checkTypeParamsNotReserved block = .ok () ∧
      checkTypeParamsAgree block = .ok () := by
  simp only [validateMutualBlock, bind, Except.bind] at h
  elim_err h with v1 h1
  elim_err h with v2 h2
  elim_err h with v3 h3
  elim_err h with v4 h4
  exact ⟨by rw [h1], by rw [h2], by rw [h3], by rw [h4], h⟩

/-- Once the duplicate scan has found a duplicate, it keeps reporting one. -/
private theorem foldl_dup_stays_some {IDMeta : Type} (block : MutualDatatype IDMeta) :
    ∀ (o : Option (LDatatype IDMeta)) (names : Std.HashSet String), o ≠ none →
      (block.foldl (fun p d => if d.name ∈ p.2 then (some d, p.2)
        else (p.1, p.2.insert d.name)) (o, names)).1 ≠ none := by
  induction block with
  | nil => intro o names ho; simpa only [List.foldl_nil] using ho
  | cons d rest ih =>
    intro o names ho
    rw [List.foldl_cons]
    split
    · exact ih (some d) names (by simp)
    · exact ih o (names.insert d.name) ho

/-- If the duplicate scan finds none, the block's datatype names are distinct and absent from
    the starting set. -/
private theorem foldl_dup_none_nodup {IDMeta : Type} (block : MutualDatatype IDMeta) :
    ∀ (o : Option (LDatatype IDMeta)) (names : Std.HashSet String),
      (block.foldl (fun p d => if d.name ∈ p.2 then (some d, p.2)
        else (p.1, p.2.insert d.name)) (o, names)).1 = none →
      (block.map (·.name)).Nodup ∧ ∀ d ∈ block, d.name ∉ names := by
  induction block with
  | nil => intro o names _; exact ⟨by simp, by simp⟩
  | cons d rest ih =>
    intro o names h
    rw [List.foldl_cons] at h
    split at h
    · exact absurd h (foldl_dup_stays_some rest (some d) _ (by simp))
    rename_i hfresh
    obtain ⟨hrestnodup, hrestfresh⟩ := ih o (names.insert d.name) h
    have hnotmem : ∀ e ∈ rest, e.name ≠ d.name ∧ e.name ∉ names := by
      intro e he
      have hne := hrestfresh e he
      rw [Std.HashSet.mem_insert] at hne
      simp only [not_or, beq_iff_eq] at hne
      exact ⟨fun heq => hne.1 heq.symm, hne.2⟩
    refine ⟨?_, ?_⟩
    · rw [List.map_cons, List.nodup_cons]
      refine ⟨?_, hrestnodup⟩
      intro hmem
      obtain ⟨e, he, heq⟩ := List.mem_map.mp hmem
      exact (hnotmem e he).1 heq
    · intro e he
      rcases List.mem_cons.mp he with rfl | he'
      · exact hfresh
      · exact (hnotmem e he').2

/-- A validated block is non-empty, its datatype names are distinct, and its datatypes declare
    the same duplicate-free type parameters up to order, none with a reserved prefix. -/
theorem validateMutualBlock_sound {IDMeta : Type}
    (block : MutualDatatype IDMeta) (h : validateMutualBlock block = .ok ()) :
    block ≠ [] ∧
    (block.map (·.name)).Nodup ∧
    (∀ d ∈ block, ∀ d' ∈ block, ∀ v, v ∈ d.typeArgs ↔ v ∈ d'.typeArgs) ∧
    (∀ d ∈ block, d.typeArgs.Nodup) ∧
    (∀ d ∈ block, ∀ v ∈ d.typeArgs, isAllowedName v = true) := by
  obtain ⟨hne, hnames, hnodup, hreserved, hagree⟩ := validateMutualBlock_ok_inv block h
  have hneq : block ≠ [] := by
    intro hb
    subst block
    simp [checkMutualBlockNonempty] at hne
  simp only [checkDatatypeNamesNodup] at hnames
  elim_err hnames with hdup
  exact ⟨hneq, (foldl_dup_none_nodup block none ∅ hdup).1,
    checkTypeParamsAgree_sound block hagree, checkTypeParamsNodup_sound block hnodup,
    checkTypeParamsNotReserved_sound block hreserved⟩

/-- Closes `b x ≠ .ok (.done ())` for a loop body `b` that only throws or yields. -/
local macro "loop_body_yields" : tactic =>
  `(tactic| (simp only [pure, Except.pure]; split <;> (try split) <;> simp))

/-- Successfully adding a mutual block to the datatype store means every check it runs
    succeeded, with inhabitance checked against the store extended by the block. -/
theorem TypeFactory.addMutualBlock_ok_inv {IDMeta : Type}
    (t t' : @TypeFactory IDMeta) (block : MutualDatatype IDMeta)
    (ar : Std.HashMap String Nat)
    (h : TypeFactory.addMutualBlock t block ar = .ok t') :
    validateMutualBlock block = .ok () ∧
    checkConstructorArgsWF block = .ok () ∧
    checkConstructorArgVarsScoped block = .ok () ∧
    (∀ d ∈ block, t.getType d.name = none) ∧
    TypeFactory.validateTypeReferences t block ar = .ok () ∧
    TypeFactory.checkMutualBlockInhab (t.push block) block = .ok () := by
  simp only [TypeFactory.addMutualBlock, bind, Except.bind] at h
  elim_err h with v1 h1
  elim_err h with v2 h2
  elim_err h with v3 h3
  elim_err h with v4 h4
  elim_err h with v5 h5
  elim_err h with v6 h6
  refine ⟨by rw [h1], by rw [h2], by rw [h3], ?_, by rw [h5], by rw [h6]⟩
  intro d hd
  have hdOk := List.forIn_yield_ok_mem block _ _
    (fun _ _ => by loop_body_yields) h4 d hd
  elim_err hdOk
  assumption

/-! ### The type references a constructor field mentions -/

/-- A type mentions exactly the names that its arity list pairs with some argument count. -/
theorem mem_getTypeRefs_iff (ty : LMonoTy) (ref : String) :
    ref ∈ getTypeRefs ty ↔ ∃ n, (ref, n) ∈ getTypeConsArities ty := by
  induction ty with
  | ftvar v => simp [getTypeRefs, getTypeConsArities]
  | bitvec sz => simp [getTypeRefs, getTypeConsArities]
  | tcons n args ih =>
    simp only [getTypeRefs, getTypeConsArities, List.mem_cons, List.mem_flatMap, Prod.mk.injEq]
    constructor
    · intro hmem
      rcases hmem with rfl | ⟨t, ht, hreft⟩
      · exact ⟨args.length, Or.inl ⟨rfl, rfl⟩⟩
      · obtain ⟨k, hk⟩ := (ih t ht).mp hreft
        exact ⟨k, Or.inr ⟨t, ht, hk⟩⟩
    · intro hex
      obtain ⟨k, hk⟩ := hex
      rcases hk with ⟨hrefn, -⟩ | ⟨t, ht, hk'⟩
      · exact Or.inl hrefn
      · exact Or.inr ⟨t, ht, (ih t ht).mpr ⟨k, hk'⟩⟩

/-- If the arity check succeeds, every type-constructor occurrence in a constructor field type
    has the arity its table records: the given table plus the stored and block datatypes. -/
theorem validateTypeReferences_arities {IDMeta : Type} (t : @TypeFactory IDMeta)
    (block : MutualDatatype IDMeta) (ar : Std.HashMap String Nat)
    (h : TypeFactory.validateTypeReferences t block ar = .ok ()) :
    ∀ d ∈ block, ∀ c ∈ d.constrs, ∀ p ∈ c.args, ∀ ref n, (ref, n) ∈ getTypeConsArities p.2 →
      ((t.allDatatypes ++ block).foldl
        (fun acc (e : LDatatype IDMeta) => acc.insert e.name e.typeArgs.length) ar)[ref]?
        = some n := by
  simp only [TypeFactory.validateTypeReferences, bind, Except.bind] at h
  elim_err h with vblock hblockLoop
  intro d hd c hc p hp ref n hmem
  have hdOk := List.forIn_yield_ok_mem block _ _
    (fun _ _ => by loop_body_yields) hblockLoop d hd
  elim_err hdOk with vconstrs hconstrLoop
  have hcOk := List.forIn_yield_ok_mem d.constrs _ _
    (fun _ _ => by loop_body_yields) hconstrLoop c hc
  elim_err hcOk with vargs hargLoop
  have hpOk := List.forIn_yield_ok_mem c.args _ _
    (fun _ _ => by loop_body_yields) hargLoop p hp
  elim_err hpOk with vrefs hrefLoop
  have hrefOk := List.forIn_yield_ok_mem (getTypeConsArities p.2) _ _
    (fun _ _ => by loop_body_yields) hrefLoop
    (ref, n) hmem
  elim_err hrefOk with declaredArity hlookup
  elim_err hrefOk with hne
  have hn : n = declaredArity := by
    simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hne
    exact hne
  rw [hn]
  exact hlookup

/-! ### Registering a mutual block in a context -/

/-- Successfully adding a mutual block to a context means no datatype of the block is named
    like a known type, and the block was added to the context's datatype store. -/
theorem LContext.addMutualBlock_ok_inv {T : LExprParams} [DecidableEq T.IDMeta]
    [Inhabited T.IDMeta] [Inhabited T.Metadata] [ToFormat T.IDMeta]
    (C C' : LContext T) (block : MutualDatatype T.IDMeta)
    (h : C.addMutualBlock block = .ok C') :
    (∀ d ∈ block, ¬ C.knownTypes.containsName d.name) ∧
    TypeFactory.addMutualBlock C.datatypes block C.knownTypes = .ok C'.datatypes := by
  simp only [LContext.addMutualBlock, bind, Except.bind] at h
  elim_err h with vloop hloop
  elim_err h with ds hds
  elim_err h with fgen hfgen
  elim_err h with fs hfs
  elim_err h with ks hks
  simp only [Except.ok.injEq] at h
  subst h
  refine ⟨?_, hds⟩
  intro d hd
  have hdOk := List.forIn_yield_ok_mem block _ _
    (fun _ _ => by loop_body_yields) hloop d hd
  elim_err hdOk
  assumption

/-! ### Positivity, uniformity and non-nesting of constructor field types

`checkConstructorArgsWF` establishes `NotNested` and `StrictPosUnif`. -/

/-- A type mentioning a name is detected as mentioning it. -/
private theorem tyNameAppearsIn_of_TyNameAppears (n : String) (ty : LMonoTy)
    (h : TyNameAppears n ty) :
    tyNameAppearsIn n ty = true := by
  induction h with
  | head args => simp [tyNameAppearsIn]
  | arg n1 args t ht _ ih =>
    simp only [tyNameAppearsIn, Bool.or_eq_true]
    exact Or.inr (List.any_eq_true.mpr ⟨tyNameAppearsIn n t, List.mem_map_of_mem ht, ih⟩)

/-- A type the detector rejects does not mention the name. -/
private theorem tyNameAbsent_of_tyNameAppearsIn_false (n : String) (ty : LMonoTy)
    (h : tyNameAppearsIn n ty = false) : TyNameAbsent n ty := by
  intro happ
  rw [tyNameAppearsIn_of_TyNameAppears n ty happ] at h
  exact absurd h (by simp)

/-- A type the uniformity check accepts uses the given name only at the given arguments. -/
private theorem checkUniform_sound (c : Format) (n : String) (args : List LMonoTy)
    (ty : LMonoTy) (h : checkUniform c n args ty = Except.ok ()) :
    UniformOccur n args ty := by
  fun_induction checkUniform c n args ty
  case case1 =>
    rename_i n1 args1 hEq
    simp only [Bool.and_eq_true, beq_iff_eq] at hEq
    rw [hEq.1, hEq.2]
    exact UniformOccur.self
  case case2 => exact absurd h (by simp)
  case case3 =>
    rename_i n1 args1 _ hNotName ih
    refine UniformOccur.other n1 args1 ?_ ?_
    · intro hn1
      simp only [Bool.not_eq_true, beq_eq_false_iff_ne, ne_eq] at hNotName
      exact hNotName hn1.symm
    · intro t ht
      exact ih t ht (foldrM_check_ok _ args1 h t ht)
  case case4 =>
    rename_i ty' hNotCons
    cases ty' with
    | ftvar v => exact UniformOccur.ftvar v
    | bitvec sz => exact UniformOccur.bitvec sz
    | tcons n1 args1 => exact absurd rfl (hNotCons n1 args1)

/-- A type application other than `arrow` on two arguments is not a binary arrow. -/
private theorem not_isBinaryArrow_tcons (n1 : String) (args1 : List LMonoTy)
    (h : ∀ t1 t2, n1 = "arrow" → args1 = [t1, t2] → False) :
    ¬ IsBinaryArrow (.tcons n1 args1) := by
  intro hex
  obtain ⟨t1, t2, heq⟩ := hex
  simp only [LMonoTy.arrow, LMonoTy.tcons.injEq] at heq
  exact h t1 t2 heq.1 heq.2

/-- A type the nesting check accepts satisfies `NotNested` for the block. -/
private theorem checkNotNested_sound (c : Format) (block : MutualDatatype Unit) (ty : LMonoTy)
    (h : checkNotNested c block ty = .ok ()) : NotNested block ty := by
  fun_induction checkNotNested c block ty
  case case1 =>
    rename_i t1 t2 ih2 ih1
    simp only [bind, Except.bind] at h
    elim_err h with v hv
    exact NotNested.arrow t1 t2 (ih2 hv) (ih1 h)
  case case2 =>
    rename_i n1 args1 _ hmem
    exact NotNested.headBlock n1 args1 hmem
  case case3 => exact absurd h (by simp)
  case case4 =>
    rename_i n1 args1 hNotArrow hmem hfind ih
    refine NotNested.headOther n1 args1 (not_isBinaryArrow_tcons n1 args1 hNotArrow) hmem ?_ ?_
    · intro d hd a ha
      have hnone := List.find?_eq_none.mp hfind d hd
      simp only [Bool.not_eq_true] at hnone
      have habsent : tyNameAppearsIn d.name a = false := by
        simpa using List.any_eq_false.mp hnone a ha
      exact tyNameAbsent_of_tyNameAppearsIn_false d.name a habsent
    · intro a ha
      exact ih a ha (foldlM_check_ok _ args1 () h a ha)
  case case5 =>
    rename_i ty' _ hNotCons
    cases ty' with
    | ftvar v => exact NotNested.ftvar v
    | bitvec sz => exact NotNested.bitvec sz
    | tcons n1 args1 => exact absurd rfl (hNotCons n1 args1)

/-- A type the positivity check accepts has no block datatype in its outer arrows' domains and
    applies every block datatype to its own parameters. -/
private theorem checkStrictPosUnifTy_sound (c : Format) (block : MutualDatatype Unit) (ty : LMonoTy)
    (h : checkStrictPosUnifTy c block ty = .ok ()) : StrictPosUnif block ty := by
  fun_induction checkStrictPosUnifTy c block ty
  case case1 => exact absurd h (by simp)
  case case2 =>
    rename_i t1 t2 hfind ih
    refine StrictPosUnif.arrow t1 t2 ?_ (ih h)
    intro d hd
    have habsent : tyNameAppearsIn d.name t1 = false := by
      simpa using List.find?_eq_none.mp hfind d hd
    exact tyNameAbsent_of_tyNameAppearsIn_false d.name t1 habsent
  case case3 =>
    rename_i ty' hNotArrow
    refine StrictPosUnif.base ty' ?_ ?_
    · intro hex
      obtain ⟨t1, t2, heq⟩ := hex
      exact hNotArrow t1 t2 heq
    · intro d hd
      exact checkUniform_sound c d.name (d.typeArgs.map .ftvar) ty'
        (foldlM_check_ok _ block () h d hd)

/-- If the constructor-argument check succeeds, every constructor field type of the block is
    not nested, strictly positive and uniform. -/
theorem checkConstructorArgsWF_sound (block : MutualDatatype Unit)
    (h : checkConstructorArgsWF block = .ok ()) :
    ∀ d ∈ block, ∀ c ∈ d.constrs, ∀ arg ∈ c.args, ConstrArgWF block arg.2 := by
  intro d hd c hc arg harg
  simp only [checkConstructorArgsWF] at h
  have hd' := foldlM_check_ok _ block () h d hd
  have hc' := foldlM_check_ok _ d.constrs () hd' c hc
  have harg' := foldlM_check_ok _ c.args () hc' arg harg
  simp only [bind, Except.bind] at harg'
  split at harg'
  · exact absurd harg' (by simp)
  rename_i v hv
  exact ⟨checkNotNested_sound _ block arg.2 hv, checkStrictPosUnifTy_sound _ block arg.2 harg'⟩

/-! ### Inhabitance of a mutual block -/

/-- Every `true` entry of the memo table names an inhabited type symbol. -/
private def InhabMemoWF (adts : @TypeFactory Unit) (m : inhabMap) : Prop :=
  ∀ ts, m.find? ts = some true → TySymInhab adts ts

/-- Recording a justified entry keeps the memo table justified. -/
private theorem InhabMemoWF.insert {adts : @TypeFactory Unit} {m : inhabMap}
    (hm : InhabMemoWF adts m)
    (ts : String) (res : Bool) (hres : res = true → TySymInhab adts ts) :
    InhabMemoWF adts (m.insert ts res) := by
  intro k hk
  rw [Map.find?_insert] at hk
  split at hk
  · rename_i hkts
    rw [hkts]
    have hrestrue : res = true := by simpa only [Option.some.injEq] using hk
    exact hres hrestrue
  · exact hm k hk

/-- The empty memo table is justified. -/
private theorem InhabMemoWF.empty (adts : @TypeFactory Unit) : InhabMemoWF adts [] := by
  intro ts hts
  exact absurd hts (by simp [Map.find?])

/-! ### Branches of the inhabitance computation -/

/-- A memoized symbol is answered from the memo table, which is unchanged. -/
private theorem typesym_inhab_memo (adts : @TypeFactory Unit) (seen : List String)
    (hnodup : seen.Nodup) (hsub : seen ⊆ adts.allDatatypes.map (fun x => x.name))
    (ts : String) (m : inhabMap) (b : Bool) (hfind : Map.find? m ts = some b) :
    typesym_inhab adts seen hnodup hsub ts m = (b, m) := by
  rw [typesym_inhab.eq_def]
  simp only [stateM_bind_apply, stateM_get_apply, hfind]
  rfl

/-- An unmemoized symbol under expansion is answered `false`; the table is unchanged. -/
private theorem typesym_inhab_seen (adts : @TypeFactory Unit) (seen : List String)
    (hnodup : seen.Nodup) (hsub : seen ⊆ adts.allDatatypes.map (fun x => x.name))
    (ts : String) (m : inhabMap) (hfind : Map.find? m ts = none)
    (hin : List.elem ts seen = true) :
    typesym_inhab adts seen hnodup hsub ts m = (false, m) := by
  rw [typesym_inhab.eq_def]
  simp only [stateM_bind_apply, stateM_get_apply]
  split
  · simp only [hfind]
    rfl
  · rename_i hbad
    exact absurd hin hbad

/-- An unmemoized symbol naming no stored datatype is assumed inhabited; the table is
    unchanged. -/
private theorem typesym_inhab_external (adts : @TypeFactory Unit) (seen : List String)
    (hnodup : seen.Nodup) (hsub : seen ⊆ adts.allDatatypes.map (fun x => x.name))
    (ts : String) (m : inhabMap) (hfind : Map.find? m ts = none)
    (hin : List.elem ts seen = false) (hgt : adts.getType ts = none) :
    typesym_inhab adts seen hnodup hsub ts m = (true, m) := by
  rw [typesym_inhab.eq_def]
  simp only [stateM_bind_apply, stateM_get_apply]
  split
  · rename_i hbad
    rw [hin] at hbad
    exact absurd hbad (by simp)
  · split
    · simp only [hfind]
      rfl
    · rename_i l' hgt2
      rw [hgt] at hgt2
      exact absurd hgt2 (by simp)

/-- An unmemoized stored datatype not under expansion is answered by scanning its constructors
    with it marked as expanding; the answer is memoized unless it is `false` under an outer
    expansion. -/
private theorem typesym_inhab_datatype_eq (adts : @TypeFactory Unit) (seen : List String)
    (hnodup : seen.Nodup) (hsub : seen ⊆ adts.allDatatypes.map (fun x => x.name))
    (ts : String) (m : inhabMap) (l : LDatatype Unit)
    (hnodup0 : (l.name :: seen).Nodup)
    (hsub0 : (l.name :: seen) ⊆ adts.allDatatypes.map (fun x => x.name))
    (hfind : Map.find? m ts = none) (hin : List.elem ts seen = false)
    (hgt : adts.getType ts = some l) :
    typesym_inhab adts seen hnodup hsub ts m =
      let r := (List.foldlM (fun accC (c : LConstr Unit) => do
          let constrInhab ←
            constr_inhab (ty_inhab adts (l.name :: seen) hnodup0 hsub0) c
          pure (accC || constrInhab)) false l.constrs : StateM inhabMap Bool) m
      (r.1, if (r.1 || seen.isEmpty) = true then Map.insert r.2 ts r.1 else r.2) := by
  rw [typesym_inhab.eq_def]
  simp only [stateM_bind_apply, stateM_get_apply]
  split
  · rename_i hbad
    rw [hin] at hbad
    exact absurd hbad (by simp)
  · split
    · rename_i hgt2
      rw [hgt] at hgt2
      exact absurd hgt2 (by simp)
    · rename_i l' hgt2
      rw [hgt, Option.some.injEq] at hgt2
      subst hgt2
      simp only [hfind, stateM_bind_apply]
      split <;> rfl

/-! ### Soundness of the inhabitance computation -/

/-- Both inhabitance computations keep the memo table justified, and their `true` answers are
    justified by `TySymInhab` or `TyInhab`. -/
private theorem inhab_sound_aux (adts : @TypeFactory Unit) (n : Nat) :
    ∀ (seen : List String) (hnodup : seen.Nodup)
      (hsub : seen ⊆ adts.allDatatypes.map (fun x => x.name)),
      adts.allDatatypes.length - seen.length = n →
      (∀ ts m, InhabMemoWF adts m →
        InhabMemoWF adts (typesym_inhab adts seen hnodup hsub ts m).2 ∧
        ((typesym_inhab adts seen hnodup hsub ts m).1 = true → TySymInhab adts ts)) ∧
      (∀ t m, InhabMemoWF adts m →
        InhabMemoWF adts (ty_inhab adts seen hnodup hsub t m).2 ∧
        ((ty_inhab adts seen hnodup hsub t m).1 = true → TyInhab adts t)) := by
  induction n using Nat.strongRecOn with
  | ind n ihn =>
  intro seen hnodup hsub hn
  have hTS : ∀ ts m, InhabMemoWF adts m →
      InhabMemoWF adts (typesym_inhab adts seen hnodup hsub ts m).2 ∧
      ((typesym_inhab adts seen hnodup hsub ts m).1 = true → TySymInhab adts ts) := by
    intro ts m hm
    cases hfind : Map.find? m ts with
    | some b =>
      rw [typesym_inhab_memo adts seen hnodup hsub ts m b hfind]
      refine ⟨hm, fun hv => hm ts ?_⟩
      rw [hfind, show b = true from hv]
    | none =>
      cases hinelem : List.elem ts seen with
      | true =>
        rw [typesym_inhab_seen adts seen hnodup hsub ts m hfind hinelem]
        exact ⟨hm, fun hv => absurd (show (false : Bool) = true from hv) (by simp)⟩
      | false =>
        cases hgt : adts.getType ts with
        | none =>
          rw [typesym_inhab_external adts seen hnodup hsub ts m hfind hinelem hgt]
          exact ⟨hm, fun _ => TySymInhab.external ts hgt⟩
        | some l =>
          have hfindl : adts.allDatatypes.find? (fun d => d.name == ts) = some l := by
            simpa only [TypeFactory.getType] using hgt
          have hlmem : l ∈ adts.allDatatypes := List.mem_of_find?_eq_some hfindl
          have hlname : l.name = ts := by
            have hp := List.find?_some hfindl
            simpa only [beq_iff_eq] using hp
          have hnamemem : l.name ∈ adts.allDatatypes.map (fun x => x.name) :=
            List.mem_map_of_mem hlmem
          have hnotin : l.name ∉ seen := by
            rw [hlname]
            intro hmem
            rw [List.elem_iff.mpr hmem] at hinelem
            exact absurd hinelem (by simp)
          have hnodup0 : (l.name :: seen).Nodup := List.nodup_cons.mpr ⟨hnotin, hnodup⟩
          have hsub0 : (l.name :: seen) ⊆ adts.allDatatypes.map (fun x => x.name) :=
            List.cons_subset.mpr ⟨hnamemem, hsub⟩
          have hlt : adts.allDatatypes.length - (l.name :: seen).length < n := by
            have hle := List.subset_nodup_length hnodup0 hsub0
            simp only [List.length_cons, List.length_map] at hle ⊢
            omega
          have hTYsmall := (ihn _ hlt (l.name :: seen) hnodup0 hsub0 rfl).2
          -- A constructor is justified when the check accepts all of its field types.
          have hGc : ∀ c : LConstr Unit, ∀ mm, InhabMemoWF adts mm →
              InhabMemoWF adts
                (constr_inhab (ty_inhab adts (l.name :: seen) hnodup0 hsub0) c mm).2 ∧
              ((constr_inhab (ty_inhab adts (l.name :: seen) hnodup0 hsub0) c mm).1 = true →
                ConstrInhab adts c) := by
            intro c mm hmm
            obtain ⟨hmF, hF⟩ := foldlM_and_sound (InhabMemoWF adts)
              (fun p : Identifier Unit × LMonoTy =>
                ty_inhab adts (l.name :: seen) hnodup0 hsub0 p.2)
              (fun p : Identifier Unit × LMonoTy => TyInhab adts p.2) c.args
              (fun x _ mx hmx => hTYsmall x.2 mx hmx) true mm hmm
            exact ⟨hmF, fun hv => ConstrInhab.mk c (fun arg harg => (hF hv).2 arg harg)⟩
          obtain ⟨hmBig, hBig⟩ := foldlM_or_sound (InhabMemoWF adts)
            (constr_inhab (ty_inhab adts (l.name :: seen) hnodup0 hsub0))
            (fun c : LConstr Unit => ConstrInhab adts c) l.constrs
            (fun c _ mm hmm => hGc c mm hmm) false m hm
          have hres : (List.foldlM (fun accC (c : LConstr Unit) => do
                let constrInhab ←
                  constr_inhab (ty_inhab adts (l.name :: seen) hnodup0 hsub0) c
                pure (accC || constrInhab)) false l.constrs m).1 = true →
              TySymInhab adts ts := by
            intro hv
            rcases hBig hv with hfalse | ⟨c, hc, hci⟩
            · exact absurd hfalse (by simp)
            · exact TySymInhab.datatype ts l c hgt hc hci
          rw [typesym_inhab_datatype_eq adts seen hnodup hsub ts m l hnodup0 hsub0
            hfind hinelem hgt]
          dsimp only
          refine ⟨?_, hres⟩
          split
          · exact hmBig.insert ts _ hres
          · exact hmBig
  refine ⟨hTS, ?_⟩
  intro t
  induction t with
  | ftvar v =>
    intro m hm
    rw [ty_inhab.eq_def]
    exact ⟨hm, fun _ => TyInhab.ftvar v⟩
  | bitvec sz =>
    intro m hm
    rw [ty_inhab.eq_def]
    exact ⟨hm, fun _ => TyInhab.bitvec sz⟩
  | tcons name args ih =>
    intro m hm
    rw [ty_inhab.eq_def]
    simp only [stateM_bind_apply]
    obtain ⟨hmS, hSym⟩ := hTS name m hm
    split
    · rename_i hchk
      obtain ⟨hmF, hF⟩ := foldrM_and_sound (InhabMemoWF adts)
        (fun ty => ty_inhab adts seen hnodup hsub ty) (fun ty => TyInhab adts ty) args
        (fun x hx mx hmx => ih x hx mx hmx) true
        (typesym_inhab adts seen hnodup hsub name m).2 hmS
      exact ⟨hmF, fun hv =>
        TyInhab.tcons name args (hSym hchk) (fun a ha => (hF hv).2 a ha)⟩
    · exact ⟨hmS, fun hv => absurd (show (false : Bool) = true from hv) (by simp)⟩

/-- A `true` answer for a datatype name means it is inhabited, and the memo table stays
    justified. -/
private theorem adt_inhab_sound (adts : @TypeFactory Unit) (ts : String) (m : inhabMap)
    (hm : InhabMemoWF adts m) :
    InhabMemoWF adts (adt_inhab adts ts m).2 ∧
    ((adt_inhab adts ts m).1 = true → TySymInhab adts ts) := by
  simp only [adt_inhab]
  exact (inhab_sound_aux adts adts.allDatatypes.length [] List.nodup_nil (List.nil_subset _)
    (Nat.sub_zero _)).1
    ts m hm

/-- Success of the block inhabitance check means every datatype of the block is inhabited. -/
theorem checkMutualBlockInhab_sound (adts : @TypeFactory Unit) (block : MutualDatatype Unit)
    (h : TypeFactory.checkMutualBlockInhab adts block = .ok ()) :
    ∀ d ∈ block, TySymInhab adts d.name := by
  simp only [TypeFactory.checkMutualBlockInhab] at h
  elim_err h with hnone
  have hsound := foldlM_option_sound (InhabMemoWF adts)
    (fun e : LDatatype Unit => adt_inhab adts e.name)
    (fun e : LDatatype Unit => TySymInhab adts e.name) (fun e => e.name)
    block (fun x _ mm hmm => adt_inhab_sound adts x.name mm hmm) none []
    (InhabMemoWF.empty adts)
  refine fun d hd => (hsound.2 ?_).2 d hd
  -- The check and the lemma write the same step function with separate `match`es,
  -- which do not unify; they agree pointwise.
  have hcongr : ∀ f g : Option String → LDatatype Unit → StateM inhabMap (Option String),
      (∀ x e, f x e = g x e) →
        List.foldlM f none block [] = List.foldlM g none block [] := by
    intro f g hfg
    rw [funext fun x => funext (hfg x)]
  refine Eq.trans (congrArg Prod.fst (hcongr _ _ ?_)) hnone
  intro x e
  cases x <;> rfl

end

public section

variable {T : LExprParams} [Inhabited T.Metadata] [Inhabited T.IDMeta] [Std.ToFormat T.IDMeta]

omit [Inhabited T.IDMeta] in
/-- Adding functions none of which is a constructor producing a Boolean keeps
    `ConstrsNotBool`. -/
private theorem Factory.ConstrsNotBool.tryAddAll {F F' : Factory T} {fs : List (LFunc T)}
    (hF : F.ConstrsNotBool)
    (hfs : ∀ fn ∈ fs, fn.isConstr = true → ∀ S, LMonoTy.subst S fn.output ≠ .bool)
    (h : F.tryAddAll fs.toArray = .ok F') : F'.ConstrsNotBool := by
  rw [Factory.tryAddAll, List.foldlM_toArray] at h
  exact fun fn hfn => (Factory.mem_foldlM_tryPush fs F F' h fn hfn).elim (hF fn) (hfs fn)

omit [Inhabited T.Metadata] [Inhabited T.IDMeta] [Std.ToFormat T.IDMeta] in
/-- No substitution turns a datatype not named `bool` into the Boolean type. -/
private theorem subst_dataDefault_ne_bool {d : LDatatype T.IDMeta} (hd : d.name ≠ "bool")
    (S : Subst) : LMonoTy.subst S (dataDefault d) ≠ .bool := by
  unfold LMonoTy.subst
  split <;> simp [dataDefault, data, LMonoTy.substCore, LMonoTy.bool, hd]

/-- **Generated constructors are not Boolean.**  When no datatype of the block is named
    `bool`, the factory `genBlockFactory` generates has no constructor whose output is
    `bool` under any type substitution. -/
theorem genBlockFactory_constrsNotBool [BEq T.Identifier] {block : MutualDatatype T.IDMeta}
    {F : Factory T} (hname : ∀ d ∈ block, d.name ≠ "bool")
    (h : genBlockFactory block = .ok F) : F.ConstrsNotBool := by
  unfold genBlockFactory at h
  split at h
  · cases h
    exact fun _ hfn => absurd hfn (by simp [Factory.default])
  · refine Factory.ConstrsNotBool.tryAddAll (fun _ hfn => absurd hfn (by simp [Factory.default]))
      ?_ h
    intro fn hfn hc
    simp only [List.mem_append, List.mem_flatMap, List.mem_map, elimFuncs, testerFunc,
      destructorFuncs, unsafeDestructorFuncs, mkDestructorFunc, List.mem_mapIdx] at hfn
    rcases hfn with (((hfn | hfn) | hfn) | hfn) | hfn
    · split at hfn
      · simp at hfn
      · simp only [List.mem_map] at hfn
        obtain ⟨_, -, rfl⟩ := hfn
        simp at hc
    · obtain ⟨d, hd, c, -, rfl⟩ := hfn
      exact subst_dataDefault_ne_bool (hname d hd)
    all_goals grind

omit [Inhabited T.IDMeta] in
/-- **Extending keeps `ConstrsNotBool`.**  Adding to a factory none of whose constructors
    produces a Boolean a factory with the same property gives a factory with the same
    property. -/
theorem Factory.ConstrsNotBool.addFactory {F G F' : Factory T} (hF : F.ConstrsNotBool)
    (hG : G.ConstrsNotBool) (h : F.addFactory G = .ok F') : F'.ConstrsNotBool :=
  Factory.ConstrsNotBool.tryAddAll hF (fs := G.toArray.toList)
    (fun fn hfn => hG fn (by simpa using hfn)) (by simpa [Factory.addFactory] using h)

/-- **Extending with generated constructors keeps `ConstrsNotBool`.**  Adding the factory
    of a block of datatypes, none named `bool`, to a factory none of whose constructors
    produces a Boolean gives a factory none of whose constructors produces a Boolean. -/
theorem Factory.ConstrsNotBool.addFactory_genBlockFactory [BEq T.Identifier]
    {block : MutualDatatype T.IDMeta} {F G F' : Factory T} (hF : F.ConstrsNotBool)
    (hname : ∀ d ∈ block, d.name ≠ "bool") (hG : genBlockFactory block = .ok G)
    (h : F.addFactory G = .ok F') : F'.ConstrsNotBool :=
  hF.addFactory (genBlockFactory_constrsNotBool hname hG) h

/-- **The factory of a type factory has no Boolean constructor.**  When no datatype of the
    type factory `t` is named `bool`, no constructor of `t.genFactory` produces a Boolean. -/
theorem TypeFactory.genFactory_constrsNotBool [BEq T.Identifier] {t : @TypeFactory T.IDMeta}
    {F : Factory T} (hname : ∀ d ∈ t.allDatatypes, d.name ≠ "bool")
    (h : t.genFactory = .ok F) : F.ConstrsNotBool := by
  unfold TypeFactory.genFactory at h
  rw [← Array.foldlM_toList (xs := t)] at h
  have hname' : ∀ b ∈ t.toList, ∀ d ∈ b, d.name ≠ "bool" := fun b hb d hd =>
    hname d (List.mem_flatten.mpr ⟨b, hb, hd⟩)
  generalize t.toList = l at h hname'
  suffices hgen : ∀ (l : List (MutualDatatype T.IDMeta)) (F0 : Factory T), F0.ConstrsNotBool →
      (∀ b ∈ l, ∀ d ∈ b, d.name ≠ "bool") →
      l.foldlM (fun f block => do f.addFactory (← genBlockFactory block)) F0 = .ok F →
      F.ConstrsNotBool from
    hgen l _ (fun _ hfn => absurd hfn (by simp [Factory.default])) hname' h
  intro l
  induction l with
  | nil => intro F0 hF0 _ h; cases h; exact hF0
  | cons b bs ih =>
    intro F0 hF0 hn h
    simp only [List.foldlM_cons, bind, Except.bind] at h
    split at h
    · cases h
    · rename_i F1 hF1
      split at hF1
      · cases hF1
      · rename_i G hG
        exact ih F1 (hF0.addFactory_genBlockFactory (hn b (by simp)) hG hF1)
          (fun b' hb' => hn b' (by simp [hb'])) h

end -- public section

end Lambda
