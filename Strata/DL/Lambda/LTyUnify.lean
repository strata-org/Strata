/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Lambda.LTy
import all Strata.DL.Lambda.LTy
public import Strata.DL.Util.List
import all Strata.DL.Util.List
public import Strata.DL.Util.Maps
import all Strata.DL.Util.Maps
import all Strata.DL.Util.Map

/-!
## Type Substitution and Unification

Implementation of type substitution and unification for Lambda. This is similar
to Algorithm J in Hindley-Milner systems.
-/

---------------------------------------------------------------------

namespace Lambda

open Std (ToFormat Format format)

public section

/-! ### Type Substitution -/

/-- Substitution mapping type variables to `LMonoTy`. -/
@[expose] abbrev SubstOne := Map TyIdentifier LMonoTy
@[expose] abbrev SubstOne.empty : SubstOne := []

/--
Substitution mapping type variables to `LMonoTy`, taking scopes into
account. The oldest scope can be obtained via `Maps.oldest`.
-/
@[expose] abbrev Subst := Maps TyIdentifier LMonoTy
@[expose] abbrev Subst.empty : Subst := []
/--
A `Subst` with an empty scope, typically meant for storing global type
substitutions.
-/
@[expose] abbrev Subst.emptyScope : Subst := [[]]

instance : ToFormat Subst where
  format := Maps.format'

/--
Check if `Subst` contains only empty scopes.
-/
def Subst.hasEmptyScopes (S : Subst) : Bool :=
  S.all (fun s => s.isEmpty)

@[simp]
theorem Subst.hasEmptyScopes_empty :
  Subst.hasEmptyScopes Subst.empty := by
  simp +ground

@[simp]
theorem Subst.hasEmptyScopes_emptyScope :
  Subst.hasEmptyScopes Subst.emptyScope := by
  simp +ground

/--
The free variables in a substitution `S` are the union of the free variables in
every type in `S`.

Note that we do not deduplicate the resulting list.
-/
def Subst.freeVars (S : Subst) : List TyIdentifier :=
  S.values.flatMap LMonoTy.freeVars

@[simp]
theorem Subst.freeVars_empty :
    Subst.freeVars Subst.empty = [] := by
  simp [Subst.freeVars, Maps.values]

@[simp]
theorem Subst.freeVars_cons (S : Subst) :
    Subst.freeVars (s :: S) = Subst.freeVars [s] ++ S.freeVars := by
  simp [Subst.freeVars, Maps.values]

theorem Subst.freeVars_of_find_subset (S : Subst) (hi : Maps.find? S i = some sty) :
    LMonoTy.freeVars sty ⊆ Subst.freeVars S := by
  have h_sty_map_value := @Maps.find?_mem_values _ _ i sty _ S hi
  simp only [Subst.freeVars]
  grind

/--
A substitution map `S` is well-formed if no key appears in the free type
variables of the values.
-/
def SubstWF (S : Subst) : Bool :=
  S.keys.all (fun k => k ∉ Subst.freeVars S)

@[simp]
theorem SubstWF_of_empty : SubstWF Subst.empty := by
  simp [SubstWF]

@[simp]
theorem SubstWF_of_empty_empty : SubstWF Subst.emptyScope := by
  unfold SubstWF List.all Maps.keys Map.keys
  unfold Maps.keys
  split <;> simp_all

theorem SubstWF_of_cons (h : SubstWF (s :: S)) :
    SubstWF [s] ∧ SubstWF S := by
  simp_all [SubstWF, Subst.freeVars]
  constructor
  · -- SubstWF [s]
    intro ty hty id hid
    exact h ty (by simp_all [Maps.keys]) id (by simp_all [Maps.values])
  · -- SubstWF S
    intro ty hty id hid
    exact h ty (by simp_all [Maps.keys]) id (by simp_all [Maps.values])
  done

theorem SubstWF.single_subst (id : TyIdentifier) (h : ¬id ∈ ty.freeVars) :
    SubstWF [[(id, ty)]] := by
  unfold SubstWF
  simp only [Maps.keys, Map.keys, Subst.freeVars, Maps.values, Map.values, List.flatMap]
  simp_all
  done


theorem Subst.mem_freeVars_of_mem_freeVars_remove (S : Subst) (id : TyIdentifier)
  (h : xty ∈ Subst.freeVars (Maps.remove S id)) :
  xty ∈ Subst.freeVars S := by
  simp_all [Subst.freeVars]
  obtain ⟨aty, h1, h2⟩ := h
  apply Exists.intro aty; simp_all
  simp [@Maps.mem_values_of_mem_keys_remove _ _ _ _ S id aty h1]

theorem SubstWF_of_remove (id : TyIdentifier) (h : SubstWF S) :
  SubstWF (Maps.remove S id) := by
  simp_all [SubstWF]
  intro xty h_xty_in_keys h_xty_in_fvs
  have h_xty_in_s_keys := @Maps.mem_keys_of_mem_keys_remove _ _ _ _ S id xty h_xty_in_keys
  have h_xty_not_in_fvs := @h xty h_xty_in_s_keys
  have := @Subst.mem_freeVars_of_mem_freeVars_remove xty S id h_xty_in_fvs
  contradiction

/--
A type substitution, along with a proof that it is well-formed.
-/
structure SubstInfo where
  subst : Subst
  isWF : SubstWF subst
  deriving Repr

def SubstInfo.empty : SubstInfo :=
  { subst := Subst.empty,
    isWF := SubstWF_of_empty }

instance : Inhabited SubstInfo where
  default := SubstInfo.empty

mutual
/--
Apply substitution `S` to monotype `mty`.
-/
@[expose] def LMonoTy.subst (S : Subst) (mty : LMonoTy) : LMonoTy :=
  if Subst.hasEmptyScopes S then mty else
  match mty with
  | .ftvar x => match S.find? x with
                | some sty => sty | none => mty
  | .bitvec _ => mty
  | .tcons name ltys =>
    .tcons name (LMonoTys.subst S ltys)
/--
Apply substitution `S` to monotypes `mtys`.
-/
@[expose] def LMonoTys.subst (S : Subst) (mtys : LMonoTys) : LMonoTys :=
  if Subst.hasEmptyScopes S then mtys else substAux S mtys []
where
  substAux S mtys acc : LMonoTys :=
  match mtys with
  | [] => acc.reverse
  | ty :: rest => substAux S rest (LMonoTy.subst S ty :: acc)
end

/--
Non tail-recursive version of `LMonoTys.subst`, useful for proofs.

See theorem `LMonoTys.subst_eq_substLogic`.
-/
def LMonoTys.substLogic (S : Subst) (mtys : LMonoTys) : LMonoTys :=
  if S.hasEmptyScopes then mtys else
  match mtys with
  | [] => []
  | mty :: mrest =>
    LMonoTy.subst S mty :: LMonoTys.substLogic S mrest

theorem LMonoTys.subst_eq_substLogic (S : Subst) (mtys : LMonoTys) :
    LMonoTys.subst S mtys = LMonoTys.substLogic S mtys := by
  by_cases hSEmpty : S.hasEmptyScopes
  case pos =>
    unfold LMonoTys.substLogic
    simp_all [subst]
  case neg =>
  simp_all [LMonoTys.subst]
  suffices h : ∀ acc, LMonoTys.subst.substAux S mtys acc =
                      acc.reverse ++ LMonoTys.substLogic S mtys by
    have := h []
    simp at this
    exact this
  intro acc
  induction mtys generalizing acc with
  | nil =>
    simp [LMonoTys.substLogic, subst.substAux]
  | cons mty mrest ih =>
    simp [LMonoTys.subst.substAux, LMonoTys.substLogic]
    rw [ih]
    simp_all
    done

theorem LMonoTys.substLogic_emptyS (h : S.hasEmptyScopes) :
  LMonoTys.substLogic S mtys = mtys := by
  induction mtys <;> simp_all [substLogic]

theorem LMonoTy.subst_emptyS (h : S.hasEmptyScopes) :
  LMonoTy.subst S ty = ty := by
  unfold LMonoTy.subst
  simp_all
  done

/-- Substitution distributes into `tcons`: `subst S (tcons name args) = tcons name (subst S args)`. -/
theorem LMonoTy.subst_tcons (S : Subst) (name : String) (args : LMonoTys) :
    LMonoTy.subst S (.tcons name args) = .tcons name (LMonoTys.subst S args) := by
  unfold LMonoTy.subst
  split
  · simp [LMonoTys.subst, *]
  · rfl

theorem LMonoTys.subst_nil (S : Subst) : LMonoTys.subst S [] = [] := by
  unfold LMonoTys.subst
  split <;> simp [LMonoTys.subst.substAux]

theorem LMonoTy.subst_bitvec (S : Subst) (n : Nat) : LMonoTy.subst S (.bitvec n) = .bitvec n := by
  unfold LMonoTy.subst
  split <;> rfl

theorem Subst.isEmpty_implies_keys_empty (h : Subst.hasEmptyScopes S) :
  (Maps.keys S) = [] := by
  induction S <;> simp_all [Maps.keys, Subst.hasEmptyScopes, Map.isEmpty]
  split at h <;> simp_all [Map.keys]
  done

theorem Subst.hasEmptyScopes_false_of_find
    (S : Subst) (a : TyIdentifier) (t : LMonoTy)
    (h : Maps.find? S a = some t) : Subst.hasEmptyScopes S = false := by
  cases h_eq : Subst.hasEmptyScopes S with
  | false => rfl
  | true => exact absurd (Subst.isEmpty_implies_keys_empty h_eq ▸ Maps.find?_mem_keys S h)
                         (by simp_all)

theorem Subst.find?_none_of_hasEmptyScopes (h : Subst.hasEmptyScopes S) (x : TyIdentifier) : Maps.find? S x = none := by
  match h_find : Maps.find? S x with
  | some t => exact absurd h (by rw [Subst.hasEmptyScopes_false_of_find S x t h_find]; decide)
  | none => rfl

theorem LMonoTy.subst_unfold (S : Subst) (ty : LMonoTy) :
    LMonoTy.subst S ty = match ty with
      | .ftvar x => match S.find? x with | some sty => sty | none => .ftvar x
      | .bitvec n => .bitvec n
      | .tcons name args => .tcons name (args.map (LMonoTy.subst S)) := by
  conv => lhs; unfold LMonoTy.subst
  split <;> rename_i h
  · cases ty with
    | ftvar x => simp [Subst.find?_none_of_hasEmptyScopes h]
    | bitvec => rfl
    | tcons name args =>
      simp
      induction args with
      | nil => rfl
      | cons a as ih =>
        simp; constructor
        . simp [LMonoTy.subst_emptyS h]
        . assumption
  · induction ty with
    | ftvar x => rfl
    | bitvec => simp
    | tcons name args =>
      -- rw [LMonoTy.subst_tcons]
      simp
      congr 1
      rw [LMonoTys.subst_eq_substLogic]
      induction args with
      | nil =>
        unfold LMonoTys.substLogic
        split <;> grind
      | cons a as ih =>
        unfold LMonoTys.substLogic
        split <;> try contradiction
        simp; grind

/-- `subst` distributes over `mkArrow'`. -/
theorem subst_mkArrow' (S : Subst) (ret : LMonoTy) (ins : List LMonoTy) :
    LMonoTy.subst S (LMonoTy.mkArrow' ret ins) =
    LMonoTy.mkArrow' (LMonoTy.subst S ret) (ins.map (LMonoTy.subst S)) := by
  induction ins with
  | nil => rfl
  | cons t ts ih =>
    simp only [LMonoTy.mkArrow'_cons, List.map]
    rw [LMonoTy.subst_unfold]
    simp only [LMonoTy.arrow, List.map]
    rw [ih]

/-- Like `LMonoTy.subst` but without the `hasEmptyScopes` short-circuit,
so it reduces definitionally on ground types.
Uses structural recursion (no well-founded recursion) so it unfolds in the kernel. -/
@[expose] def LMonoTy.substReduce (S : Subst) : LMonoTy → LMonoTy
  | .ftvar x => match S.find? x with | some sty => sty | none => .ftvar x
  | .bitvec n => .bitvec n
  | .tcons name ltys => .tcons name (substReduceList S ltys)
where substReduceList (S : Subst) : List LMonoTy → List LMonoTy
  | [] => []
  | ty :: tys => substReduce S ty :: substReduceList S tys

theorem LMonoTy.substReduceList_eq_map (S : Subst) (ltys : List LMonoTy) :
    LMonoTy.substReduce.substReduceList S ltys = ltys.map (substReduce S) := by
  induction ltys with
  | nil => rfl
  | cons hd tl ih => simp [substReduce.substReduceList, ih]

theorem LMonoTy.subst_eq_substReduce (S : Subst) (ty : LMonoTy) :
    LMonoTy.subst S ty = LMonoTy.substReduce S ty := by
  induction ty with
  | ftvar x => rw [subst_unfold]; simp [substReduce]
  | bitvec n => rw [subst_unfold]; simp [substReduce]
  | tcons name ltys ih =>
    rw [subst_unfold]; simp only [substReduce, substReduceList_eq_map]
    congr 1
    exact List.map_congr_left ih

/-! ## Type substitution agreement lemmas

These lemmas establish that if two substitutions produce the same result on a
type, they must agree on all free variables of that type — and conversely, if
they agree on all free variables, they produce the same result. -/

/-- If two substitutions produce the same result on a type `ty`, then they
agree on every free variable of `ty` (in the sense of producing the same
substitution result on that variable). -/
theorem subst_eq_implies_agree_on_freeVars
    {S₁ S₂ : Subst}
    {ty : LMonoTy}
    (h : LMonoTy.subst S₁ ty = LMonoTy.subst S₂ ty)
    (v : TyIdentifier)
    (hv : v ∈ LMonoTy.freeVars ty)
    : LMonoTy.subst S₁ (.ftvar v) = LMonoTy.subst S₂ (.ftvar v) := by
  induction ty with
  | ftvar x =>
    simp only [LMonoTy.freeVars, List.mem_singleton] at hv
    subst hv; exact h
  | bitvec n =>
    simp [LMonoTy.freeVars] at hv
  | tcons name args ih =>
    simp only [LMonoTy.subst_unfold] at h
    simp only [LMonoTy.freeVars] at hv
    have h_args := LMonoTy.tcons.inj h |>.2
    -- v ∈ freeVars of some ty ∈ args; find it and apply IH
    have h_map_eq := List.map_eq_map_iff.mp h_args
    have ⟨ty, ht, hv_ty⟩ := LMonoTys.freeVars_exists hv
    exact ih ty ht (h_map_eq ty ht) hv_ty

/-- If two substitutions agree on all free variables of `ty` (in the sense of
producing the same substitution result), then they produce the same result
on `ty`. -/
theorem agree_on_freeVars_implies_subst_eq
    {S₁ S₂ : Subst}
    {ty : LMonoTy}
    (h : ∀ v, v ∈ LMonoTy.freeVars ty →
      LMonoTy.subst S₁ (.ftvar v) = LMonoTy.subst S₂ (.ftvar v))
    : LMonoTy.subst S₁ ty = LMonoTy.subst S₂ ty := by
  induction ty with
  | ftvar v =>
    exact h v (by simp [LMonoTy.freeVars])
  | bitvec n =>
    simp only [LMonoTy.subst_unfold]
  | tcons name args ih =>
    simp only [LMonoTy.subst_unfold]
    congr 1
    simp only [LMonoTy.freeVars] at h
    exact List.map_eq_map_iff.mpr fun ty ht =>
      ih ty ht fun v hv => h v (LMonoTys.freeVars_mem_subset ht hv)

/-- List version: if two substitutions agree on all free variables of every
type in a list, then mapping `subst` over the list produces the same result. -/
theorem agree_on_freeVars_implies_subst_eq_list
    {S₁ S₂ : Subst}
    {tys : List LMonoTy}
    (h : ∀ v, v ∈ LMonoTys.freeVars tys →
      LMonoTy.subst S₁ (.ftvar v) = LMonoTy.subst S₂ (.ftvar v))
    : tys.map (LMonoTy.subst S₁) = tys.map (LMonoTy.subst S₂) :=
  List.map_eq_map_iff.mpr fun _ ht =>
    agree_on_freeVars_implies_subst_eq fun v hv =>
      h v (LMonoTys.freeVars_mem_subset ht hv)

/--
No key (i.e., type identifier) in a well-formed substitution `S` can appear as a
free variable in a substituted type (i.e., in `LMonoTy.subst S ty`).
-/
theorem LMonoTy.subst_keys_not_in_substituted_type (h : SubstWF S) :
    S.keys.all (fun k => k ∉ LMonoTy.freeVars (LMonoTy.subst S ty)) := by
  by_cases hSEmpty : S.hasEmptyScopes
  case pos =>
    simp_all [@Subst.isEmpty_implies_keys_empty S hSEmpty]
  case neg =>
  induction ty
  case ftvar i =>
    simp_all [LMonoTy.subst]
    intro id hid
    split
    · rename_i _ sty heq
      simp_all [SubstWF, Subst.freeVars]
      have hmap := @Maps.find?_mem_values _ _ i sty _ S heq
      exact h id hid sty hmap
    · simp_all [freeVars]
      have := @Maps.find?_of_not_mem_values _ _ i _ S
      simp_all
      exact ne_of_mem_of_not_mem hid this
  case bitvec n =>
    simp_all [LMonoTy.subst]
    unfold LMonoTy.freeVars
    simp
  case tcons name args h1 =>
    simp_all
    simp [subst]
    induction args
    case nil =>
      simp_all [LMonoTys.subst_eq_substLogic, LMonoTys.substLogic, LMonoTys.freeVars, LMonoTy.freeVars]
    case cons head tail tail_ih =>
      simp_all
      obtain ⟨h1, h2⟩ := h1
      intro x hx
      have h1' := h1 x hx
      simp [LMonoTy.freeVars, LMonoTys.subst_eq_substLogic, LMonoTys.substLogic] at tail_ih ⊢
      simp [hSEmpty, h1']
      exact tail_ih x hx
  done

/--
The free variables in a type `mty` after the application of a substitution `S`
are a subset of the free variables in `mty` and the free variables in `S`.
-/
theorem LMonoTy.freeVars_of_subst_subset (S : Subst) (mty : LMonoTy) :
    LMonoTy.freeVars (LMonoTy.subst S mty) ⊆
    LMonoTy.freeVars mty ++ Subst.freeVars S := by
  by_cases hSEmpty : S.hasEmptyScopes
  case pos =>
    unfold subst; simp_all [Subst.hasEmptyScopes]
  case neg =>
  simp [Subst.freeVars]
  induction mty
  case ftvar x =>
    simp_all [subst]
    split
    · -- Case: S.find? x = some sty
      rename_i sty h_find
      intro v hv; simp_all; right
      apply Exists.intro sty; simp [hv]
      apply @Maps.find?_mem_values _ _ x sty _ S h_find
    · -- Case: S.find? x = none
      simp [freeVars]
  case bitvec n =>
    simp [subst]
  case tcons name args ih =>
    simp [LMonoTy.subst, LMonoTy.freeVars]
    induction args
    case nil =>
      simp_all [LMonoTys.freeVars, LMonoTy.freeVars, LMonoTys.subst_eq_substLogic, LMonoTys.substLogic]
    case cons mty mtys mtys_ih =>
      simp at hSEmpty
      simp_all [LMonoTys.subst_eq_substLogic, LMonoTys.substLogic]
      simp [freeVars] at *
      generalize (subst S mty).freeVars = x at mtys_ih ih
      generalize mty.freeVars = a at mtys_ih ih
      generalize LMonoTys.freeVars mtys = b at mtys_ih ih
      generalize List.flatMap freeVars (Maps.values S) = c at mtys_ih ih
      generalize (LMonoTys.substLogic S mtys).freeVars = d at mtys_ih ih
      obtain ⟨ih1, ih2⟩ := ih
      apply And.intro
      case left =>
        have := List.subset_append_right b c
        have : a ++ c ⊆ a ++ (b ++ c) := by
          simp_all (config := {maxDischargeDepth := 1000})
        exact fun _ x => this (ih1 x)
      case right =>
        exact List.subset_append_of_subset_right a mtys_ih
  done

/--
Apply `new` to `old` substitution.
-/
def SubstOne.apply (new old : SubstOne) : SubstOne :=
  applyAux new old []
  where applyAux (new old acc : SubstOne) : SubstOne :=
  match old with
  | [] => acc.reverse
  | (id, lty) :: rest =>
    applyAux new rest ((id, LMonoTy.subst [new] lty) :: acc)

/--
Non tail-recursive version of `SubstOne.apply`, useful for proofs.
-/
def SubstOne.applyLogic (new old : SubstOne) : SubstOne :=
  match old with
  | [] => []
  | (id, lty) :: rest =>
    (id, LMonoTy.subst [new] lty) :: SubstOne.applyLogic new rest

theorem SubstOne.apply_eq_applyLogic (new old : SubstOne) :
    SubstOne.apply new old = SubstOne.applyLogic new old := by
  simp [SubstOne.apply]
  suffices h : ∀ acc, SubstOne.apply.applyAux new old acc =
                  @HAppend.hAppend SubstOne SubstOne SubstOne _
                    acc.reverse (SubstOne.applyLogic new old) by
    have := h []
    simp at this
    exact this
  intro acc
  induction old generalizing acc with
  | nil =>
    simp [SubstOne.applyLogic, apply.applyAux]
    unfold HAppend.hAppend instHAppendMap
    simp_all
  | cons mty mrest ih =>
    simp [SubstOne.apply.applyAux, SubstOne.applyLogic]
    rw [ih]; simp
    unfold HAppend.hAppend instHAppendMap instHAppendOfAppend Append.append List.instAppend
    simp_all
    done

theorem SubstOne.applyLogic_empty_new (h : new.isEmpty) :
  SubstOne.applyLogic new old = old := by
  induction old
  case nil => simp [applyLogic]
  case cons head tail ih =>
    simp [applyLogic]
    have : Subst.hasEmptyScopes [new] := by
      unfold Subst.hasEmptyScopes; simp_all [Map.isEmpty]
    have := @LMonoTy.subst_emptyS [new] head.snd (by assumption)
    simp_all
  done

@[simp]
theorem SubstOne.keys_of_apply_eq :
    Map.keys (SubstOne.apply new old) = Map.keys old := by
  induction old <;> simp_all [Map.keys, SubstOne.apply_eq_applyLogic, SubstOne.applyLogic]

/--
Apply the `new` substitution to the `old` one.
-/
def Subst.apply (new : SubstOne) (old : Subst) : Subst :=
  match old with
  | [] => old
  | o :: orest => SubstOne.apply new o :: (Subst.apply new orest)

@[simp]
theorem Subst.keys_of_apply_eq :
    Maps.keys (Subst.apply new old) = Maps.keys old := by
  induction old
  case nil => simp [Maps.keys, apply]
  case cons hd tl ih => simp_all [Maps.keys, apply]
  done

/-- `Map.find?` after `SubstOne.applyLogic` maps the value through `subst`. -/
theorem SubstOne.find?_applyLogic (new old : SubstOne) (x : TyIdentifier) :
    Map.find? (SubstOne.applyLogic new old) x =
    (Map.find? old x).map (LMonoTy.subst [new]) := by
  induction old with
  | nil => simp [SubstOne.applyLogic, Map.find?]
  | cons hd rest ih =>
    simp only [SubstOne.applyLogic, Map.find?]
    split
    · simp [*]
    · exact ih

/-- `Maps.find?` after `Subst.apply` maps the value through `subst`. -/
theorem Subst.find?_apply (new : SubstOne) (S : Subst) (x : TyIdentifier) :
    Maps.find? (Subst.apply new S) x =
    (Maps.find? S x).map (LMonoTy.subst [new]) := by
  induction S with
  | nil => simp [Subst.apply, Maps.find?]
  | cons hd tl ih =>
    simp only [Subst.apply, Maps.find?]
    rw [SubstOne.apply_eq_applyLogic, SubstOne.find?_applyLogic]
    cases h : Map.find? hd x with
    | some v => simp
    | none => simp; exact ih

/--
No key in a well-formed substitution `newS` appears in the free variables of a
composed substitution `(Subst.apply newS oldS)`. Note that there are no
restrictions on `oldS` here.
-/
theorem Subst.keys_not_in_apply (h : SubstWF [newS]) :
    newS.keys.all (fun k => k ∉ Subst.freeVars (Subst.apply newS oldS)) := by
  simp [Subst.freeVars]
  induction oldS
  case nil => simp [Subst.apply, Maps.values]
  case cons s S ih =>
    simp_all [Subst.apply, SubstOne.apply_eq_applyLogic]
    intro i hi ty hty
    simp [Maps.values] at hty
    cases hty
    case inl h1 =>
      induction s
      case nil => simp_all [SubstOne.applyLogic, Map.values]
      case cons head tail tail_ih =>
        simp [SubstOne.applyLogic, Map.values] at h1
        cases h1 <;> try simp_all
        have h2' := @LMonoTy.subst_keys_not_in_substituted_type [newS] head.snd h
        simp_all [Maps.keys]
    case inr h1 =>
      exact ih i hi ty h1
  done

/--
For all types `mty` in a substitution `(Subst.apply newS S)`, the free variables
in `mty` are a subset of those in `newS` and `S`.
-/
theorem Subst.freeVars_of_apply_subset (newS : SubstOne) (S : Subst) (mty : LMonoTy)
    (h : mty ∈ Maps.values (Subst.apply newS S)) :
    LMonoTy.freeVars mty ⊆ Subst.freeVars [newS] ++ Subst.freeVars S := by
  induction S generalizing mty newS
  case nil =>
    simp_all only [apply, Maps.values, List.not_mem_nil]
  case cons s S S_ih =>
    simp [apply, Maps.values, SubstOne.apply_eq_applyLogic] at h
    cases h with
    | inr h_tail =>
      have : freeVars [newS] ++ freeVars S ⊆ freeVars [newS] ++ freeVars (s :: S) := by
        simp [freeVars, Maps.values]
      exact List.Subset.trans (S_ih newS mty h_tail) this
    | inl h_head =>
      induction s generalizing mty
      case inl.nil =>
        simp_all [freeVars, Maps.values, Map.values, SubstOne.applyLogic]
      case inl.cons hd tl tl_ih =>
        simp_all [freeVars, Maps.values, Map.values]
        simp [SubstOne.applyLogic, Map.values] at h_head
        cases h_head
        · rename_i h
          have h_subset := @LMonoTy.freeVars_of_subst_subset [newS] hd.snd
          simp [freeVars, Maps.values, ←h] at h_subset
          grind
        · grind
    done

/--
The free variables in `(Subst.apply newS S)` are a subset of those in `newS` and
`S`.
-/
theorem Subst.freeVars_of_apply_subset_alt (newS : SubstOne) (S : Subst) :
    Subst.freeVars (Subst.apply newS S) ⊆
    Subst.freeVars [newS] ++ Subst.freeVars S := by
  have h := @Subst.freeVars_of_apply_subset newS S
  simp_all [Subst.freeVars, Maps.values]
  grind
  done

theorem SubstWF.apply_one_substituted_type (S : SubstInfo) (id : TyIdentifier) (ty : LMonoTy) :
    SubstWF (Subst.apply [(id, LMonoTy.subst S.subst ty)] S.subst) := by
  simp [SubstWF]; intro i hi
  generalize h_new_ty : LMonoTy.subst S.subst ty = new_ty at *
  have h1 : S.subst.keys.all (fun k => k ∉ new_ty.freeVars) := by
    have := @LMonoTy.subst_keys_not_in_substituted_type S.subst ty S.isWF
    simp; simp_all
  have hsubset := @Subst.freeVars_of_apply_subset_alt [(id, new_ty)] S.subst
  have h_id_new_ty : Subst.freeVars [[(id, new_ty)]] = new_ty.freeVars := by
    simp [Subst.freeVars, Maps.values, Map.values]
  rw [h_id_new_ty] at hsubset
  have h_i_not_in_new_ty : i ∉ new_ty.freeVars := by
    simp at h1
    apply @h1 i hi
  have h_i_not_in_S_values : i ∉ S.subst.freeVars := by
    have h := S.isWF
    simp [SubstWF] at h
    apply @h i hi
  have h_i_not_in_union : i ∉ new_ty.freeVars ++ S.subst.freeVars := by
   exact List.not_mem_append h_i_not_in_new_ty h_i_not_in_S_values
  subst new_ty
  exact fun a => h_i_not_in_union (hsubset a)
  done

theorem SubstWF_mk_insert
    (h_s_not_in_S_values : i ∉ S.freeVars)
    (h_s_not_in_S_keys : S.keys.all (fun k => k ∉ ty.freeVars))
    (h_s_WF : SubstWF [[(i, ty)]])
    (h_S_WF : SubstWF S) :
    SubstWF (Maps.insert S i ty) := by
  simp_all [SubstWF, Maps.values, Maps.keys, Map.values, Map.keys, Subst.freeVars]
  intro x h_x_keys xty h_ty_values
  have h_insert_keys := @Maps.insert_keys_subset _ _ i ty _ S
  have h_insert_values := @Maps.insert_values_subset _ _ i ty _ S
  grind
  done

theorem SubstWF.cons_of_subst_apply (S : SubstInfo) (id : TyIdentifier) (ty newty : LMonoTy)
    (h_newty : newty = LMonoTy.subst S.subst ty)
    (h_id_newty_WF : SubstWF [[(id, newty)]])
    (h_subst_apply_WF : SubstWF (Subst.apply [(id, newty)] S.subst)) :
    SubstWF (Maps.insert (Subst.apply [(id, newty)] S.subst) id newty) := by
  have h_id_not_in_apply : id ∉ (Subst.apply [(id, newty)] S.subst).freeVars := by
    simp_all
    have := @Subst.keys_not_in_apply [(id, newty)] S.subst
    simp_all [Map.keys]
  have h : (∀ (x : TyIdentifier), x ∈ Maps.keys S.subst → ¬x ∈ newty.freeVars) := by
    have := @LMonoTy.subst_keys_not_in_substituted_type S.subst ty S.isWF
    simp [h_newty]; simp_all
  have h_insert := @SubstWF_mk_insert id newty (Subst.apply [(id, newty)] S.subst)
  simp_all
  done

/--
Apply substitution `S` to the free type variables in `ty`.
-/
def LTy.subst (S : Subst) (ty : LTy) : LTy :=
  match ty with
  | .forAll xs ty =>
    let S' := go xs S
    .forAll xs (LMonoTy.subst S' ty)
  where go xs S :=
  match xs with
  | [] => S | x :: rest => go rest (S.erase x)

/--
Open `ty` by instantiating the bound type variable `x` with `xty`.
Note: there is function LTy.close in LTy.lean. LTy.open is located in
this file because it uses LMonoTy.subst.
-/
def LTy.open (x : TyIdentifier) (xty : LMonoTy) (ty : LTy) : LTy :=
  match ty with
  | .forAll vars lty =>
    if x ∈ vars then
      let S := [(x, xty)]
      .forAll (vars.removeAll [x]) (LMonoTy.subst [S] lty)
    else
      ty

/--
Open `ty` by instantiating all its bound variables with `tys`, giving the
`LMonoTy` that results. `tys` should have length equal to the number of bound
variables in `ty`.
-/
def LTy.openFull (ty: LTy) (tys: List LMonoTy) : LMonoTy :=
  LMonoTy.subst [(List.zip (LTy.boundVars ty) tys)] (LTy.toMonoTypeUnsafe ty)

---------------------------------------------------------------------

/-! ### Substitution Properties -/

/--
Substitution on `LMonoTy.bool` is the identity (ground type).
-/
theorem LMonoTy.subst_bool (S : Subst) : LMonoTy.subst S LMonoTy.bool = LMonoTy.bool := by
  simp [LMonoTy.bool, LMonoTy.subst]
  intro h
  simp [LMonoTys.subst, h, LMonoTys.subst.substAux]

/-- Substitution distributes over a 2-element `tcons`, giving component-wise results. -/
theorem LMonoTy.subst_tcons_pair (S : Subst) (name : String) (a b : LMonoTy) :
    LMonoTy.subst S (.tcons name [a, b]) = .tcons name [LMonoTy.subst S a, LMonoTy.subst S b] := by
  rw [LMonoTy.subst_tcons]
  congr 1
  rw [LMonoTys.subst_eq_substLogic]
  by_cases hS : Subst.hasEmptyScopes S
  · simp [LMonoTys.substLogic, hS]
    exact ⟨(LMonoTy.subst_emptyS hS).symm, (LMonoTy.subst_emptyS hS).symm⟩
  · have hS_ne : Subst.hasEmptyScopes S = false := by
      revert hS; cases Subst.hasEmptyScopes S <;> simp
    simp [LMonoTys.substLogic, hS_ne]

/-- If no key of `S` appears in `freeVars(mty)`, then `subst S mty = mty`. -/
theorem LMonoTy.subst_no_relevant_keys (S : Subst) (mty : LMonoTy)
    (h : ∀ x, x ∈ LMonoTy.freeVars mty → x ∉ Maps.keys S) :
    LMonoTy.subst S mty = mty := by
  by_cases hS : Subst.hasEmptyScopes S
  · exact LMonoTy.subst_emptyS hS
  · induction mty with
    | ftvar x =>
      simp [LMonoTy.subst, hS]
      rw [Maps.not_mem_keys_find?_none' S x (h x (by simp [LMonoTy.freeVars]))]
    | bitvec n => simp [LMonoTy.subst]
    | tcons name args ih =>
      simp [LMonoTy.subst, LMonoTys.subst_eq_substLogic, hS]
      induction args with
      | nil => simp [LMonoTys.substLogic, hS]
      | cons a rest ih_rest =>
        simp [LMonoTys.substLogic, hS]
        exact ⟨ih a (List.mem_cons.mpr (Or.inl rfl))
                 (fun x hx => h x (by simp [LMonoTy.freeVars, LMonoTys.freeVars]; left; exact hx)),
               ih_rest (fun b hb => ih b (List.mem_cons.mpr (Or.inr hb)))
                 (fun x hx => h x (by simp [LMonoTy.freeVars, LMonoTys.freeVars]; right; exact hx))⟩

/-- Extensionality for `LMonoTy.subst`: if two substitutions agree on all
    free variables of `mty`, they produce the same result. -/
theorem LMonoTy.subst_ext (S1 S2 : Subst) (mty : LMonoTy)
    (h : ∀ x, x ∈ LMonoTy.freeVars mty → Maps.find? S1 x = Maps.find? S2 x) :
    LMonoTy.subst S1 mty = LMonoTy.subst S2 mty := by
  by_cases hS1 : Subst.hasEmptyScopes S1 <;> by_cases hS2 : Subst.hasEmptyScopes S2
  · -- Both empty scopes: both are identity
    rw [LMonoTy.subst_emptyS hS1, LMonoTy.subst_emptyS hS2]
  · -- S1 empty, S2 not: S1 is identity, show S2 is also identity on mty
    rw [LMonoTy.subst_emptyS hS1]
    symm; apply LMonoTy.subst_no_relevant_keys
    intro x hx
    have h_keys_nil := Subst.isEmpty_implies_keys_empty hS1
    have h_find_none : Maps.find? S1 x = none :=
      Maps.not_mem_keys_find?_none' S1 x (by rw [h_keys_nil]; simp)
    have := h x hx; rw [h_find_none] at this
    exact Maps.find?_of_not_mem_values S2 this.symm
  · -- S1 not empty, S2 empty: symmetric
    rw [LMonoTy.subst_emptyS hS2]
    apply LMonoTy.subst_no_relevant_keys
    intro x hx
    have h_keys_nil := Subst.isEmpty_implies_keys_empty hS2
    have h_find_none : Maps.find? S2 x = none :=
      Maps.not_mem_keys_find?_none' S2 x (by rw [h_keys_nil]; simp)
    have := h x hx; rw [h_find_none] at this
    exact Maps.find?_of_not_mem_values S1 this
  · -- Neither empty: structural induction
    have hS1' : Subst.hasEmptyScopes S1 = false := by
      revert hS1; cases Subst.hasEmptyScopes S1 <;> simp
    have hS2' : Subst.hasEmptyScopes S2 = false := by
      revert hS2; cases Subst.hasEmptyScopes S2 <;> simp
    induction mty with
    | ftvar x =>
      simp [LMonoTy.subst, hS1', hS2']
      rw [h x (by simp [LMonoTy.freeVars])]
    | bitvec _ => simp [LMonoTy.subst]
    | tcons name args ih =>
      simp only [LMonoTy.subst, hS1', hS2', Bool.false_eq_true, ↓reduceIte]; congr 1
      rw [LMonoTys.subst_eq_substLogic, LMonoTys.subst_eq_substLogic]
      induction args with
      | nil => simp [LMonoTys.substLogic, hS1', hS2']
      | cons a rest ih_rest =>
        simp only [LMonoTys.substLogic, hS1', hS2', Bool.false_eq_true, ↓reduceIte]; congr 1
        · exact ih a (List.mem_cons.mpr (Or.inl rfl))
            (fun x hx => h x (by simp [LMonoTy.freeVars, LMonoTys.freeVars]; left; exact hx))
        · exact ih_rest (fun m hm => ih m (List.mem_cons.mpr (Or.inr hm)))
            (fun x hx => h x (by simp [LMonoTy.freeVars, LMonoTys.freeVars]; right; exact hx))

/--
If `t` is a value in a well-formed substitution `S` (i.e., `Maps.find? S a = some t`),
then `subst S t = t`. This is because `SubstWF` guarantees no key of `S` appears
in the free variables of any value in `S`.
-/
theorem LMonoTy.subst_idempotent_value (S : Subst) (a : TyIdentifier) (t : LMonoTy)
    (h_find : Maps.find? S a = some t) (h_wf : SubstWF S) :
    LMonoTy.subst S t = t := by
  apply LMonoTy.subst_no_relevant_keys
  intro x hx
  have h_x_in_fvs : x ∈ Subst.freeVars S := Subst.freeVars_of_find_subset S h_find hx
  simp [SubstWF] at h_wf
  intro h_x_key
  exact h_wf x h_x_key h_x_in_fvs

/--
If no key of a substitution `S` appears free in `ty`, then applying `S` to
`ty` leaves it unchanged. This is the key lemma for proving idempotence.
-/
theorem LMonoTy.subst_no_key_free (S : Subst) (ty : LMonoTy)
    (h : S.keys.all (fun k => k ∉ ty.freeVars)) :
    LMonoTy.subst S ty = ty := by
  apply subst_no_relevant_keys
  grind

/--
Well-formed substitutions are idempotent: applying the substitution twice
gives the same result as applying it once. Follows from `subst_no_key_free`
and `subst_keys_not_in_substituted_type`.
-/
theorem LMonoTy.subst_idempotent (S : Subst) (hWF : SubstWF S) (ty : LMonoTy) :
    LMonoTy.subst S (LMonoTy.subst S ty) = LMonoTy.subst S ty := by
  exact LMonoTy.subst_no_key_free S (LMonoTy.subst S ty)
    (LMonoTy.subst_keys_not_in_substituted_type hWF)

---------------------------------------------------------------------

/-! ### Type Constraints -/

/--
A type constraint `(ty1, ty2)` that records that `ty1` and `ty2` must
have a common substitution instance.
-/
@[expose] abbrev Constraint := (LMonoTy × LMonoTy)
/--
A list of type constraints. These should really be viewed as a set.
-/
@[expose] abbrev Constraints := List Constraint

/--
Get the free type variables in the type constraint `c`.
-/
def Constraint.freeVars (c : Constraint) : List TyIdentifier :=
  let (t1, t2) := c
  LMonoTy.freeVars t1 ++ LMonoTy.freeVars t2

/--
Get the free type variables in type constraints `cs`.
-/
def Constraints.freeVars (cs : Constraints) : List TyIdentifier :=
  match cs with
  | [] => []
  | c :: c_rest =>
    c.freeVars ++ Constraints.freeVars c_rest

theorem Constraints.freeVars_length_cons :
    (freeVars cs).length < (freeVars (c :: cs)).length ∨
    (freeVars cs).length = (freeVars (c :: cs)).length := by
  simp [freeVars, Constraint.freeVars]
  omega

theorem Constraints.freeVars_single_constraint_comm_subset :
    Constraints.freeVars [(t1, t2)] ⊆ Constraints.freeVars [(t2, t1)] := by
  simp [Constraints.freeVars, Constraint.freeVars]

@[simp]
theorem Constraints.freeVars_of_cons_zip :
    Constraints.freeVars ((a :: as).zip (b :: bs)) =
    LMonoTy.freeVars a ++ LMonoTy.freeVars b ++ Constraints.freeVars (as.zip bs) := by
  simp [Constraints.freeVars, Constraint.freeVars]

theorem Constraints.freeVars_of_zip_subset :
    (Constraints.freeVars (args1.zip args2)) ⊆
    (LMonoTys.freeVars args1 ++ LMonoTys.freeVars args2) := by
  induction args1 generalizing args2 with
  | nil => simp_all [freeVars]
  | cons head tail ih =>
    unfold List.zip List.zipWith
    split
    · rename_i xs ys xs' y ys' heq
      simp_all [freeVars]
      obtain ⟨heq1, heq2⟩ := heq
      subst ys xs'
      apply And.intro
      · simp [Constraint.freeVars, Constraint.freeVars]
        simp_all (config := {maxDischargeDepth := 10})
      · have ih' := @ih ys'
        unfold List.zip at ih'
        apply List.subset_append_of_subset_right head.freeVars
        generalize LMonoTys.freeVars tail = A at *
        generalize y.freeVars = B at *
        generalize LMonoTys.freeVars ys' = C at *
        have : A ++ C ⊆ A ++ (B ++ C) := by simp_all
        exact fun _ x => this (ih' x)
    · simp_all [freeVars]
  done

theorem Constraints.freeVars_of_zip_superset (h : args1.length = args2.length) :
    (LMonoTys.freeVars args1 ++ LMonoTys.freeVars args2) ⊆
    (Constraints.freeVars (args1.zip args2)) := by
  induction args1 generalizing args2 with
  | nil =>
    simp_all [freeVars, LMonoTys.freeVars]
    have : args2 = [] := by exact List.length_eq_zero_iff.mp (id (Eq.symm h))
    simp_all [LMonoTys.freeVars]
  | cons head tail ih =>
    cases args2
    case cons.nil =>
      simp_all
    case cons.cons x xs =>
      have ih' := @ih xs (by simp_all)
      simp only [LMonoTys.freeVars_of_cons, Constraints.freeVars_of_cons_zip]
      -- We give Lean permission to do increased backchaining to allow automatic
      -- application of lemmas like
      -- `List.subset_append_of_subset_left` and
      -- `List.subset_append_of_subset_right`,
      simp_all (config := {maxDischargeDepth := 10})
    done

theorem Constraints.freeVars_zip_dedup_length (h : args1.length = args2.length) :
  (Constraints.freeVars (args1.zip args2)).dedup.length =
  (LMonoTys.freeVars args1 ++ LMonoTys.freeVars args2).dedup.length := by
  have h1 := @Constraints.freeVars_of_zip_superset args1 args2 h
  have h2 := @Constraints.freeVars_of_zip_subset args1 args2
  have h3 := @List.length_dedup_subset_eq _ _
              (args1.freeVars ++ args2.freeVars) (freeVars (List.zip args1 args2)) h1 h2
  exact id (Eq.symm h3)

/--
The size of a constraint, useful for termination arguments.
-/
def Constraint.size (c : Constraint) : Nat :=
  c.fst.size + c.snd.size

@[simp]
theorem Constraint.size_gt_zero : 0 < Constraint.size c := by
  simp_all [Constraint.size]
  have := @LMonoTy.size_gt_zero c.fst
  omega

/--
The size of a set of constraint, where each constituent type is sized as a tree.
-/
def Constraints.size (cs : Constraints) : Nat :=
  match cs with
  | [] => 0
  | c :: rest => c.size + Constraints.size rest

@[simp]
theorem Constraints.size_cons :
    Constraints.size rest < Constraints.size (c :: rest) := by
  simp [Constraints.size, Constraint.size]
  have := @LMonoTy.size_gt_zero c.fst
  have := @LMonoTy.size_gt_zero c.snd
  omega

@[simp]
theorem Constraints.size_append :
    Constraints.size (xs ++ ys) = Constraints.size xs + Constraints.size ys := by
  induction xs
  case nil => simp_all [size]
  case cons x xs ih =>
    simp_all [size]; omega

theorem Constraints.size_zip_eq (h : args1.length = args2.length) :
    Constraints.size (args1.zip args2) = LMonoTys.size args1 + LMonoTys.size args2 := by
  induction args1 generalizing args2
  case nil =>
    simp_all [size, LMonoTys.size]
    have : args2 = [] := by exact List.length_eq_zero_iff.mp (id (Eq.symm h))
    simp_all [LMonoTys.size]
  case cons head tail ih =>
    cases args2
    case nil => simp_all
    case cons x xs =>
      simp_all [size, Constraint.size, LMonoTys.size]
      omega

/--
Apply substitution `S` to type constraints `cs`.
-/
def Constraints.subst (S : Subst) (cs : Constraints) : Constraints :=
  match cs with
  | [] => []
  | (lty1, lty2) :: rest =>
    (LMonoTy.subst S lty1, LMonoTy.subst S lty2) ::
    Constraints.subst S rest

@[simp]
theorem Constraints.subst.length_same : (Constraints.subst S cs).length = cs.length := by
  induction cs <;> simp_all [subst]

---------------------------------------------------------------------

/-! ### Type Unification -/

/--
Function encoding the property that the free variables in a substitution `newS`
are a subset of those in constraints `cs` and substitution `oldS`.
-/
def Subst.freeVars_subset_prop (cs : Constraints) (newS oldS : SubstInfo) : Prop :=
  Subst.freeVars newS.subst ⊆
  Constraints.freeVars cs ++ Subst.freeVars oldS.subst

/--
The free variables in a well-formed type substitution (i.e., `newS.subst` and
`newS.isWF`) are bounded by those in the type constraints `cs` and in the old
substitution `oldS`.
-/
structure ValidSubstRelation (cs : Constraints) (oldS : SubstInfo) where
  newS : SubstInfo
  goodSubset : Subst.freeVars_subset_prop cs newS oldS

@[simp]
theorem Subst.freeVars_subset_prop_of_empty (S : SubstInfo) :
    Subst.freeVars_subset_prop [] S S := by
  simp [Subst.freeVars_subset_prop]

theorem Subst.freeVars_subset_prop_single_constraint_comm :
    Subst.freeVars_subset_prop [(t1, t2)] newS oldS =
    Subst.freeVars_subset_prop [(t2, t1)] newS oldS := by
  simp [Subst.freeVars_subset_prop, Constraints.freeVars, Constraint.freeVars]
  apply Iff.intro
  · intro h
    have : t1.freeVars ++ (t2.freeVars ++ oldS.subst.freeVars) ⊆
           t2.freeVars ++ (t1.freeVars ++ oldS.subst.freeVars) := by
      simp_all
    exact fun _ x => this (h x)
  · intro h
    have : t2.freeVars ++ (t1.freeVars ++ oldS.subst.freeVars) ⊆
           t1.freeVars ++ (t2.freeVars ++ oldS.subst.freeVars) := by
      simp_all
    exact fun _ x => this (h x)
  done

private theorem Subst.freeVars_subset_prop_mk_cons
    (R1 : ValidSubstRelation [c] S)
    (R2 : ValidSubstRelation c_rest R1.newS) :
    Subst.freeVars_subset_prop (c :: c_rest) R2.newS S := by
  obtain ⟨h_si_1, h_prop_1⟩ := R1
  obtain ⟨h_si_2, h_prop_2⟩ := R2
  simp [Subst.freeVars_subset_prop] at h_prop_1 h_prop_2 ⊢
  simp_all [Constraints.freeVars, Constraint.freeVars]
  generalize (h_si_1.subst.freeVars) = A at *
  generalize (h_si_2.subst.freeVars) = B at *
  generalize (S.subst.freeVars) = C at *
  generalize c.fst.freeVars = D at *
  generalize c.snd.freeVars = E at *
  generalize c_rest.freeVars = F at *
  have : F ++ A ⊆ D ++ (E ++ (F ++ C)) := by
    simp_all (config := {maxDischargeDepth := 1000})
    have : D ++ (E ++ C) ⊆ D ++ (E ++ (F ++ C)) := by
      simp_all (config := {maxDischargeDepth := 1000})
    exact fun _ x => this (h_prop_1 x)
  exact fun _ x => this (h_prop_2 x)
  done

private theorem ugly_subset_lemma {α : Type} [DecidableEq α]
    (newS oldS sty lty orig_lty : List α)
    (h1 : newS ⊆ sty ++ (lty ++ oldS))
    (h2 : sty ⊆ oldS)
    (h3 : lty ⊆ orig_lty ++ oldS) :
    newS ⊆ orig_lty ++ oldS := by
  have h1' : newS ⊆ sty ++ lty ++ oldS := by simp_all
  clear h1
  have h2 : sty ++ lty ++ oldS ⊆ (lty ++ oldS) := by
    simp_all
  have h3 : newS ⊆ (lty ++ oldS) := by
    exact fun _ a_1 => h2 (h1' a_1)
  have h4 : lty ++ oldS ⊆ orig_lty ++ oldS := by
    simp_all
  exact fun _ a_1 => h4 (h3 a_1)
  done

theorem Subst.freeVars_subset_prop_of_ftvar_id_when_id_in_S (S : SubstInfo) (id : TyIdentifier)
    (orig_lty sty lty : LMonoTy)
    (h_lty : lty = LMonoTy.subst S.subst orig_lty)
    (_h4 : ¬id ∈ lty.freeVars)
    (_h5 : Maps.find? S.subst id = some sty)
    (relS : ValidSubstRelation [(sty, lty)] S) :
    Subst.freeVars_subset_prop [(LMonoTy.ftvar id, orig_lty)] relS.newS S := by
  obtain ⟨newS, h_newS_subset⟩ := relS
  simp [h_lty, Subst.freeVars_subset_prop, Constraints.freeVars, Constraint.freeVars]
    at h_newS_subset ⊢
  have h_sty := @Subst.freeVars_of_find_subset id sty S.subst _h5
  have h_lty := @LMonoTy.freeVars_of_subst_subset S.subst orig_lty
  apply List.subset_append_of_subset_right (LMonoTy.ftvar id).freeVars
  simp_all
  generalize Subst.freeVars newS.subst = newS at *
  generalize Subst.freeVars S.subst = oldS at *
  have := @ugly_subset_lemma _ _ newS oldS sty.freeVars lty.freeVars orig_lty.freeVars
  simp [*] at this
  assumption
  done

theorem Subst.freeVars_of_insert (S : Subst) (id : TyIdentifier) (ty : LMonoTy) :
  Subst.freeVars (Maps.insert S id ty) ⊆ Subst.freeVars S ++ LMonoTy.freeVars ty := by
  have h_insert_vals := @Maps.insert_values_subset _ _ id ty _ S
  simp [freeVars]
  grind
  done

theorem Subst.freeVars_subset_prop_of_single_constraint
    (S newS : SubstInfo) (new_subst : Subst) (id : TyIdentifier) (orig_lty lty : LMonoTy)
    (h_lty : lty = LMonoTy.subst S.subst orig_lty)
    (h_new_subst : new_subst = Maps.insert (Subst.apply [(id, lty)] S.subst) id lty)
    (h' : SubstWF new_subst)
    (h_newS : newS = { subst := new_subst, isWF := h' }) :
    Subst.freeVars_subset_prop [(LMonoTy.ftvar id, orig_lty)] newS S := by
  simp_all [Subst.freeVars_subset_prop]
  simp [Constraints.freeVars]
  have h_orig_lty_subset := @LMonoTy.freeVars_of_subst_subset S.subst orig_lty
  have h_subset := @Subst.freeVars_of_apply_subset_alt
                 [(id, LMonoTy.subst S.subst orig_lty)] S.subst
  have h_freevars := @Subst.freeVars_of_insert (apply [(id, LMonoTy.subst S.subst orig_lty)] S.subst)
                      id (LMonoTy.subst S.subst orig_lty)
  simp [Constraint.freeVars, LMonoTy.freeVars]
  apply List.subset_cons_of_subset id
  conv at h_subset => rhs; lhs; simp [freeVars, Maps.values, Map.values]
  grind
  done

theorem Subst.freeVars_subset_prop_of_tcons (S : SubstInfo)
    (name1 name2 : String) (args1 args2 : List LMonoTy)
    (h_new_constraints : new_constraints = args1.zip args2)
    (relS : ValidSubstRelation new_constraints S)  :
    Subst.freeVars_subset_prop
      [(LMonoTy.tcons name1 args1, LMonoTy.tcons name2 args2)] relS.newS S := by
  obtain ⟨newS, h_newS_subset⟩ := relS
  simp [Subst.freeVars_subset_prop, h_new_constraints] at h_newS_subset
  simp_all [Subst.freeVars_subset_prop, Constraints.freeVars]
  have h := @Constraints.freeVars_of_zip_subset args1 args2
  simp [Constraint.freeVars, LMonoTy.freeVars]
  have : LMonoTys.freeVars args1 ++ (LMonoTys.freeVars args2 ++ (Subst.freeVars S.subst)) =
         LMonoTys.freeVars args1 ++  LMonoTys.freeVars args2 ++ (Subst.freeVars S.subst) := by
    simp_all
  rw [this]; clear this
  generalize List.flatMap LMonoTy.freeVars (Maps.values newS.subst) = A at *
  generalize Constraints.freeVars (args1.zip args2) = B at *
  generalize LMonoTys.freeVars args1 ++ LMonoTys.freeVars args2 = C at *
  generalize Subst.freeVars S.subst = D at *
  have : B ++ D ⊆ C ++ D := by simp_all
  exact fun _ x => this (h_newS_subset x)

private theorem Constraint.unify_termination_goal_1
    (S : SubstInfo) (id : TyIdentifier)
    (orig_lty lty sty : LMonoTy)
    (h_lty : lty = LMonoTy.subst S.subst orig_lty)
    (_h4 : ¬id ∈ lty.freeVars)
    (_h5 : Maps.find? S.subst id = some sty) :
    (Constraints.freeVars [(sty, LMonoTy.subst S.subst orig_lty)] ++ S.subst.freeVars).dedup.length <
    (Constraints.freeVars [(LMonoTy.ftvar id, orig_lty)] ++ S.subst.freeVars).dedup.length ∨
    (Constraints.freeVars [(sty, LMonoTy.subst S.subst orig_lty)] ++ S.subst.freeVars).dedup.length =
    (Constraints.freeVars [(LMonoTy.ftvar id, orig_lty)] ++ S.subst.freeVars).dedup.length ∧
    Constraints.size [(sty, LMonoTy.subst S.subst orig_lty)] <
    Constraints.size [(LMonoTy.ftvar id, orig_lty)] := by
  have h_sty := @Subst.freeVars_of_find_subset id sty S.subst _h5
  have h_subst_orig_lty := @LMonoTy.freeVars_of_subst_subset S.subst orig_lty
  have h_subset :
        (id :: (sty.freeVars ++
               ((LMonoTy.subst S.subst orig_lty).freeVars ++ S.subst.freeVars))) ⊆
        (id :: (orig_lty.freeVars ++ S.subst.freeVars)) := by
    simp_all
  generalize h_l1 : (sty.freeVars ++
                      ((LMonoTy.subst S.subst orig_lty).freeVars ++ S.subst.freeVars)) = l1 at *
  generalize h_l2 : (orig_lty.freeVars ++ S.subst.freeVars) = l2 at *
  have h_subset_right := @List.length_dedup_append_subset_right _ _ (id :: l1) (id :: l2) h_subset
  have h_len := @List.length_dedup_append_le_left _ _ (id :: l1) (id :: l2)
  have h_id : id ∉ l1 := by
    subst l1; simp_all
    have h_S_ok := S.isWF
    simp [SubstWF] at h_S_ok
    apply And.intro
    · have h_sty_values := @Maps.find?_mem_values _ _ id sty _ S.subst _h5
      have h_id_keys := @Maps.find?_mem_keys _ _ id sty _ S.subst _h5
      exact fun a => h_S_ok id h_id_keys (h_sty a)
    · have h_id_keys := @Maps.find?_mem_keys _ _ id sty _ S.subst _h5
      exact h_S_ok id h_id_keys
  have h_dedup1 := @List.length_dedup_cons_of_not_mem _ _ id l1 h_id
  simp_all
  simp [Constraints.freeVars, Constraint.freeVars, LMonoTy.freeVars, h_l1, h_l2]
  omega
  done

-- This theorem follows from `Constraints.unify_termination_goal_1`, but also
-- requires the proof that
-- `Constraints.size [(t1, t2)] == Constraints.size [(t2, t1)]`
-- and similarly, `Constraints.freeVars_single_constraint_comm_subset`.
private theorem Constraint.unify_termination_goal_2
    (S : SubstInfo) (id : TyIdentifier)
    (orig_lty lty sty : LMonoTy)
    (h_lty : lty = LMonoTy.subst S.subst orig_lty)
    (_h4 : ¬id ∈ lty.freeVars)
    (_h5 : Maps.find? S.subst id = some sty) :
    (Constraints.freeVars [(sty, LMonoTy.subst S.subst orig_lty)] ++ S.subst.freeVars).dedup.length <
    (Constraints.freeVars [(orig_lty, LMonoTy.ftvar id)] ++ S.subst.freeVars).dedup.length ∨
    (Constraints.freeVars [(sty, LMonoTy.subst S.subst orig_lty)] ++ S.subst.freeVars).dedup.length =
    (Constraints.freeVars [(orig_lty, LMonoTy.ftvar id)] ++ S.subst.freeVars).dedup.length ∧
    Constraints.size [(sty, LMonoTy.subst S.subst orig_lty)] <
    Constraints.size [(orig_lty, LMonoTy.ftvar id)] := by
  have h1 := @Constraints.freeVars_single_constraint_comm_subset orig_lty (LMonoTy.ftvar id)
  have h2 := @Constraints.freeVars_single_constraint_comm_subset (LMonoTy.ftvar id) orig_lty
  have h3 := @Constraint.unify_termination_goal_1 S id orig_lty lty sty h_lty _h4 _h5
  generalize Constraints.freeVars [(orig_lty, LMonoTy.ftvar id)] = A at *
  generalize Constraints.freeVars [(LMonoTy.ftvar id, orig_lty)] = B at *
  generalize Constraints.freeVars [(sty, LMonoTy.subst S.subst orig_lty)] = X at *
  generalize S.subst.freeVars = Y at *
  simp_all [Constraints.size, Constraint.size]
  have h_sub1 : A ++ Y ⊆ B ++ Y := by simp_all
  have h_sub2 : B ++ Y ⊆ A ++ Y := by simp_all
  have h_sub : (B ++ Y).dedup.length = (A ++ Y).dedup.length := by
    exact List.length_dedup_subset_eq (B ++ Y) (A ++ Y) h_sub2 h_sub1
  simp_all
  omega
  done

private theorem Constraint.unify_termination_goal_3
    (S : SubstInfo) (name1 name2 : String) (args1 args2 : List LMonoTy)
    (h_tcons : name1 = name2 ∧ args1.length = args2.length) :
    (Constraints.freeVars (args1.zip args2) ++ S.subst.freeVars).dedup.length <
    (Constraints.freeVars [(LMonoTy.tcons name2 args1, LMonoTy.tcons name2 args2)] ++
     S.subst.freeVars).dedup.length ∨
    (Constraints.freeVars (args1.zip args2) ++ S.subst.freeVars).dedup.length =
    (Constraints.freeVars [(LMonoTy.tcons name2 args1, LMonoTy.tcons name2 args2)] ++
     S.subst.freeVars).dedup.length ∧
    Constraints.size (args1.zip args2) <
    Constraints.size [(LMonoTy.tcons name2 args1, LMonoTy.tcons name2 args2)] := by
  have h_zip_fvs_super := @Constraints.freeVars_of_zip_superset args1 args2 h_tcons.right
  have h_zip_fvs_sub := @Constraints.freeVars_of_zip_subset args1 args2
  have h_zip_size := @Constraints.size_zip_eq args1 args2 h_tcons.right
  have h_fvs_tcons :
    Constraints.freeVars [(LMonoTy.tcons name2 args1, LMonoTy.tcons name2 args2)] =
    LMonoTys.freeVars args1 ++ LMonoTys.freeVars args2 := by
    simp [Constraints.freeVars, Constraint.freeVars, LMonoTy.freeVars]
  have h_size_tcons :
    Constraints.size [(LMonoTy.tcons name2 args1, LMonoTy.tcons name2 args2)] =
    1 + LMonoTys.size args1 + (1 + LMonoTys.size args2) := by
    simp_all [Constraints.size, Constraint.size, LMonoTy.size]
  simp_all
  clear h_size_tcons h_zip_size h_tcons h_fvs_tcons
  generalize Constraints.freeVars (args1.zip args2) = A at *
  generalize LMonoTys.freeVars args1 = B1 at *
  generalize LMonoTys.freeVars args2 = B2 at *
  generalize S.subst.freeVars = C at *
  have h1 : (A ++ C) ⊆ (B1 ++ (B2 ++ C)) := by
    simp_all
    have : B1 ++ B2 ⊆ B1 ++ (B2 ++ C) := by simp_all
    exact fun _ x => this (h_zip_fvs_sub x)
  have h2 : (B1 ++ (B2 ++ C)) ⊆ (A ++ C) := by
    simp_all
  have h_len_eq := @List.length_dedup_subset_eq _ _
                   (A ++ C) (B1 ++ (B2 ++ C)) h1 h2
  omega
  done

private theorem Constraints.unify_termination_goal_1
    (cs : Constraints) (c : Constraint) (S : SubstInfo) :
    (Constraints.freeVars [c] ++ S.subst.freeVars).dedup.length <
      (Constraints.freeVars (c :: cs) ++ S.subst.freeVars).dedup.length ∨
    (Constraints.freeVars [c] ++ S.subst.freeVars).dedup.length =
        (Constraints.freeVars (c :: cs) ++ S.subst.freeVars).dedup.length ∧
    (Constraints.size [c] < Constraints.size (c :: cs) ∨
     Constraints.size [c] = Constraints.size (c :: cs)) := by
  simp_all [Constraints.freeVars, Constraints.size]
  have h_sub : (c.freeVars ++ S.subst.freeVars) ⊆
               (c.freeVars ++ (cs.freeVars ++ S.subst.freeVars)) := by
    simp_all
  generalize (c.freeVars ++ S.subst.freeVars) = l1 at *
  generalize (c.freeVars ++ (cs.freeVars ++ S.subst.freeVars)) = l2 at *
  have h1 : (l1.dedup.length < l2.dedup.length) ∨ (l1.dedup.length = l2.dedup.length) := by
    have := @List.length_dedup_of_subset_le _ _ l1 l2 h_sub
    exact Or.symm (Nat.eq_or_lt_of_le this)
  cases h1 <;> try simp_all
  exact Or.symm (Nat.eq_zero_or_pos (Constraints.size cs))
  done

private theorem Constraints.unify_termination_goal_2
    (cs : Constraints) (c : Constraint) (S : SubstInfo)
    (relS : ValidSubstRelation [c] S) :
    (Constraints.freeVars cs ++ relS.newS.subst.freeVars).dedup.length <
    (Constraints.freeVars (c :: cs) ++ S.subst.freeVars).dedup.length ∨
    (Constraints.freeVars cs ++ relS.newS.subst.freeVars).dedup.length =
    (Constraints.freeVars (c :: cs) ++ S.subst.freeVars).dedup.length := by
  obtain ⟨newS, h_subset_prop⟩ := relS
  simp [Subst.freeVars_subset_prop, Constraints.freeVars] at h_subset_prop
  simp [Constraints.freeVars] at *
  have h_sub : (cs.freeVars ++ newS.subst.freeVars) ⊆
               (c.freeVars ++ (cs.freeVars ++ S.subst.freeVars)) := by
    simp_all
    generalize newS.subst.freeVars = A at *
    generalize c.freeVars = B at *
    generalize cs.freeVars = C at *
    generalize S.subst.freeVars = D at *
    have : B ++ D ⊆ B ++ (C ++ D) := by simp_all
    exact fun _ x => this (h_subset_prop x)
  have := @List.length_dedup_of_subset_le _ _
            (cs.freeVars ++ newS.subst.freeVars)
            (c.freeVars ++ (cs.freeVars ++ S.subst.freeVars))
            h_sub
  omega
  done

/--
Kinds of errors that can occur during type unification. Also includes the
failing constraint.
-/
inductive UnifyError where
  | ImpossibleToUnify (c : Constraint) (original : Option Constraint := .none)
  | FailedOccursCheck (tyvar : TyIdentifier) (ty : LMonoTy) (c : Constraint) (original : Option Constraint := .none)
  deriving Repr, Inhabited, DecidableEq

def UnifyError.addOriginalConstraint (e : UnifyError) (o : Constraint) : UnifyError :=
  match e with
  | ImpossibleToUnify c _ => ImpossibleToUnify c o
  | FailedOccursCheck tyvar ty c _ => FailedOccursCheck tyvar ty c o

instance : ToFormat UnifyError where
  format u := match u with
    | .ImpossibleToUnify c opt_original =>
      let msg_fn := fun (x : Constraint) => f!"Impossible to unify {x.fst} with {x.snd}."
      match opt_original with
      | none => msg_fn c
      | some original =>
        if c == original then
          msg_fn c
        else
          (msg_fn original) ++ f!"\nFirst mismatch: {c.fst} with {c.snd}."
    | .FailedOccursCheck tyvar ty c opt_original =>
      let msg_fn := f!"Failed occurs check: \
                      {tyvar} cannot be unified with {ty} because it would \
                      create a circular dependency during unification."
        match opt_original with
        | none => msg_fn
        | some original =>
          if original == c then msg_fn
          else msg_fn ++ f!" Failure occurred when unifying {original.fst} with {original.snd}."

mutual
/--
Type unification for a single constraint `c` w.r.t. a well-formed type
substitution `S`. See `Constraints.unify` for the top-level function.
-/
def Constraint.unifyOne (c : Constraint) (S : SubstInfo) :
  Except UnifyError (ValidSubstRelation [c] S) :=
  let (t1, t2) := c
  if _h1: t1 == t2 then
     have h_sub : Subst.freeVars_subset_prop [(t1, t2)] S S := by
      simp [Subst.freeVars_subset_prop]
    .ok { newS := S, goodSubset := h_sub }
  else
    match _h2: t1, t2 with
    | .ftvar id, orig_lty | orig_lty, .ftvar id => do
      -- Unification for variable `id`
      let lty := LMonoTy.subst S.subst orig_lty
      have h_sub1 : Subst.freeVars_subset_prop [(LMonoTy.ftvar id, orig_lty)] S S := by
        simp [Subst.freeVars_subset_prop]
      have h_sub2 : Subst.freeVars_subset_prop [(orig_lty, LMonoTy.ftvar id)] S S := by
        simp [Subst.freeVars_subset_prop]
      if _h3 : (.ftvar id) == lty then
        .ok { newS := S, goodSubset := by all_goals simp [h_sub1, h_sub2] }
      else if _h4 : id ∈ lty.freeVars then
        -- Occurs check: `id` should not appear in the free type variables of
        -- `lty`.
        .error (.FailedOccursCheck id lty (t1, t2))
      else
        -- At this point, `id` cannot be a free variable in `lty`.
        match _h5 : S.subst.find? id with
        | some sty =>
          -- `sty` must unify with `lty`.
          let relS ← Constraint.unifyOne (sty, lty) S
          have h_sub1_new : Subst.freeVars_subset_prop [(LMonoTy.ftvar id, orig_lty)] relS.newS S := by
            exact Subst.freeVars_subset_prop_of_ftvar_id_when_id_in_S
                  S id orig_lty sty lty rfl _h4 _h5 relS
          have h_sub2_new : Subst.freeVars_subset_prop [(orig_lty, LMonoTy.ftvar id)] relS.newS S := by
            simp_all [Subst.freeVars_subset_prop_single_constraint_comm]
          .ok { newS := relS.newS,
                goodSubset := by all_goals simp [h_sub1_new, h_sub2_new] }
        | none =>
          -- `id` must unify with `lty`. We then add `[id ↦ lty]` to the
          -- substitution.
          have h_id_lty_WF : SubstWF [[(id, lty)]] = true := by
            exact SubstWF.single_subst id _h4
          have h_subst_apply_WF :  SubstWF (Subst.apply [(id, lty)] S.subst) := by
            exact SubstWF.apply_one_substituted_type S id orig_lty
          let new_subst := (Subst.apply [(id, lty)] S.subst).insert id lty
          have h' : SubstWF new_subst := by
            exact SubstWF.cons_of_subst_apply S id orig_lty lty rfl h_id_lty_WF h_subst_apply_WF
          let newS := SubstInfo.mk new_subst h'
          have h_sub1 : Subst.freeVars_subset_prop [(LMonoTy.ftvar id, orig_lty)] newS S := by
            exact Subst.freeVars_subset_prop_of_single_constraint S newS new_subst
                   id orig_lty (LMonoTy.subst S.subst orig_lty) rfl rfl h' rfl
          have h_sub2 : Subst.freeVars_subset_prop [(orig_lty, LMonoTy.ftvar id)] newS S := by
            simp_all [Subst.freeVars_subset_prop_single_constraint_comm]
          .ok { newS := newS, goodSubset := by all_goals simp [h_sub1, h_sub2] }
    | .bitvec n1, .bitvec n2 =>
      if _h7 : n1 == n2 then
        .ok { newS := SubstInfo.mk [] (by simp [SubstWF]), goodSubset := by grind }
      else
        .error (.ImpossibleToUnify (t1, t2))
    | .tcons name1 args1, .tcons name2 args2 => do
      if _h6 : name1 == name2 && args1.length == args2.length then
       let new_constraints := List.zip args1 args2
       let relS ← Constraints.unifyCore new_constraints S
       have h_sub : Subst.freeVars_subset_prop
                    [(LMonoTy.tcons name1 args1, LMonoTy.tcons name2 args2)] relS.newS S := by
         exact Subst.freeVars_subset_prop_of_tcons S name1 name2 args1 args2 rfl relS
       .ok { newS := relS.newS, goodSubset := by simp [h_sub] }
      else
        .error (.ImpossibleToUnify (t1, t2))
    | .bitvec _, .tcons _ _ =>
        .error (.ImpossibleToUnify (t1, t2))
    | .tcons _ _, .bitvec _ =>
        .error (.ImpossibleToUnify (t1, t2))
  termination_by ((((Constraints.freeVars [c]) ++ S.subst.freeVars).dedup.length),
                  Constraints.size [c],
                  0)
  decreasing_by
    all_goals simp_all [Prod.lex_def]
    -- Subgoal 1
    · exact @Constraint.unify_termination_goal_1 S id orig_lty lty sty (by exact rfl) _h4 _h5
    -- Subgoal 2
    · exact @Constraint.unify_termination_goal_2 S id orig_lty lty sty (by exact rfl) _h4 _h5
    -- Subgoal 3
    · exact @Constraint.unify_termination_goal_3 S name1 name2 args1 args2 _h6

/--
Type unification for constraints `cs` w.r.t. a well-formed type
substitution `S`. See `Constraints.unify` for the top-level function.
-/
def Constraints.unifyCore (cs : Constraints) (S : SubstInfo) :
    Except UnifyError (ValidSubstRelation cs S) := do
  match _h0 : cs with
  | [] => .ok { newS := S, goodSubset := by simp [Subst.freeVars_subset_prop_of_empty] }
  | c :: c_rest =>
    let relS ← Constraint.unifyOne c S |> .mapError (fun e => UnifyError.addOriginalConstraint e c)
    let new_relS ← Constraints.unifyCore c_rest relS.newS
    .ok { newS := new_relS.newS, goodSubset := by simp [Subst.freeVars_subset_prop_mk_cons] }
  termination_by ((((Constraints.freeVars cs) ++ S.subst.freeVars).dedup.length),
                  Constraints.size cs,
                  1)

  decreasing_by
    all_goals simp_all [Prod.lex_def]
    -- Subgoal 1
    · exact @Constraints.unify_termination_goal_1 c_rest c S
    -- Subgoal 2
    · exact @Constraints.unify_termination_goal_2 c_rest c S relS
end

/--
`Constraints.unify` is Lambda's type unification function, which implements a
bottom-up Hindley-Milner style algorithm that finds the most general type
(principal type) of an expression by finding a substitution that makes all the
types in the input constraints equal.

On failure, returns the constraint that cannot be unified --
note that this can be different from a constraint `c` in `cs` because it could
involve subterms of types in `c` (e.g., `Map int bool` and `Map int int` fail to
unify because `bool` and `int` can't be unified). The constraint returned on
failure would be the _first_ mismatching one, not necessarily the only one.

Returns a well-formed `S` w.r.t. `cs` otherwise.
-/
def Constraints.unify (constraints : Constraints) (S : SubstInfo) :
    Except UnifyError SubstInfo := do
    let relS ← Constraints.unifyCore constraints S
    .ok relS.newS

/-- A key in a well-formed substitution does not appear in its own image. -/
theorem SubstWF.not_mem_freeVars_of_find (S : Subst) (a : TyIdentifier) (t : LMonoTy)
    (h_find : Maps.find? S a = some t) (h_wf : SubstWF S) :
    a ∉ LMonoTy.freeVars t := by
  simp [SubstWF] at h_wf
  have h_key := Maps.find?_mem_keys S h_find
  have h_fv_subset := Subst.freeVars_of_find_subset S h_find
  grind

/-- Absorption for type lists: the single substitution is absorbed element-wise. -/
theorem LMonoTys.subst_absorbs_single (S : Subst) (a : TyIdentifier) (t : LMonoTy)
    (mtys : LMonoTys)
    (hS : Subst.hasEmptyScopes S = false)
    (hSingle : Subst.hasEmptyScopes [[(a, t)]] = false)
    (ih : ∀ m, m ∈ mtys → LMonoTy.subst S (LMonoTy.subst [[(a, t)]] m) = LMonoTy.subst S m) :
    LMonoTys.subst S (LMonoTys.subst [[(a, t)]] mtys) = LMonoTys.subst S mtys := by
  rw [LMonoTys.subst_eq_substLogic, LMonoTys.subst_eq_substLogic, LMonoTys.subst_eq_substLogic]
  induction mtys with
  | nil => simp [LMonoTys.substLogic, hS, hSingle]
  | cons m rest ih_rest =>
    simp only [LMonoTys.substLogic, hS, hSingle, Bool.false_eq_true, ↓reduceIte]
    grind

/--
#### Absorption: relating substitutions produced by successive resolveAux calls

Absorption: `subst S (subst [(a,t)] mty) = subst S mty` when `Maps.find? S a = some t`
and `SubstWF S`. The single-variable substitution `[(a,t)]` is "absorbed" by `S`
because `S` already maps `a` to `t`.
-/
theorem LMonoTy.subst_absorbs_single (S : Subst) (a : TyIdentifier) (t : LMonoTy)
    (mty : LMonoTy) (h_find : Maps.find? S a = some t) (h_wf : SubstWF S) :
    LMonoTy.subst S (LMonoTy.subst [[(a, t)]] mty) = LMonoTy.subst S mty := by
  have hS : Subst.hasEmptyScopes S = false :=
    Subst.hasEmptyScopes_false_of_find S a t h_find
  have hSingle : Subst.hasEmptyScopes [[(a, t)]] = false := by
    simp [Subst.hasEmptyScopes, Map.isEmpty]
  induction mty with
  | ftvar x =>
    by_cases h_eq : a = x
    · -- x = a: inner subst gives t, then subst S t = t = subst S (ftvar a)
      subst h_eq
      have h_inner : LMonoTy.subst [[(a, t)]] (.ftvar a) = t := by
        simp [LMonoTy.subst, Subst.hasEmptyScopes, Map.isEmpty, Maps.find?, Map.find?]
      rw [h_inner]
      simp [LMonoTy.subst, hS, h_find]
      exact LMonoTy.subst_idempotent_value S a t h_find h_wf
    · -- x ≠ a: inner subst is identity
      have h_inner : LMonoTy.subst [[(a, t)]] (.ftvar x) = .ftvar x := by
        simp [LMonoTy.subst, Subst.hasEmptyScopes, Map.isEmpty, Maps.find?, Map.find?, h_eq]
      rw [h_inner]
  | bitvec n =>
    simp [LMonoTy.subst]
  | tcons name args ih =>
    simp only [LMonoTy.subst, hSingle, hS, Bool.false_eq_true, ↓reduceIte]
    congr 1
    exact LMonoTys.subst_absorbs_single S a t args hS hSingle ih

/-!
When `resolveAux` processes subexpressions, each call extends the substitution.
The key property is that later substitutions "absorb" earlier ones: applying the
outer substitution after the inner one is the same as applying the outer alone.

This lets us upgrade typing judgments from an inner substitution to the final one.
-/

/--
`S_outer` absorbs `S_inner` means: for every binding `a ↦ t` in `S_inner`,
`subst S_outer t = subst S_outer (ftvar a)`. In other words, `S_outer` already
"knows about" every binding in `S_inner`.
-/
def Subst.absorbs (S_outer S_inner : Subst) : Prop :=
  ∀ a t, Maps.find? S_inner a = some t →
    LMonoTy.subst S_outer t = LMonoTy.subst S_outer (.ftvar a)

/--
Absorption implies substitution composition collapses:
`subst S_outer (subst S_inner mty) = subst S_outer mty`.
-/
theorem LMonoTy.subst_absorbs (S_outer S_inner : Subst) (mty : LMonoTy)
    (h : Subst.absorbs S_outer S_inner) :
    LMonoTy.subst S_outer (LMonoTy.subst S_inner mty) = LMonoTy.subst S_outer mty := by
  by_cases h_emptyI : Subst.hasEmptyScopes S_inner
  · rw [LMonoTy.subst_emptyS h_emptyI]
  · have hInner : Subst.hasEmptyScopes S_inner = false := by
      revert h_emptyI; cases Subst.hasEmptyScopes S_inner <;> simp
    induction mty with
    | ftvar x =>
      cases h_find : Maps.find? S_inner x with
      | none =>
        have : LMonoTy.subst S_inner (.ftvar x) = .ftvar x := by
          simp [LMonoTy.subst, hInner, h_find]
        rw [this]
      | some t =>
        have : LMonoTy.subst S_inner (.ftvar x) = t := by
          simp [LMonoTy.subst, hInner, h_find]
        rw [this]; exact h x t h_find
    | bitvec n => simp [LMonoTy.subst]
    | tcons name args ih =>
      have h_inner : LMonoTy.subst S_inner (.tcons name args) =
          .tcons name (LMonoTys.subst S_inner args) := by
        unfold LMonoTy.subst; simp only [hInner, Bool.false_eq_true, ↓reduceIte]
      rw [h_inner]
      by_cases h_emptyO : Subst.hasEmptyScopes S_outer
      · rw [LMonoTy.subst_emptyS h_emptyO, LMonoTy.subst_emptyS h_emptyO]
        congr 1
        rw [LMonoTys.subst_eq_substLogic]
        suffices ∀ xs, (∀ m, m ∈ xs → LMonoTy.subst S_inner m = m) →
            LMonoTys.substLogic S_inner xs = xs by
          exact this args (fun m hm => by
            have := ih m hm
            simp only [LMonoTy.subst_emptyS h_emptyO] at this; exact this)
        intro xs; induction xs with
        | nil => intro _; simp [LMonoTys.substLogic, hInner]
        | cons a rest ih_rest =>
          intro ih_cons
          simp only [LMonoTys.substLogic, hInner, Bool.false_eq_true, ↓reduceIte]
          rw [ih_cons a List.mem_cons_self,
              ih_rest (fun m hm => ih_cons m (List.mem_cons_of_mem a hm))]
      · have hOuter : Subst.hasEmptyScopes S_outer = false := by
          revert h_emptyO; cases Subst.hasEmptyScopes S_outer <;> simp
        have h_l : LMonoTy.subst S_outer (.tcons name (LMonoTys.subst S_inner args)) =
            .tcons name (LMonoTys.subst S_outer (LMonoTys.subst S_inner args)) := by
          unfold LMonoTy.subst; simp only [hOuter, Bool.false_eq_true, ↓reduceIte]
        have h_r : LMonoTy.subst S_outer (.tcons name args) =
            .tcons name (LMonoTys.subst S_outer args) := by
          unfold LMonoTy.subst; simp only [hOuter, Bool.false_eq_true, ↓reduceIte]
        rw [h_l, h_r]; congr 1
        rw [LMonoTys.subst_eq_substLogic, LMonoTys.subst_eq_substLogic,
            LMonoTys.subst_eq_substLogic]
        suffices ∀ xs,
            (∀ m, m ∈ xs → LMonoTy.subst S_outer (LMonoTy.subst S_inner m) =
              LMonoTy.subst S_outer m) →
            LMonoTys.substLogic S_outer (LMonoTys.substLogic S_inner xs) =
              LMonoTys.substLogic S_outer xs by
          exact this args (fun m hm => ih m hm)
        intro xs; induction xs with
        | nil => intro _; simp [LMonoTys.substLogic, hOuter, hInner]
        | cons a rest ih_rest =>
          intro ih_cons
          simp only [LMonoTys.substLogic, hOuter, hInner, Bool.false_eq_true, ↓reduceIte]
          rw [ih_cons a List.mem_cons_self,
              ih_rest (fun m hm => ih_cons m (List.mem_cons_of_mem a hm))]

/-- Every well-formed substitution absorbs itself. -/
theorem Subst.absorbs_refl (S : Subst) (h_wf : SubstWF S) :
    Subst.absorbs S S := by
  intro a t h_find
  have h_not_empty := Subst.hasEmptyScopes_false_of_find S a t h_find
  have : LMonoTy.subst S (.ftvar a) = t := by
    simp [LMonoTy.subst, h_not_empty, h_find]
  rw [this]
  exact LMonoTy.subst_idempotent_value S a t h_find h_wf

/-- Absorption is transitive: if `S2` absorbs `S1` and `S3` absorbs `S2`,
    then `S3` absorbs `S1`. -/
theorem Subst.absorbs_trans (S1 S2 S3 : Subst)
    (h12 : Subst.absorbs S2 S1) (h23 : Subst.absorbs S3 S2) :
    Subst.absorbs S3 S1 := by
  intro a t h_find
  have h1 := h12 a t h_find
  rw [← LMonoTy.subst_absorbs S3 S2 t h23, h1,
      LMonoTy.subst_absorbs S3 S2 (.ftvar a) h23]

/--
Composition lemma: applying a singleton substitution `[[(v, t)]]` followed by
`[ys]` equals applying the merged substitution `[(v, t) :: ys]`, provided
`subst [ys] t = t` (i.e., `t` is stable under `ys`).

This is a key lemma for proving that sequential `tinst` applications
(each substituting one bound variable) produce the same result as a
single parallel substitution with all bindings.
-/

theorem LMonoTy.subst_cons_single
    (v : TyIdentifier) (t : LMonoTy) (ys : SubstOne) (mty : LMonoTy)
    (h_t : LMonoTy.subst [ys] t = t) :
    LMonoTy.subst [ys] (LMonoTy.subst [[(v, t)]] mty) =
    LMonoTy.subst [((v, t) :: ys)] mty := by
  have hSingle : Subst.hasEmptyScopes [[(v, t)]] = false := by
    simp [Subst.hasEmptyScopes, Map.isEmpty]
  have hCons : Subst.hasEmptyScopes [((v, t) :: ys)] = false := by
    simp [Subst.hasEmptyScopes, Map.isEmpty]
  by_cases hYs : Subst.hasEmptyScopes [ys]
  · -- ys is empty, so subst [ys] is identity
    have h_ys_empty : ys = [] := by
      simp [Subst.hasEmptyScopes, Map.isEmpty] at hYs
      cases ys with
      | nil => rfl
      | cons _ _ => simp at hYs
    subst h_ys_empty
    simp only [LMonoTy.subst_emptyS hYs]
  · have hYs_ne : Subst.hasEmptyScopes [ys] = false := by
      revert hYs; cases Subst.hasEmptyScopes [ys] <;> simp
    induction mty with
    | ftvar x =>
      by_cases h_eq : v = x
      · -- v = x: inner subst gives t, then subst [ys] t = t by h_t
        subst h_eq
        have h_inner : LMonoTy.subst [[(v, t)]] (.ftvar v) = t := by
          simp [LMonoTy.subst, Subst.hasEmptyScopes, Map.isEmpty, Maps.find?, Map.find?]
        rw [h_inner, h_t]
        -- RHS: subst [(v,t)::ys] (ftvar v) = t (first match in (v,t)::ys)
        simp [LMonoTy.subst, hCons, Maps.find?, Map.find?]
      · -- v ≠ x: inner subst is identity, lookup x in ys
        have h_inner : LMonoTy.subst [[(v, t)]] (.ftvar x) = .ftvar x := by
          simp [LMonoTy.subst, Subst.hasEmptyScopes, Map.isEmpty, Maps.find?, Map.find?, h_eq]
        rw [h_inner]
        -- Both sides look up x in ys (since v ≠ x, (v,t)::ys skips (v,t))
        simp [LMonoTy.subst, hYs_ne, hCons, Maps.find?, Map.find?, h_eq]
    | bitvec n =>
      simp [LMonoTy.subst]
    | tcons name args ih =>
      simp only [LMonoTy.subst, hSingle, hYs_ne, hCons, Bool.false_eq_true, ↓reduceIte]
      congr 1
      rw [LMonoTys.subst_eq_substLogic, LMonoTys.subst_eq_substLogic,
          LMonoTys.subst_eq_substLogic]
      suffices ∀ xs,
          (∀ m, m ∈ xs → LMonoTy.subst [ys] (LMonoTy.subst [[(v, t)]] m) =
            LMonoTy.subst [((v, t) :: ys)] m) →
          LMonoTys.substLogic [ys] (LMonoTys.substLogic [[(v, t)]] xs) =
            LMonoTys.substLogic [((v, t) :: ys)] xs by
        exact this args ih
      intro xs; induction xs with
      | nil => intro _; simp [LMonoTys.substLogic, hSingle, hYs_ne, hCons]
      | cons a rest ih_rest =>
        intro ih_xs
        simp only [LMonoTys.substLogic, hSingle, hYs_ne, hCons, Bool.false_eq_true, ↓reduceIte]
        rw [ih_xs a List.mem_cons_self,
            ih_rest (fun m hm => ih_xs m (List.mem_cons_of_mem a hm))]

-- Helper: applyLogic preserves some bindings.
private theorem Map.find?_applyLogic_some_h' {new old : SubstOne} {a : TyIdentifier} {t : LMonoTy}
    (h : Map.find? old a = some t) :
    Map.find? (SubstOne.applyLogic new old) a = some (LMonoTy.subst [new] t) := by
  induction old with
  | nil => simp [Map.find?] at h
  | cons hd rest ih =>
    simp only [SubstOne.applyLogic, Map.find?]
    simp only [Map.find?] at h
    grind

-- Helper: applyLogic preserves none bindings.
private theorem Map.find?_applyLogic_none_h' {new old : SubstOne} {a : TyIdentifier}
    (h : Map.find? old a = none) :
    Map.find? (SubstOne.applyLogic new old) a = none := by
  induction old with
  | nil => simp [SubstOne.applyLogic, Map.find?]
  | cons hd rest ih =>
    simp [SubstOne.applyLogic, Map.find?]
    simp [Map.find?] at h
    grind

-- Helper: Subst.apply preserves some bindings.
private theorem Maps.find?_apply_some_h' {new : SubstOne} {old : Subst} {a : TyIdentifier} {t : LMonoTy}
    (h : Maps.find? old a = some t) :
    Maps.find? (Subst.apply new old) a = some (LMonoTy.subst [new] t) := by
  induction old with
  | nil => simp [Maps.find?] at h
  | cons m rest ih =>
    simp only [Subst.apply, Maps.find?]
    simp only [Maps.find?] at h
    rw [SubstOne.apply_eq_applyLogic]
    cases h_ma : Map.find? m a with
    | none =>
      rw [h_ma] at h
      rw [Map.find?_applyLogic_none_h' h_ma]
      exact ih h
    | some val =>
      rw [h_ma] at h; simp only [Option.some.injEq] at h; subst h
      rw [Map.find?_applyLogic_some_h' h_ma]

-- Helper: Except.mapError preserves ok values.
private theorem Except.mapError_ok_h' {α β γ : Type} {f : α → β} {e : Except α γ} {v : γ}
    (h : Except.mapError f e = .ok v) : e = .ok v := by
  cases e with
  | error a => simp [Except.mapError] at h
  | ok val => simp [Except.mapError] at h; exact congrArg Except.ok h

-- Helper: insert+apply produces an absorbing substitution.
private theorem absorbs_of_insert_apply_h' (S : SubstInfo) (id : TyIdentifier) (lty : LMonoTy)
    (h_none : Maps.find? S.subst id = none)
    (h_wf : SubstWF ((Subst.apply [(id, lty)] S.subst).insert id lty)) :
    Subst.absorbs ((Subst.apply [(id, lty)] S.subst).insert id lty) S.subst := by
  intro a t h_find
  have h_a_ne_id : a ≠ id := by
    intro h_eq; subst h_eq; rw [h_find] at h_none; simp at h_none
  let S_new := (Subst.apply [(id, lty)] S.subst).insert id lty
  have h_apply_a := Maps.find?_apply_some_h' (new := [(id, lty)]) h_find
  have h_find_new : Maps.find? S_new a = some (LMonoTy.subst [[(id, lty)]] t) := by
    show Maps.find? (Maps.insert _ id lty) a = _
    rw [Maps.find?_insert_ne _ _ _ _ h_a_ne_id]
    exact h_apply_a
  have h_find_id : Maps.find? S_new id = some lty := Maps.find?_insert_self _ id lty
  have h_not_empty := Subst.hasEmptyScopes_false_of_find S_new a _ h_find_new
  have h_subst_ftvar : LMonoTy.subst S_new (.ftvar a) = LMonoTy.subst [[(id, lty)]] t := by
    simp [LMonoTy.subst, h_not_empty, h_find_new]
  have h_idem := LMonoTy.subst_idempotent_value S_new a _ h_find_new h_wf
  have h_abs := LMonoTy.subst_absorbs_single S_new id lty t h_find_id h_wf
  rw [h_subst_ftvar, ← h_abs, h_idem]

/-- After inserting `(id, lty)` into the applied substitution, `subst _ (ftvar id) = lty`. -/
private theorem subst_ftvar_new_binding
    (S : Subst) (id : TyIdentifier) (lty : LMonoTy)
    (_h_none : Maps.find? S id = none) :
    LMonoTy.subst (Maps.insert (Subst.apply [(id, lty)] S) id lty) (LMonoTy.ftvar id) = lty := by
  have h_find := Maps.find?_insert_self (Subst.apply [(id, lty)] S) id lty
  have h_not_empty : ¬Subst.hasEmptyScopes (Maps.insert (Subst.apply [(id, lty)] S) id lty) := by
    intro h_empty
    exact absurd ((Subst.isEmpty_implies_keys_empty h_empty) ▸ Maps.find?_mem_keys _ h_find) (by simp)
  unfold LMonoTy.subst; simp [h_not_empty, h_find]

/-- When `S.find? id = none`, the new substitution absorbs `S` and maps `orig_lty` to `lty`. -/
private theorem subst_orig_new_binding
    (S : Subst) (id : TyIdentifier) (lty orig_lty : LMonoTy)
    (h_none : Maps.find? S id = none)
    (h_lty : lty = LMonoTy.subst S orig_lty)
    (h_occurs : ¬(id ∈ lty.freeVars)) :
    LMonoTy.subst (Maps.insert (Subst.apply [(id, lty)] S) id lty) orig_lty = lty := by
  subst h_lty
  have h_find_S'_id : Maps.find? (Maps.insert (Subst.apply [(id, LMonoTy.subst S orig_lty)] S)
      id (LMonoTy.subst S orig_lty)) id = some (LMonoTy.subst S orig_lty) :=
    Maps.find?_insert_self _ _ _
  have hS' : Subst.hasEmptyScopes (Maps.insert (Subst.apply [(id, LMonoTy.subst S orig_lty)] S)
      id (LMonoTy.subst S orig_lty)) = false :=
    Subst.hasEmptyScopes_false_of_find _ id _ h_find_S'_id
  have h_find_ne : ∀ x, x ≠ id →
      Maps.find? (Maps.insert (Subst.apply [(id, LMonoTy.subst S orig_lty)] S)
        id (LMonoTy.subst S orig_lty)) x =
      (Maps.find? S x).map (LMonoTy.subst [[(id, LMonoTy.subst S orig_lty)]]) := fun x hx =>
    (Maps.find?_insert_ne _ _ _ _ hx).trans (Subst.find?_apply _ _ _)
  have h_single_noop : ∀ t : LMonoTy, ¬(id ∈ t.freeVars) →
      LMonoTy.subst [[(id, LMonoTy.subst S orig_lty)]] t = t := fun t ht =>
    LMonoTy.subst_no_relevant_keys _ _ (fun x hx => by
      simp [Maps.keys, Map.keys]; intro heq; subst heq; exact ht hx)
  by_cases hS : Subst.hasEmptyScopes S
  · simp only [LMonoTy.subst_emptyS hS] at h_occurs h_find_ne ⊢
    apply LMonoTy.subst_no_relevant_keys
    intro x hx
    have h_ne : x ≠ id := fun h => h_occurs (h ▸ hx)
    exact Maps.find?_of_not_mem_values _ (by
      rw [h_find_ne x h_ne, Maps.not_mem_keys_find?_none' S x
        ((Subst.isEmpty_implies_keys_empty hS) ▸ (by simp))]; simp)
  · have hS_ne : Subst.hasEmptyScopes S = false := by
      revert hS; cases Subst.hasEmptyScopes S <;> simp
    suffices ∀ mty, ¬(id ∈ (LMonoTy.subst S mty).freeVars) →
        LMonoTy.subst (Maps.insert (Subst.apply [(id, LMonoTy.subst S orig_lty)] S)
          id (LMonoTy.subst S orig_lty)) mty = LMonoTy.subst S mty from
      this orig_lty h_occurs
    intro mty h_nf
    induction mty with
    | ftvar x =>
      by_cases h_id : x = id
      · subst h_id; exfalso; apply h_nf
        simp [LMonoTy.subst, hS_ne, h_none, LMonoTy.freeVars]
      · unfold LMonoTy.subst
        simp only [hS', hS_ne, Bool.false_eq_true, ↓reduceIte, h_find_ne x h_id]
        cases h_fx : Maps.find? S x with
        | none => simp
        | some t =>
          simp only [Option.map]
          exact h_single_noop t (by
            have : LMonoTy.subst S (.ftvar x) = t := by
              simp [LMonoTy.subst, hS_ne, h_fx]
            rwa [this] at h_nf)
    | bitvec n => simp [LMonoTy.subst]
    | tcons name args ih =>
      unfold LMonoTy.subst
      simp only [hS', hS_ne, Bool.false_eq_true, ↓reduceIte]
      congr 1
      rw [LMonoTys.subst_eq_substLogic, LMonoTys.subst_eq_substLogic]
      have h_nf' : ¬(id ∈ LMonoTys.freeVars (LMonoTys.substLogic S args)) := by
        have h_eq : LMonoTy.subst S (.tcons name args) =
            .tcons name (LMonoTys.subst S args) := by
          unfold LMonoTy.subst; simp [hS_ne]
        simp only [h_eq, LMonoTy.freeVars, LMonoTys.subst_eq_substLogic] at h_nf
        exact h_nf
      suffices ∀ xs,
          (∀ m, m ∈ xs → ¬(id ∈ (LMonoTy.subst S m).freeVars) →
            LMonoTy.subst (Maps.insert (Subst.apply [(id, LMonoTy.subst S orig_lty)] S)
              id (LMonoTy.subst S orig_lty)) m = LMonoTy.subst S m) →
          ¬(id ∈ LMonoTys.freeVars (LMonoTys.substLogic S xs)) →
          LMonoTys.substLogic (Maps.insert (Subst.apply [(id, LMonoTy.subst S orig_lty)] S)
            id (LMonoTy.subst S orig_lty)) xs = LMonoTys.substLogic S xs by
        exact this args (fun m hm h_nfm => ih m hm h_nfm) h_nf'
      intro xs; induction xs with
      | nil => intros; simp [LMonoTys.substLogic, hS', hS_ne]
      | cons a rest ih_rest =>
        intro ih_xs h_nf_xs
        simp only [LMonoTys.substLogic, hS', hS_ne, Bool.false_eq_true, ↓reduceIte]
        have h_eq_cons : LMonoTys.substLogic S (a :: rest) =
            LMonoTy.subst S a :: LMonoTys.substLogic S rest := by
          simp [LMonoTys.substLogic, hS_ne]
        rw [h_eq_cons, LMonoTys.freeVars_of_cons] at h_nf_xs
        have h1 : ¬(id ∈ (LMonoTy.subst S a).freeVars) :=
          fun h => h_nf_xs (List.mem_append_left _ h)
        have h2 : ¬(id ∈ LMonoTys.freeVars (LMonoTys.substLogic S rest)) :=
          fun h => h_nf_xs (List.mem_append_right _ h)
        rw [ih_xs a (.head _) h1,
            ih_rest (fun m hm => ih_xs m (.tail _ hm)) h2]

/-- Bundled result for the three properties proved simultaneously about `unifyOne`:
    soundness (constraint is equalized), absorption (output absorbs input),
    and key inclusion (output keys come from input keys, constraint freeVars,
    or input value freeVars). -/
structure Constraint.UnifyOneProperties (c : Constraint) (S : SubstInfo)
    (relS : ValidSubstRelation [c] S) : Prop where
  sound : LMonoTy.subst relS.newS.subst c.1 = LMonoTy.subst relS.newS.subst c.2
  absorbs : Subst.absorbs relS.newS.subst S.subst
  keys_incl : ∀ k, k ∈ Maps.keys relS.newS.subst →
    k ∈ Maps.keys S.subst ∨ k ∈ Constraint.freeVars c ∨ k ∈ Subst.freeVars S.subst

/-- Bundled result for the three properties proved simultaneously about `unifyCore`. -/
structure Constraints.UnifyCoreProperties (cs : Constraints) (S : SubstInfo)
    (relS : ValidSubstRelation cs S) : Prop where
  sound : ∀ p, p ∈ cs → LMonoTy.subst relS.newS.subst p.1 = LMonoTy.subst relS.newS.subst p.2
  absorbs : Subst.absorbs relS.newS.subst S.subst
  keys_incl : ∀ k, k ∈ Maps.keys relS.newS.subst →
    k ∈ Maps.keys S.subst ∨ k ∈ Constraints.freeVars cs ∨ k ∈ Subst.freeVars S.subst

-- Combined soundness, absorption, and key-inclusion for `unifyOne`/`unifyCore`.
-- A single mutual induction on `Constraint.unifyOne.induct` proves all three
-- properties simultaneously, sharing the 17-case decomposition.
--
-- The theorem proves `motive1` (for `unifyOne`) directly; `motive2` (for
-- `unifyCore`) is proved as part of the same induction and is exposed
-- separately via `Constraints.unifyCore_sound`.
theorem Constraint.unifyOne_sound (c : Constraint) (S : SubstInfo)
    (relS : ValidSubstRelation [c] S)
    (h : Constraint.unifyOne c S = .ok relS) :
    Constraint.UnifyOneProperties c S relS := by
  suffices ∀ relS, Constraint.unifyOne c S = .ok relS →
      Constraint.UnifyOneProperties c S relS from this relS h
  apply Constraint.unifyOne.induct
    (motive1 := fun c S => ∀ relS, Constraint.unifyOne c S = .ok relS →
      Constraint.UnifyOneProperties c S relS)
    (motive2 := fun cs S => ∀ relS, Constraints.unifyCore cs S = .ok relS →
      Constraints.UnifyCoreProperties cs S relS)
  -- Case 1: t1 == t2
  · intro S t1 t2 h_eq _ relS h
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h
    · simp only [Except.ok.injEq] at h; subst h
      exact ⟨by grind, Subst.absorbs_refl S.subst S.isWF, fun k hk => Or.inl hk⟩
    · exact absurd h_eq ‹_›
  -- Case 2: ftvar id, orig_lty; ftvar id == lty
  · intro S id orig_lty h_neq _lty _ _ h_eq_lty relS h
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h
    · exact absurd ‹_› h_neq
    · simp only [Except.ok.injEq] at h; subst h
      refine ⟨?_, Subst.absorbs_refl S.subst S.isWF, fun k hk => Or.inl hk⟩
      show LMonoTy.subst S.subst (.ftvar id) = LMonoTy.subst S.subst orig_lty
      have h_id_eq : LMonoTy.ftvar id = LMonoTy.subst S.subst orig_lty := eq_of_beq h_eq_lty
      rw [h_id_eq]; exact LMonoTy.subst_idempotent S.subst S.isWF orig_lty
  -- Case 3: ftvar id, orig_lty; occurs check — error
  · intro S id orig_lty h_neq _lty _ _ h_neq_lty h_occurs relS h
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h <;> grind
  -- Case 4: ftvar id, orig_lty; some sty — recursive
  · intro S id orig_lty h_neq _lty _ _ h_neq_lty h_not_occurs sty h_some ih_rec relS h
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h
    · exact absurd ‹_› h_neq
    · split at h
      · rename_i sty' h_some'
        rw [h_some] at h_some'; simp only [Option.some.injEq] at h_some'; subst h_some'
        simp only [bind, Except.bind] at h
        split at h
        · simp at h
        · rename_i relS' h_call
          simp only [Except.ok.injEq] at h; rw [← h]
          have ih := ih_rec relS' h_call
          -- Absorption (from IH)
          have h_abs := ih.absorbs
          -- Soundness: subst S' (ftvar id) = subst S' orig_lty
          have h_sound : LMonoTy.subst relS'.newS.subst (.ftvar id) =
              LMonoTy.subst relS'.newS.subst orig_lty := by
            have h_ftvar : LMonoTy.subst relS'.newS.subst (.ftvar id) =
                LMonoTy.subst relS'.newS.subst sty := by
              have := h_abs id sty h_some; simp only [this]
            have h_orig : LMonoTy.subst relS'.newS.subst (LMonoTy.subst S.subst orig_lty) =
                LMonoTy.subst relS'.newS.subst orig_lty :=
              LMonoTy.subst_absorbs relS'.newS.subst S.subst orig_lty h_abs
            rw [h_ftvar, ih.sound, h_orig]
          -- Key inclusion (from IH, lifting freeVars)
          have h_keys : ∀ k, k ∈ Maps.keys relS'.newS.subst →
              k ∈ Maps.keys S.subst ∨
              k ∈ Constraint.freeVars (LMonoTy.ftvar id, orig_lty) ∨
              k ∈ Subst.freeVars S.subst := by
            intro k hk
            rcases ih.keys_incl k hk with h1 | h2 | h3
            · left; exact h1
            · simp only [Constraint.freeVars, List.mem_append] at h2
              rcases h2 with h_sty | h_lty
              · right; right; exact Subst.freeVars_of_find_subset S.subst h_some h_sty
              · rcases List.mem_append.mp (LMonoTy.freeVars_of_subst_subset S.subst orig_lty h_lty) with
                  h_orig | h_vals
                · right; left; simp [Constraint.freeVars]; right; exact h_orig
                · right; right; exact h_vals
            · right; right; exact h3
          exact ⟨h_sound, h_abs, h_keys⟩
      · rename_i h_none; rw [h_some] at h_none; simp at h_none
  -- Case 5: ftvar id, orig_lty; none — insert+apply
  · intro S id orig_lty h_neq _lty _ _ h_neq_lty h_not_occurs h_none _ _ _ns h' _nS _ _ relS h
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h
    · exact absurd ‹_› h_neq
    · split at h
      · rename_i sty h_some; rw [h_none] at h_some; simp at h_some
      · simp only [Except.ok.injEq] at h; subst h
        refine ⟨?_, ?_, ?_⟩
        · -- Soundness
          exact Eq.trans
            (subst_ftvar_new_binding S.subst id (LMonoTy.subst S.subst orig_lty) h_none)
            (subst_orig_new_binding S.subst id (LMonoTy.subst S.subst orig_lty)
              orig_lty h_none rfl h_not_occurs).symm
        · -- Absorption
          exact absorbs_of_insert_apply_h' S id (LMonoTy.subst S.subst orig_lty) h_none
            (SubstWF.cons_of_subst_apply S id orig_lty _ rfl
              (SubstWF.single_subst id h_not_occurs) (SubstWF.apply_one_substituted_type S id orig_lty))
        · -- Key inclusion
          intro k hk
          have hk' := Maps.insert_keys_subset (ms := Subst.apply [(_,_)] S.subst) (key := _) (val := _) hk
          rw [Subst.keys_of_apply_eq] at hk'
          rcases List.mem_cons.mp hk' with rfl | h_old
          · right; left; simp [Constraint.freeVars, LMonoTy.freeVars]
          · left; exact h_old
  -- Case 6: orig_lty, ftvar id; ftvar id == lty
  · intro S orig_lty id h_neq _ _lty _ _ h_eq_lty relS h
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h
    · exact absurd ‹_› h_neq
    · simp only [Except.ok.injEq] at h; subst h
      refine ⟨?_, Subst.absorbs_refl S.subst S.isWF, fun k hk => Or.inl hk⟩
      show LMonoTy.subst S.subst orig_lty = LMonoTy.subst S.subst (.ftvar id)
      have h_id_eq : LMonoTy.ftvar id = LMonoTy.subst S.subst orig_lty := eq_of_beq h_eq_lty
      rw [h_id_eq]; exact (LMonoTy.subst_idempotent S.subst S.isWF orig_lty).symm
  -- Case 7: orig_lty, ftvar id; occurs check — error
  · intro S orig_lty id h_neq _ _lty _ _ h_neq_lty h_occurs relS h
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h
    · exact absurd ‹_› h_neq
    · simp at h
  -- Case 8: orig_lty, ftvar id; some sty — recursive (symmetric to case 4)
  · intro S orig_lty id h_neq _ _lty _ _ h_neq_lty h_not_occurs sty h_some ih_rec relS h
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h
    · exact absurd ‹_› h_neq
    · split at h
      · rename_i sty' h_some'
        rw [h_some] at h_some'; simp only [Option.some.injEq] at h_some'; subst h_some'
        simp only [bind, Except.bind] at h
        split at h
        · simp at h
        · rename_i relS' h_call
          simp only [Except.ok.injEq] at h; rw [← h]
          have ih := ih_rec relS' h_call
          have h_abs := ih.absorbs
          -- Soundness: subst S' orig_lty = subst S' (ftvar id)
          have h_sound : LMonoTy.subst relS'.newS.subst orig_lty =
              LMonoTy.subst relS'.newS.subst (.ftvar id) := by
            have h_ftvar : LMonoTy.subst relS'.newS.subst (.ftvar id) =
                LMonoTy.subst relS'.newS.subst sty := by
              have := h_abs id sty h_some; simp only [this]
            have h_orig : LMonoTy.subst relS'.newS.subst (LMonoTy.subst S.subst orig_lty) =
                LMonoTy.subst relS'.newS.subst orig_lty :=
              LMonoTy.subst_absorbs relS'.newS.subst S.subst orig_lty h_abs
            rw [← h_orig, ← ih.sound, h_ftvar]
          -- Key inclusion (symmetric to case 4)
          have h_keys : ∀ k, k ∈ Maps.keys relS'.newS.subst →
              k ∈ Maps.keys S.subst ∨
              k ∈ Constraint.freeVars (orig_lty, LMonoTy.ftvar id) ∨
              k ∈ Subst.freeVars S.subst := by
            intro k hk
            rcases ih.keys_incl k hk with h1 | h2 | h3
            · left; exact h1
            · simp only [Constraint.freeVars, List.mem_append] at h2
              rcases h2 with h_sty | h_lty
              · right; right; exact Subst.freeVars_of_find_subset S.subst h_some h_sty
              · rcases List.mem_append.mp (LMonoTy.freeVars_of_subst_subset S.subst orig_lty h_lty) with
                  h_orig | h_vals
                · right; left; simp [Constraint.freeVars]; left; exact h_orig
                · right; right; exact h_vals
            · right; right; exact h3
          exact ⟨h_sound, h_abs, h_keys⟩
      · rename_i h_none; rw [h_some] at h_none; simp at h_none
  -- Case 9: orig_lty, ftvar id; none — insert+apply (symmetric to case 5)
  · intro S orig_lty id h_neq _ _lty _ _ h_neq_lty h_not_occurs h_none _ _ _ns h' _nS _ _ relS h
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h
    · exact absurd ‹_› h_neq
    · split at h
      · rename_i sty h_some; rw [h_none] at h_some; simp at h_some
      · simp only [Except.ok.injEq] at h; subst h
        refine ⟨?_, ?_, ?_⟩
        · -- Soundness
          exact Eq.symm (Eq.trans
            (subst_ftvar_new_binding S.subst id (LMonoTy.subst S.subst orig_lty) h_none)
            (subst_orig_new_binding S.subst id (LMonoTy.subst S.subst orig_lty)
              orig_lty h_none rfl h_not_occurs).symm)
        · -- Absorption
          exact absorbs_of_insert_apply_h' S id (LMonoTy.subst S.subst orig_lty) h_none
            (SubstWF.cons_of_subst_apply S id orig_lty _ rfl
              (SubstWF.single_subst id h_not_occurs) (SubstWF.apply_one_substituted_type S id orig_lty))
        · -- Key inclusion
          intro k hk
          have hk' := Maps.insert_keys_subset (ms := Subst.apply [(_,_)] S.subst) (key := _) (val := _) hk
          rw [Subst.keys_of_apply_eq] at hk'
          rcases List.mem_cons.mp hk' with rfl | h_old
          · right; left; simp [Constraint.freeVars, LMonoTy.freeVars]
          · left; exact h_old
  -- Case 10: bitvec n1 == n2 contradiction
  · intro S n1 n2 h_neq h_eq_n relS h; grind
  -- Case 11: bitvec n1 ≠ n2 — error
  · intro S n1 n2 h_neq h_neq_n relS h
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h <;> grind
  -- Case 12: tcons match — recursive unifyCore
  · intro S name1 args1 name2 args2 h_neq h_match _nc ih_core relS h
    rw [Constraint.unifyOne.eq_def] at h; simp only at h; split at h
    · exact absurd ‹_› h_neq
    · simp only [bind, Except.bind] at h
      split at h
      · simp at h
      · rename_i relS' h_call
        simp only [Except.ok.injEq] at h; rw [← h]
        have ih := ih_core relS' h_call
        refine ⟨?_, ih.absorbs, ?_⟩
        · -- Soundness: subst S' (tcons name1 args1) = subst S' (tcons name2 args2)
          have h_name_eq : name1 = name2 := by
            have := (Bool.and_eq_true _ _ ▸ h_match : _ ∧ _).1; exact eq_of_beq this
          have h_len_eq : args1.length = args2.length := by
            have := (Bool.and_eq_true _ _ ▸ h_match : _ ∧ _).2; exact of_decide_eq_true this
          subst h_name_eq
          have ih_pw := ih.sound
          have h_args_eq : ∀ (l1 l2 : LMonoTys), l1.length = l2.length →
              (∀ p, p ∈ l1.zip l2 →
                LMonoTy.subst relS'.newS.subst p.1 = LMonoTy.subst relS'.newS.subst p.2) →
              LMonoTys.subst relS'.newS.subst l1 = LMonoTys.subst relS'.newS.subst l2 := by
            intro l1 l2 h_len h_pw
            rw [LMonoTys.subst_eq_substLogic, LMonoTys.subst_eq_substLogic]
            by_cases hS : Subst.hasEmptyScopes relS'.newS.subst
            · have h_id : ∀ l, LMonoTys.substLogic relS'.newS.subst l = l := by
                intro l; induction l with
                | nil => simp [LMonoTys.substLogic, hS]
                | cons _ _ _ => simp [LMonoTys.substLogic, hS]
              rw [h_id, h_id]
              induction l1 generalizing l2 with
              | nil => cases l2 with | nil => rfl | cons _ _ => simp at h_len
              | cons a rest ih_l =>
                cases l2 with
                | nil => simp at h_len
                | cons b rest2 =>
                  simp at h_len
                  have h_ab := h_pw (a, b) List.mem_cons_self
                  simp [LMonoTy.subst_emptyS hS] at h_ab
                  rw [h_ab, ih_l rest2 h_len fun p hp => h_pw p (List.mem_cons_of_mem _ hp)]
            · have hS_ne : Subst.hasEmptyScopes relS'.newS.subst = false := by
                revert hS; cases Subst.hasEmptyScopes relS'.newS.subst <;> simp
              induction l1 generalizing l2 with
              | nil => cases l2 with | nil => simp [LMonoTys.substLogic, hS_ne] | cons _ _ => simp at h_len
              | cons a rest ih_l =>
                cases l2 with
                | nil => simp at h_len
                | cons b rest2 =>
                  simp at h_len
                  simp only [LMonoTys.substLogic, hS_ne, Bool.false_eq_true, ↓reduceIte]
                  have h_ab : LMonoTy.subst relS'.newS.subst a = LMonoTy.subst relS'.newS.subst b :=
                    h_pw (a, b) List.mem_cons_self
                  rw [h_ab, ih_l rest2 h_len fun p hp => h_pw p (List.mem_cons_of_mem _ hp)]
          have h_list := h_args_eq args1 args2 h_len_eq ih_pw
          by_cases hS_final : Subst.hasEmptyScopes relS'.newS.subst
          · simp [LMonoTy.subst_emptyS hS_final]
            simp [LMonoTys.subst, hS_final] at h_list; rw [h_list]
          · have hS_ne : Subst.hasEmptyScopes relS'.newS.subst = false := by
              revert hS_final; cases Subst.hasEmptyScopes relS'.newS.subst <;> simp
            simp [LMonoTy.subst, hS_ne]; exact h_list
        · -- Key inclusion
          intro k hk
          rcases ih.keys_incl k hk with h1 | h2 | h3
          · left; exact h1
          · right; left; simp only [Constraint.freeVars, LMonoTy.freeVars, List.mem_append]
            exact List.mem_append.mp (Constraints.freeVars_of_zip_subset h2)
          · right; right; exact h3
  -- Case 13: tcons name/length mismatch — error
  · intro S name1 args1 name2 args2 h_neq h_mismatch relS h
    rw [Constraint.unifyOne.eq_def] at h; grind
  -- Case 14: bitvec, tcons — error
  · intro S size name args h_neq relS h
    rw [Constraint.unifyOne.eq_def] at h; grind
  -- Case 15: tcons, bitvec — error
  · intro S name args size h_neq relS h
    rw [Constraint.unifyOne.eq_def] at h; grind
  -- Case 16: unifyCore []
  · intro S relS h
    rw [Constraints.unifyCore.eq_def] at h; simp only at h
    simp only [Except.ok.injEq] at h; subst h
    exact ⟨fun p hp => by grind, Subst.absorbs_refl S.subst S.isWF, fun k hk => Or.inl hk⟩
  -- Case 17: unifyCore c :: rest
  · intro S c c_rest ih1 ih2 relS h
    rw [Constraints.unifyCore.eq_def] at h; simp only at h
    simp only [Bind.bind, Except.bind, Except.mapError] at h
    split at h
    · simp at h
    · rename_i relS_one h_one_raw
      have h_one := Except.mapError_ok_h' h_one_raw
      split at h
      · simp at h
      · rename_i relS_rest h_rest
        simp only [Except.ok.injEq] at h; subst h
        have ih_one := ih1 relS_one h_one
        have ih_rest := ih2 relS_one relS_rest h_rest
        refine ⟨?_, ?_, ?_⟩
        · -- Soundness: all pairs in c :: c_rest are equalized
          intro p hp
          cases List.mem_cons.mp hp with
          | inl h_pc =>
            subst h_pc
            have h_sound_one := ih_one.sound
            have h_abs := ih_rest.absorbs
            calc LMonoTy.subst relS_rest.newS.subst p.1
                = LMonoTy.subst relS_rest.newS.subst (LMonoTy.subst relS_one.newS.subst p.1) :=
                  (LMonoTy.subst_absorbs _ _ _ h_abs).symm
              _ = LMonoTy.subst relS_rest.newS.subst (LMonoTy.subst relS_one.newS.subst p.2) := by
                  rw [h_sound_one]
              _ = LMonoTy.subst relS_rest.newS.subst p.2 :=
                  LMonoTy.subst_absorbs _ _ _ h_abs
          | inr h_rest_mem =>
            exact ih_rest.sound p h_rest_mem
        · -- Absorption: transitive
          exact Subst.absorbs_trans S.subst relS_one.newS.subst relS_rest.newS.subst
            ih_one.absorbs ih_rest.absorbs
        · -- Key inclusion
          intro k hk
          rcases ih_rest.keys_incl k hk with hk1 | hk2 | hk3
          · rcases ih_one.keys_incl k hk1 with h1a | h1b | h1c
            · left; exact h1a
            · right; left; simp [Constraints.freeVars]; left; exact h1b
            · right; right; exact h1c
          · right; left; simp [Constraints.freeVars]; right; exact hk2
          · rcases List.mem_append.mp (relS_one.goodSubset hk3) with h_c | h_s
            · right; left; simp [Constraints.freeVars]; left
              simp [Constraints.freeVars] at h_c; exact h_c
            · right; right; exact h_s

/-- Combined soundness, absorption, and key-inclusion for `unifyCore`.
    Proved by simple list induction, delegating to `Constraint.unifyOne_sound`
    for each head constraint. -/
theorem Constraints.unifyCore_sound (cs : Constraints) (S : SubstInfo)
    (relS : ValidSubstRelation cs S)
    (h : Constraints.unifyCore cs S = .ok relS) :
    Constraints.UnifyCoreProperties cs S relS := by
  induction cs generalizing S with
  | nil =>
    rw [Constraints.unifyCore.eq_def] at h; simp only at h
    simp only [Except.ok.injEq] at h; subst h
    exact ⟨fun p hp => by grind, Subst.absorbs_refl S.subst S.isWF, fun k hk => Or.inl hk⟩
  | cons c rest ih =>
    rw [Constraints.unifyCore.eq_def] at h; simp only at h
    simp only [Bind.bind, Except.bind, Except.mapError] at h
    split at h
    · simp at h
    · rename_i relS_one h_one_raw
      have h_one := Except.mapError_ok_h' h_one_raw
      split at h
      · simp at h
      · rename_i relS_rest h_rest
        simp only [Except.ok.injEq] at h; subst h
        have ih_one := Constraint.unifyOne_sound c S relS_one h_one
        have ih_rest := ih relS_one.newS relS_rest h_rest
        refine ⟨?_, ?_, ?_⟩
        · -- Soundness
          intro p hp
          cases List.mem_cons.mp hp with
          | inl h_pc =>
            subst h_pc
            have h_abs := ih_rest.absorbs
            calc LMonoTy.subst relS_rest.newS.subst p.1
                = LMonoTy.subst relS_rest.newS.subst (LMonoTy.subst relS_one.newS.subst p.1) :=
                  (LMonoTy.subst_absorbs _ _ _ h_abs).symm
              _ = LMonoTy.subst relS_rest.newS.subst (LMonoTy.subst relS_one.newS.subst p.2) := by
                  rw [ih_one.sound]
              _ = LMonoTy.subst relS_rest.newS.subst p.2 :=
                  LMonoTy.subst_absorbs _ _ _ h_abs
          | inr h_rest_mem =>
            exact ih_rest.sound p h_rest_mem
        · -- Absorption
          exact Subst.absorbs_trans S.subst relS_one.newS.subst relS_rest.newS.subst
            ih_one.absorbs ih_rest.absorbs
        · -- Key inclusion
          intro k hk
          rcases ih_rest.keys_incl k hk with hk1 | hk2 | hk3
          · rcases ih_one.keys_incl k hk1 with h1a | h1b | h1c
            · left; exact h1a
            · right; left; simp [Constraints.freeVars]; left; exact h1b
            · right; right; exact h1c
          · right; left; simp [Constraints.freeVars]; right; exact hk2
          · rcases List.mem_append.mp (relS_one.goodSubset hk3) with h_c | h_s
            · right; left; simp [Constraints.freeVars]; left
              simp [Constraints.freeVars] at h_c; exact h_c
            · right; right; exact h_s

/-- Unification produces a substitution that absorbs the input substitution. -/
theorem unify_absorbs (constraints : Constraints) (S_old S_new : SubstInfo)
    (h : Constraints.unify constraints S_old = .ok S_new) :
    Subst.absorbs S_new.subst S_old.subst := by
  simp only [Constraints.unify, bind, Except.bind] at h
  split at h
  · simp at h
  · rename_i relS h_core
    simp only [Except.ok.injEq] at h; subst h
    exact (Constraints.unifyCore_sound constraints S_old relS h_core).absorbs

---------------------------------------------------------------------

end -- public section
end Lambda
