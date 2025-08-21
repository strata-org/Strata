/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/

import Strata.DL.Lambda.LTy
import Strata.DL.Util.List

/-!
## Type Substitution and Unification

Implementation of type substitution and unification for Lambda. This is similar
to Algorithm J in Hindley-Milner systems.
-/

---------------------------------------------------------------------

namespace Lambda

open Std (ToFormat Format format)

/-! ### Type Substitution -/

/-- Substitution mapping type variables to `LMonoTy`. -/
abbrev Subst := Map TyIdentifier LMonoTy

private def formatSubst (S : Subst) : Format :=
  match S with
  | [] => ""
  | (id, lty) :: rest => f!"({id}, {lty})\n{formatSubst rest}"

instance : ToFormat Subst where
  format := formatSubst

/--
The free variables in a substitution `S` are the union of the free variables in
every type in `S`.

Note that we do not deduplicate the resulting list.
-/
def Subst.freeVars (S : Subst) : List TyIdentifier :=
  S.values.flatMap LMonoTy.freeVars

@[simp]
theorem Subst.freeVars_empty :
    Subst.freeVars [] = [] := by
  simp [Subst.freeVars, Map.values]

@[simp]
theorem Subst.freeVars_cons (S : Subst) :
    Subst.freeVars (s :: S) = s.snd.freeVars ++ S.freeVars := by
  simp [Subst.freeVars, Map.values]

theorem Subst.freeVars_of_find_subset (S : Subst) (hi : Map.find? S i = some sty) :
    LMonoTy.freeVars sty ⊆ Subst.freeVars S := by
  have h_sty_map_value := @Map.find?_mem_values _ _ i sty _ S hi
  simp [List.instHasSubset, List.Subset, Subst.freeVars]
  intro x hx
  apply Exists.intro sty
  simp_all

/--
A substitution map `S` is well-formed if no key appears in the free type
variables of the values.
-/
def SubstWF (S : Subst) : Bool :=
  S.keys.all (fun k => k ∉ Subst.freeVars S)

theorem SubstWF_of_cons (h : SubstWF (s :: S)) :
    SubstWF [s] ∧ SubstWF S := by
  simp_all [SubstWF, Subst.freeVars]
  constructor
  · -- SubstWF [s]
    intro ty hty id hid
    exact h ty (by simp_all [Map.keys]) id (by simp_all [Map.values])
  · -- SubstWF S
    intro ty hty id hid
    exact h ty (by simp_all [Map.keys]) id (by simp_all [Map.values])
  done

theorem SubstWF_mk_cons
    (h_s_not_in_S_values : s.fst ∉ S.freeVars)
    (h_s_not_in_S_keys : S.keys.all (fun k => k ∉ s.snd.freeVars))
    (h_s_WF : SubstWF [s])
    (h_S_WF : SubstWF S) :
    SubstWF (s :: S) := by
  simp_all [SubstWF, Map.values, Map.keys, Subst.freeVars]
  done

theorem SubstWF.single_subst (id : TyIdentifier) (h : ¬id ∈ ty.freeVars) :
    SubstWF [(id, ty)] := by
  simp [SubstWF]
  intro lty' h_lty
  simp [Map.keys] at h_lty; subst lty'
  simp_all
  done

@[simp]
theorem SubstWF_of_empty : SubstWF [] := by
  simp [SubstWF]

/--
A type substitution, along with a proof that it is well-formed.
-/
structure SubstInfo where
  subst : Subst
  isWF : SubstWF subst
  deriving Repr

def SubstInfo.empty : SubstInfo :=
  { subst := [],
    isWF := SubstWF_of_empty }

mutual
/--
Apply substitution `S` to monotype `mty`.
-/
def LMonoTy.subst (S : Subst) (mty : LMonoTy) : LMonoTy :=
  match mty with
  | .ftvar x => match S.find? x with
                | some sty => sty | none => mty
  | .bitvec _ => mty
  | .tcons name ltys =>
    .tcons name (LMonoTys.subst S ltys)
/--
Apply substitution `S` to monotypes `mtys`.
-/
def LMonoTys.subst (S : Subst) (mtys : LMonoTys) : LMonoTys :=
    match mtys with
    | [] => [] | ty :: rest => LMonoTy.subst S ty :: LMonoTys.subst S rest
end

/--
No key (i.e., type identifier) in a well-formed substitution `S` can appear as a
free variable in a substituted type (i.e., in `LMonoTy.subst S ty`).
-/
theorem LMonoTy.subst_keys_not_in_substituted_type (h : SubstWF S) :
    S.keys.all (fun k => k ∉ LMonoTy.freeVars (LMonoTy.subst S ty)) := by
  induction ty
  case ftvar i =>
    simp_all [LMonoTy.subst]
    intro id hid
    split
    · rename_i _ sty heq
      simp_all [SubstWF, Subst.freeVars]
      have hmap := @Map.find?_mem_values _ _ i sty _ S heq
      exact h id hid sty hmap
    · simp_all [freeVars]
      have := @Map.find?_of_not_mem_values _ _ i _ S
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
    case nil => simp_all [LMonoTys.subst, LMonoTys.freeVars, LMonoTy.freeVars]
    case cons head tail tail_ih =>
      simp_all
      obtain ⟨h1, h2⟩ := h1
      intro x hx
      have h1' := h1 x hx
      simp [LMonoTy.freeVars, LMonoTys.subst] at tail_ih ⊢
      simp [h1']
      exact tail_ih x hx
  done

/--
The free variables in a type `mty` after the application of a substitution `S`
are a subset of the free variables in `mty` and the free variables in `S`.
-/
theorem LMonoTy.freeVars_of_subst_subset (S : Subst) (mty : LMonoTy) :
    LMonoTy.freeVars (LMonoTy.subst S mty) ⊆
    LMonoTy.freeVars mty ++ Subst.freeVars S := by
  simp [Subst.freeVars]
  induction mty
  case ftvar x =>
    simp [subst]
    split
    · -- Case: S.find? x = some sty
      rename_i sty h_find
      intro v hv; simp_all; right
      apply Exists.intro sty; simp [hv]
      apply @Map.find?_mem_values _ _ x sty _ S h_find
    · -- Case: S.find? x = none
      simp [freeVars]
  case bitvec n =>
    simp [subst]
  case tcons name args ih =>
    simp [LMonoTy.subst, LMonoTy.freeVars]
    induction args
    case nil => simp_all [LMonoTys.freeVars, LMonoTys.subst]
    case cons mty mtys mtys_ih =>
      simp_all
      simp [LMonoTys.subst]
      generalize (subst S mty).freeVars = x at mtys_ih ih
      generalize mty.freeVars = a at mtys_ih ih
      generalize LMonoTys.freeVars mtys = b at mtys_ih ih
      generalize List.flatMap freeVars (Map.values S) = c at mtys_ih ih
      generalize (LMonoTys.subst S mtys).freeVars = d at mtys_ih ih
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
Apply the `new` substitution to the `old` one.
-/
def Subst.apply (new : Subst) (old : Subst) : Subst :=
  match old with
  | [] => []
  | (id, lty) :: rest =>
    (id, LMonoTy.subst new lty) :: Subst.apply new rest

@[simp]
theorem Subst.keys_of_apply_eq :
    Map.keys (Subst.apply new old) = Map.keys old := by
  induction old <;> simp_all [Map.keys, Subst.apply]

/--
No key in a well-formed substitution `newS` appears in the free variables of a
composed substitution `(Subst.apply newS oldS)`. Note that there are no
restrictions on `oldS` here.
-/
theorem Subst.keys_not_in_apply (h : SubstWF newS) :
    newS.keys.all (fun k => k ∉ Subst.freeVars (Subst.apply newS oldS)) := by
  simp [Subst.freeVars]
  induction oldS
  case nil => simp_all [Subst.apply, Map.values]
  case cons head tail tail_ih =>
    simp_all [Subst.apply]
    intro i hi ty hty
    simp [Map.values] at hty
    cases hty
    case inl h1 =>
      have := @LMonoTy.subst_keys_not_in_substituted_type newS head.snd h
      simp_all
    case inr h1 =>
      exact tail_ih i hi ty h1
  done

/--
For all types `mty` in a substitution `(Subst.apply newS S)`, the free variables
in `mty` are a subset of those in `newS` and `S`.
-/
theorem Subst.freeVars_of_apply_subset (newS S : Subst) (mty : LMonoTy)
    (h : mty ∈ Map.values (Subst.apply newS S)) :
    LMonoTy.freeVars mty ⊆ Subst.freeVars newS ++ Subst.freeVars S := by
  induction S generalizing mty newS
  case nil => simp_all [Map.values, Subst.apply]
  case cons head tail tail_ih =>
    simp [Subst.apply, Map.values] at h
    cases h with
    | inl h_head =>
      subst mty
      have h_subset := @LMonoTy.freeVars_of_subst_subset newS head.snd
      generalize (LMonoTy.subst newS head.snd).freeVars = x at h_subset
      simp [Subst.freeVars_cons]
      generalize head.snd.freeVars = y at h_subset
      generalize newS.freeVars = z at *
      generalize freeVars tail = w at *
      have h1 :=  @List.subset_append_of_subset_right _ x (y ++ z) w h_subset
      have h2 : w ++ (y ++ z) ⊆ z ++ (y ++ w) := by
        simp_all (config := {maxDischargeDepth := 1000})
      exact fun _ x => h2 (h1 x)
    | inr h_tail =>
      have : freeVars newS ++ freeVars tail ⊆ freeVars newS ++ freeVars (head :: tail) := by
        simp_all
      exact List.Subset.trans (tail_ih newS mty h_tail) this
  done

/--
The free variables in `(Subst.apply newS S)` are a subset of those in `newS` and
`S`.
-/
theorem Subst.freeVars_of_apply_subset_alt (newS S : Subst) :
    Subst.freeVars (Subst.apply newS S) ⊆
    Subst.freeVars newS ++ Subst.freeVars S := by
  have h := @Subst.freeVars_of_apply_subset newS S
  simp_all [Subst.freeVars]
  generalize (Map.values (newS.apply S)) = A at *
  generalize newS.values.flatMap LMonoTy.freeVars = B at *
  generalize S.values.flatMap LMonoTy.freeVars = C at *
  simp [List.instHasSubset, List.Subset]
  intro x ty hty hx
  exact List.mem_append.mp (h ty hty hx)
  done

theorem SubstWF.apply_one_substituted_type (S : SubstInfo) (id : TyIdentifier) (ty : LMonoTy) :
    SubstWF (Subst.apply [(id, LMonoTy.subst S.subst ty)] S.subst) := by
  simp [SubstWF]; intro i hi
  generalize h_new_ty : LMonoTy.subst S.subst ty = new_ty at *
  have h1 : S.subst.keys.all (fun k => k ∉ new_ty.freeVars) := by
    have := @LMonoTy.subst_keys_not_in_substituted_type S.subst ty S.isWF
    simp; simp_all
  have hsubset := @Subst.freeVars_of_apply_subset_alt [(id, new_ty)] S.subst
  have h_id_new_ty : Subst.freeVars [(id, new_ty)] = new_ty.freeVars := by
    simp [Subst.freeVars, Map.values]
  rw [h_id_new_ty] at hsubset
  have h_i_not_in_new_ty : i ∉ new_ty.freeVars := by simp_all
  have h_i_not_in_S_values : i ∉ S.subst.freeVars := by
    have h := S.isWF
    simp [SubstWF] at h; simp_all
  have h_i_not_in_union : i ∉ new_ty.freeVars ++ S.subst.freeVars := by
    exact List.not_mem_append h_i_not_in_new_ty h_i_not_in_S_values
  subst new_ty
  exact fun a => h_i_not_in_union (hsubset a)
  done

theorem SubstWF.cons_of_subst_apply (S : SubstInfo) (id : TyIdentifier) (ty newty : LMonoTy)
    (h_newty : newty = LMonoTy.subst S.subst ty)
    (h_id_newty_WF : SubstWF [(id, newty)])
    (h_subst_apply_WF : SubstWF (Subst.apply [(id, newty)] S.subst)) :
    SubstWF ((id, newty) :: Subst.apply [(id, newty)] S.subst) := by
  have h_cons := @SubstWF_mk_cons (id, newty) (Subst.apply [(id, newty)] S.subst)
  have h_id_not_in_apply : id ∉ (Subst.apply [(id, newty)] S.subst).freeVars := by
    simp_all
    have := @Subst.keys_not_in_apply [(id, newty)] S.subst
    simp_all [Map.keys]
  have h : (∀ (x : TyIdentifier), x ∈ Map.keys S.subst → ¬x ∈ newty.freeVars) := by
    have := @LMonoTy.subst_keys_not_in_substituted_type S.subst ty S.isWF
    simp [h_newty]; simp_all
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

---------------------------------------------------------------------

/-! ### Type Constraints -/

/--
A type constraint `(ty1, ty2)` that records that `ty1` and `ty2` must
have a common substitution instance.
-/
abbrev Constraint := (LMonoTy × LMonoTy)
/--
A list of type constraints. These should really be viewed as a set.
-/
abbrev Constraints := List Constraint

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
    (_h5 : Map.find? S.subst id = some sty)
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

theorem Subst.freeVars_subset_prop_of_single_constraint
    (S newS : SubstInfo) (new_subst : Subst) (id : TyIdentifier) (orig_lty lty : LMonoTy)
    (h_lty : lty = LMonoTy.subst S.subst orig_lty)
    (h_new_subst : new_subst = (id, lty) :: Subst.apply [(id, lty)] S.subst)
    (h' : SubstWF new_subst)
    (h_newS : newS = { subst := new_subst, isWF := h' }) :
    Subst.freeVars_subset_prop [(LMonoTy.ftvar id, orig_lty)] newS S := by
  simp_all [Subst.freeVars_subset_prop]
  simp [Constraints.freeVars]
  have h_orig_lty_subset := @LMonoTy.freeVars_of_subst_subset S.subst orig_lty
  have h_subset := @Subst.freeVars_of_apply_subset_alt
                 [(id, LMonoTy.subst S.subst orig_lty)] S.subst
  apply And.intro
  case left =>
    simp at h_subset
    apply List.subset_cons_of_subset id
    simp_all (config := {maxDischargeDepth := 10})
  case right =>
    simp_all [Constraint.freeVars, LMonoTy.freeVars]
    generalize (LMonoTy.subst S.subst orig_lty).freeVars = B at *
    have : B ++ S.subst.freeVars ⊆ orig_lty.freeVars ++ S.subst.freeVars := by
      simp_all
    exact List.subset_cons_of_subset id fun _ x => this (h_subset x)
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
  generalize List.flatMap LMonoTy.freeVars (Map.values newS.subst) = A at *
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
    (_h5 : Map.find? S.subst id = some sty) :
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
    · have h_sty_values := @Map.find?_mem_values _ _ id sty _ S.subst _h5
      have h_id_keys := @Map.find?_mem_keys _ _ id sty _ S.subst _h5
      exact fun a => h_S_ok id h_id_keys (h_sty a)
    · have h_id_keys := @Map.find?_mem_keys _ _ id sty _ S.subst _h5
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
    (_h5 : Map.find? S.subst id = some sty) :
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

mutual
def Constraint.unifyOne (c : Constraint) (S : SubstInfo) :
  Except Format (ValidSubstRelation [c] S) :=
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
        .error f!"Ftvar {id} is in the free variables of {lty}!"
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
          have h_id_lty_WF : SubstWF [(id, lty)] = true := by
            exact SubstWF.single_subst id _h4
          have h_subst_apply_WF :  SubstWF (Subst.apply [(id, lty)] S.subst) := by
            exact SubstWF.apply_one_substituted_type S id orig_lty
          let new_subst := (id, lty) :: Subst.apply [(id, lty)] S.subst
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
        .error f!"Cannot unify differently sized bitvector types {t1} and {t2}!"
    | .tcons name1 args1, .tcons name2 args2 => do
      if _h6 : name1 == name2 && args1.length == args2.length then
       let new_constraints := List.zip args1 args2
       let relS ← Constraints.unifyCore new_constraints S
       have h_sub : Subst.freeVars_subset_prop
                    [(LMonoTy.tcons name1 args1, LMonoTy.tcons name2 args2)] relS.newS S := by
         exact Subst.freeVars_subset_prop_of_tcons S name1 name2 args1 args2 rfl relS
       .ok { newS := relS.newS, goodSubset := by simp [h_sub] }
      else
        .error f!"Cannot unify differently named type constructors {t1} and {t2}!"
    | .bitvec _, .tcons _ _ =>
        .error f!"Cannot unify bv type {t1} and type constructor {t2}!"
    | .tcons _ _, .bitvec _ =>
        .error f!"Cannot unify type constructor {t1} and bv type {t2}!"
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

def Constraints.unifyCore (cs : Constraints) (S : SubstInfo) :
    Except Format (ValidSubstRelation cs S) := do
  match _h0 : cs with
  | [] => .ok { newS := S, goodSubset := by simp [Subst.freeVars_subset_prop_of_empty] }
  | c :: c_rest =>
    let relS ← Constraint.unifyOne c S
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
-/
def Constraints.unify (constraints : Constraints) (S : SubstInfo) :
    Except Format SubstInfo := do
    let relS ← Constraints.unifyCore constraints S
    .ok relS.newS

/--
info: ok: (b, (arrow c d))
(a, int)
-/
#guard_msgs in
open LTy.Syntax in
#eval  do let S ← Constraints.unify [(mty[%a → %b], mty[int → (%c → %d)])] SubstInfo.empty
          return (format S.subst)

---------------------------------------------------------------------

end Lambda
