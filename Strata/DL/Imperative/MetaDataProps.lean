/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.MetaData
import all Strata.DL.Imperative.MetaData
public import Strata.Util.ListUtilsProps

/-! # Properties of metadata

- `MetaData.mapExprs_empty`: mapping the expressions of the empty metadata gives the empty
  metadata.
- `MetaData.mapExprs_id`: mapping the expressions of metadata by the identity changes nothing.
- `MetaData.exprs_mapExprs`: the expressions of mapped metadata are the mapped expressions.
- `MetaData.mapExprs_mapExprs_of`: a second expression map absorbs a first one that it does not
  distinguish from the identity.
- `MetaData.mapExprs_eq_of_rel`: related metadata arrays agree after mapping their expressions
  by a function that identifies `G`-related expressions.
- `MetaData.Rel.mapExprs_right`: mapping the expressions of the second array by a function that
  keeps `G`-related expressions related preserves the relation.
-/

namespace Imperative

public section

/-- `mapExprs` of the empty metadata is the empty metadata. -/
theorem MetaData.mapExprs_empty {P : PureExpr} (g : P.Expr → P.Expr) :
    (MetaData.empty : MetaData P).mapExprs g = MetaData.empty := by
  first
  | rfl
  | simp [MetaData.mapExprs, MetaData.mapExprsM, MetaData.empty]

/-- `mapExprs` with the identity is the identity. -/
theorem MetaData.mapExprs_id {P : PureExpr} (md : MetaData P) : md.mapExprs id = md := by
  rcases md with ⟨l⟩
  simp only [MetaData.mapExprs, MetaData.mapExprsM]
  simp only [id_eq, bind_pure_comp, map_pure, List.mapM_toArray, Id.run_map, List.idRun_mapM,
    Array.mk.injEq]
  refine (List.map_congr_left fun x _ => ?_).trans (List.map_id l)
  rcases x with ⟨fld, value⟩
  cases value <;> rfl

/-- The expressions of `md.mapExprs h` are those of `md`, mapped by `h`. -/
theorem MetaData.exprs_mapExprs {P : PureExpr} (h : P.Expr → P.Expr) (md : MetaData P) :
    (md.mapExprs h).exprs = md.exprs.map h := by
  rcases md with ⟨l⟩
  simp only [MetaData.mapExprs, MetaData.mapExprsM, MetaData.exprs]
  simp only [bind_pure_comp, map_pure, List.mapM_toArray, Id.run_map, List.idRun_mapM]
  induction l with
  | nil => rfl
  | cons e l ih =>
    rcases e with ⟨fld, value⟩
    cases value <;> simp_all

/-- Mapping the expressions of metadata by `f` and then `g` is mapping by `g` when `g` cannot tell
    `f e` from `e`. -/
theorem MetaData.mapExprs_mapExprs_of {P : PureExpr} (f g : P.Expr → P.Expr)
    (hgf : ∀ e, g (f e) = g e) (md : MetaData P) :
    (md.mapExprs f).mapExprs g = md.mapExprs g := by
  rcases md with ⟨l⟩
  simp only [MetaData.mapExprs, MetaData.mapExprsM, bind_pure_comp, map_pure,
    List.mapM_toArray, Id.run_map, List.idRun_mapM, Array.mk.injEq, List.map_map]
  refine List.map_congr_left fun e _ => ?_
  rcases e with ⟨fld, v⟩
  cases v <;> simp only [Function.comp_apply, Id.run_pure, hgf]

/-- Related metadata values are equal when the first is not an expression. -/
theorem MetaDataElem.Value.Rel.eq_of_ne_expr {P : PureExpr} {G : P.Expr → P.Expr → Prop}
    {v v' : MetaDataElem.Value P} (h : ∀ e, v ≠ .expr e) (hval : MetaDataElem.Value.Rel G v v') :
    v = v' := by
  cases v with
  | expr e => exact absurd rfl (h e)
  | _ => exact hval

/-- Related metadata values are equal when the second is not an expression. -/
theorem MetaDataElem.Value.Rel.eq_of_ne_expr_right {P : PureExpr} {G : P.Expr → P.Expr → Prop}
    {v v' : MetaDataElem.Value P} (h : ∀ e, v' ≠ .expr e) (hval : MetaDataElem.Value.Rel G v v') :
    v = v' := by
  cases v with
  | expr e =>
    cases v' with
    | expr e' => exact absurd rfl (h e')
    | _ => exact hval
  | _ => exact hval

/-- A value that is not an expression is related to itself. -/
theorem MetaDataElem.Value.Rel.refl_of_ne_expr {P : PureExpr} {G : P.Expr → P.Expr → Prop}
    {v : MetaDataElem.Value P} (h : ∀ e, v ≠ .expr e) : MetaDataElem.Value.Rel G v v := by
  cases v with
  | expr e => exact absurd rfl (h e)
  | _ => rfl

/-- Mapping the expressions of two related metadata arrays by a function that identifies
    `G`-related expressions gives equal arrays. -/
theorem MetaData.mapExprs_eq_of_rel {P : PureExpr} {G : P.Expr → P.Expr → Prop}
    {md md' : MetaData P} (fe : P.Expr → P.Expr)
    (hG : ∀ p q, G p q → fe q = fe p) (h : MetaData.Rel G md md') :
    md'.mapExprs fe = md.mapExprs fe := by
  rcases md with ⟨l⟩
  rcases md' with ⟨l'⟩
  unfold MetaData.Rel at h
  simp only [MetaData.mapExprs, MetaData.mapExprsM, bind_pure_comp, map_pure,
    List.mapM_toArray, Id.run_map, List.idRun_mapM, Array.mk.injEq]
  refine (List.Rel₂.map_eq ?_ h).symm
  intro e e' hee
  obtain ⟨hfld, hval⟩ := hee
  rcases e with ⟨f, v⟩
  rcases e' with ⟨f', v'⟩
  simp only at hfld hval
  subst hfld
  by_cases hex : ∃ x, v = .expr x
  · obtain ⟨x, hx⟩ := hex
    subst hx
    cases v' with
    | expr x' =>
      simp only [MetaDataElem.Value.Rel] at hval
      simp only [hG x x' hval]
    | msg m => cases hval
    | switch b => cases hval
    | provenance p => cases hval
  · have hne : ∀ e, v ≠ .expr e := fun e he => hex ⟨e, he⟩
    have heq : v = v' := MetaDataElem.Value.Rel.eq_of_ne_expr hne hval
    subst heq
    cases v with
    | expr x => exact absurd ⟨x, rfl⟩ hex
    | msg m => rfl
    | switch b => rfl
    | provenance p => rfl

/-- Mapping the expressions of the second of two related metadata arrays by a function that keeps
    `G`-related expressions related preserves the relation. -/
theorem MetaData.Rel.mapExprs_right {P : PureExpr} {G : P.Expr → P.Expr → Prop}
    {md md' : MetaData P} (g : P.Expr → P.Expr) (hg : ∀ p q, G p q → G p (g q))
    (h : MetaData.Rel G md md') : MetaData.Rel G md (md'.mapExprs g) := by
  rcases md with ⟨l⟩
  rcases md' with ⟨l'⟩
  unfold MetaData.Rel at h ⊢
  simp only [MetaData.mapExprs, MetaData.mapExprsM, bind_pure_comp, map_pure,
    List.mapM_toArray, Id.run_map, List.idRun_mapM, List.toList_toArray] at h ⊢
  refine List.Rel₂.map_right _ ?_ h
  intro e e' hee
  obtain ⟨hfld, hval⟩ := hee
  rcases e' with ⟨f', v'⟩
  rcases e with ⟨f, v⟩
  simp only at hfld hval
  subst hfld
  by_cases hex : ∃ x', v' = .expr x'
  · obtain ⟨x', hx'⟩ := hex
    subst hx'
    cases v with
    | expr x =>
      simp only [MetaDataElem.Value.Rel] at hval ⊢
      exact ⟨rfl, hg _ _ hval⟩
    | msg m => cases hval
    | switch b => cases hval
    | provenance p => cases hval
  · have hne : ∀ e, v' ≠ .expr e := fun e he => hex ⟨e, he⟩
    have heq : v = v' := MetaDataElem.Value.Rel.eq_of_ne_expr_right hne hval
    subst heq
    cases v with
    | expr x => exact absurd ⟨x, rfl⟩ hex
    | msg m => exact ⟨rfl, rfl⟩
    | switch b => exact ⟨rfl, rfl⟩
    | provenance p => exact ⟨rfl, rfl⟩

end -- public section

end Imperative
