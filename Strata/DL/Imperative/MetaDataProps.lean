/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.DL.Imperative.MetaData
import all Strata.DL.Imperative.MetaData

/-! # Properties of metadata

- `MetaData.mapExprs_empty`: mapping the expressions of the empty metadata gives the empty
  metadata.
- `MetaData.mapExprs_id`: mapping the expressions of metadata by the identity changes nothing.
- `MetaData.exprs_mapExprs`: the expressions of mapped metadata are the mapped expressions.
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

end -- public section

end Imperative
