/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.Typing.Spec.DatatypeTypeSpec
import all Strata.Languages.Core.Typing.Spec.DatatypeTypeSpec
import all Strata.DL.Lambda.TypeFactory
import Strata.Util.ListUtilsProps

/-! ## Datatype block compatibility

Key theorem: `MutualBlockTyCompat.generatedFuncNames_eq` (compatible blocks generate the same
function names). -/

namespace Core
namespace TypeSpec

open Lambda

public section

/-- A resolved block compatible with a source block generates the same function names. -/
theorem MutualBlockTyCompat.generatedFuncNames_eq
    {Γ : TContext Unit} {block_r block : List (LDatatype Unit)}
    (h : MutualBlockTyCompat Γ block_r block) :
    MutualDatatype.generatedFuncNames block_r = MutualDatatype.generatedFuncNames block := by
  have hblock : ∀ {γ : Type} (f : LDatatype Unit → List γ),
      (∀ d_r d, DatatypeTyCompat Γ d_r d → f d_r = f d) →
      block_r.flatMap f = block.flatMap f := by
    intro γ f hf
    simp only [List.flatMap_def]
    rw [List.Rel₂.map_eq hf h]
  have hconstrs : ∀ {γ : Type} {d_r d : LDatatype Unit} (f : LConstr Unit → List γ),
      DatatypeTyCompat Γ d_r d →
      (∀ c_r c, ConstrTyCompat Γ c_r c → f c_r = f c) →
      d_r.constrs.flatMap f = d.constrs.flatMap f := by
    intro γ d_r d f hd hf
    simp only [List.flatMap_def]
    rw [List.Rel₂.map_eq hf hd.2.2]
  have hargs : ∀ {c_r c : LConstr Unit} (f : Identifier Unit → String),
      ConstrTyCompat Γ c_r c →
      c_r.args.map (fun arg => f arg.1) = c.args.map (fun arg => f arg.1) := by
    intro c_r c f hc
    exact List.Rel₂.map_eq (fun _ _ hp => by rw [hp.1]) hc.2.2
  have helim : block_r.map (fun d => (elimFuncName d).name) =
      block.map (fun d => (elimFuncName d).name) :=
    List.Rel₂.map_eq (fun _ _ hd => by simp only [elimFuncName, hd.1]) h
  have hctor : block_r.flatMap (fun d => d.constrs.map (fun c => c.name.name)) =
      block.flatMap (fun d => d.constrs.map (fun c => c.name.name)) :=
    hblock _ (fun _ _ hd => List.Rel₂.map_eq (fun _ _ hc => by rw [hc.1]) hd.2.2)
  have htester : block_r.flatMap (fun d => d.constrs.map (fun c => c.testerName)) =
      block.flatMap (fun d => d.constrs.map (fun c => c.testerName)) :=
    hblock _ (fun _ _ hd => List.Rel₂.map_eq (fun _ _ hc => hc.2.1) hd.2.2)
  have hdestr : ∀ {d_r d : LDatatype Unit}, DatatypeTyCompat Γ d_r d →
      ∀ n, destructorFuncName d_r n = destructorFuncName d n := by
    intro d_r d hd n
    simp only [destructorFuncName, hd.1]
  have hdes : ∀ g : LDatatype Unit → Identifier Unit → String,
      (∀ {d_r d : LDatatype Unit}, DatatypeTyCompat Γ d_r d → ∀ n, g d_r n = g d n) →
      block_r.flatMap (fun d => d.constrs.flatMap (fun c => c.args.map (fun a => g d a.1))) =
        block.flatMap (fun d => d.constrs.flatMap (fun c => c.args.map (fun a => g d a.1))) := by
    intro g hg
    refine hblock _ (fun d_r d hd => ?_)
    simp only [hg hd]
    exact hconstrs _ hd (fun _ _ hc => hargs _ hc)
  have hunsafe : ∀ {d_r d : LDatatype Unit}, DatatypeTyCompat Γ d_r d →
      ∀ n, unsafeDestructorFuncName d_r n = unsafeDestructorFuncName d n := by
    intro d_r d hd n
    simp only [unsafeDestructorFuncName, hdestr hd]
  unfold MutualDatatype.generatedFuncNames
  rw [helim, hctor, htester, hdes _ hdestr, hdes _ hunsafe]

end -- public section

end TypeSpec
end Core
