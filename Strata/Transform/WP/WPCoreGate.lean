/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.WP.WPCoreDefs
public import Strata.Transform.WP.WPOutSyntax
public import Strata.Transform.WP.WPProps
public import Strata.Transform.WP.WPCoreTyping

/-! # The initial-environment gate of the output of the WP phase

The output `w.lay` of the WP phase of a Core statement list `ss` satisfies the target gate
`BlockInitEnvWF (wpTgtParams params) w.lay ρ₀'` whenever `ss` satisfies the source gate at
`ρ₀`, the environments are related by `EntryRel`, and the output declares distinct names that
are declared by `ss` or fresh, declares only types declared by `ss`, the Boolean type or types
of free variables of `ss`, and references only operators of `ss` (`wp_gate`).

Key theorem: `wp_gate`. -/

namespace Core
namespace WP

open Imperative Imperative.BigStep Imperative.WP Core.Logic

public section

/-- **The target gate of the WP phase.**  The output `w.lay` of the WP phase of the list `ss` with
    free-variable types `tys` satisfies the initial-environment gate with the target parameters
    at `ρ₀'` when `ss` satisfies the syntactic precondition `WPPre`, the source gate holds at
    `ρ₀`, the environments are related by `EntryRel`, and:
    * the names `w.lay` declares are distinct, and each is declared by `ss` or is a fresh name
      that `inputAvoid G tys ss` does not avoid;
    * each type `w.lay` declares is declared by `ss`, is the Boolean type, or is the type in
      `tys` of a free variable of `ss`;
    * each operator `w.lay` references is referenced by `ss`;
    * `ss` is well typed under `tys` (`Statements.WellTyped`). -/
theorem wp_gate {G : IdSet Expression} {tys : Tys Expression} {ss : Statements}
    {w : WOut Expression} {params : InitEnvWFParams} {ρ₀ ρ₀' : Env Expression}
    (hw : wpEntry G tys ss = .ok w) (hpre : WPPre tys ss) (hrel : EntryRel tys ρ₀ ρ₀')
    (hwf : BlockInitEnvWF params ss ρ₀) (htyp : Statements.WellTyped (fun x => tys.get? x) ss)
    (hD : (Block.definedVars w.lay false).Nodup ∧ ∀ y ∈ Block.definedVars w.lay false,
      y ∈ Block.definedVars ss false ∨
        ∃ b k, y = freshName b k ∧ (inputAvoid G tys ss).contains y = false)
    (hT : ∀ ty ∈ Block.initTypes w.lay, ty ∈ Block.initTypes ss ∨ ty = HasBool.boolTy ∨
      ∃ x ∈ Block.freeVars ss, tys.get? x = some ty)
    (hO : ∀ o ∈ Block.getOps w.lay, o ∈ Block.getOps ss) :
    BlockInitEnvWF (wpTgtParams params) w.lay ρ₀' := by
  obtain ⟨rfl, hty, hfr⟩ := hrel
  obtain ⟨hfvS, hwfl, hcov⟩ := hpre
  have htree := (wpBody_shape hw).1
  have hfvw := wpEntry_fv hw hwfl
  have hsrc : ∀ x ∈ Block.freeVars ss, (ρ₀'.store x).isSome := fun x hx =>
    hwf.readWritesDefined x (Block.freeVars_sub_touched x hx) fun hd =>
      wfl_defs_not_mem hwfl x hd (hfvS x hx)
  have hund : ∀ n ∈ Block.definedVars w.lay false, (ρ₀'.store n).isNone := fun n hn =>
    (hD.2 n hn).elim (hwf.defsUndefined n) fun ⟨b, k, he, hc⟩ => by
      cases hs : ρ₀'.store n
      · rfl
      · have hm := hfr n (by simp [hs]) b k he
        grind [inputAvoid, AvoidSet.contains, IdSet.ofList]
  have hST : StoreHasTyping ρ₀'.factory ρ₀'.store (fvTyping tys ss) := fun x ty hx => by
    simp only [fvTyping] at hx
    split at hx
    · rename_i hxf
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (hsrc x hxf)
      exact ⟨v, hv, hty x (hfvS x hxf) (hfvS x hxf) ty hx v hv⟩
    · cases hx
  exact {
    toWellFormedSemanticEval := hwf.toWellFormedSemanticEval
    storeWellDefined := hwf.storeWellDefined
    readWritesDefined := fun n hn hnd =>
      hsrc n (hfvw n ((List.mem_append.1 (touched_sub_fv_defs htree n hn)).resolve_right hnd))
    defsUndefined := hund
    definedVarsNotReserved := fun _ _ _ _ _ h => nomatch h
    reservedFresh := fun _ _ _ _ _ h => nomatch h
    exitsNotReserved := by simp [Imperative.Block.labels_of_treeForm htree]
    defUseOk := defUse_of_treeForm htree (fun x hx => hsrc x (hfvw x hx)) hD.1
      (fun x hx => by simpa using hund x hx)
      (fun o ho => block_defUse_ops ss hwf.defUseOk o (hO o ho))
    factoryDeclared := hwf.factoryDeclared
    initTypesInhabited := fun ty hm => by
      rcases hT ty hm with h | rfl | ⟨x, hx, hg⟩
      · exact hwf.initTypesInhabited ty h
      · exact ⟨_, bool_valueOfTy (.inl rfl)⟩
      · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 (hsrc x hx)
        exact ⟨v, hty x (hfvS x hx) (hfvS x hx) ty hg v hv⟩
    fvarTypesOk := ⟨fvTyping tys ss, hST, (wpEntry_wellTyped hw ⟨hfvS, hwfl, hcov⟩ htyp).1.2.2⟩ }

end -- public section

end WP
end Core
