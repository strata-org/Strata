/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.WF
public import Strata.Languages.Core.ProcedureType
public import Strata.Util.ExceptProps
import Strata.Util.ListUtilsProps
import all Strata.DL.Imperative.CFG
import all Strata.Languages.Core.ProcedureType
import Strata.Languages.Core.IdentifiersProps

/-! # Well-formedness established by the CFG type checker

`CFG.typeCheck_establishes_wfcfg`: a successful `CFG.typeCheck` run establishes
`WF.WFCFGProp`. Each conjunct inverts one of the guards that run before the
per-block loop: the three structural conjuncts invert `checkUniqueLabels`,
`checkEntryExists` and `checkTargetLabels`; the scoping conjuncts invert
`checkBlockInitsNodup`, `checkDomScoped`, `checkInitsIncomparable` and
`checkNoLoopInits`.

The scoping conjuncts are stated over the same graph analyses the guards compute
(`computeDominators`, `cycleLabelsWith`, `reachableLabels`), so this theorem
holds whatever those analyses return. That they agree with path-based dominance,
cycles and reachability is not proved here (see the
`Strata.DL.Imperative.CFGDominators` module header).

`Procedure.typeCheck_ioNotOld`: no parameter of a procedure that passes `Procedure.typeCheck`
is named `old x` (the proposition of `WF.WFProcedureProp.ioNotOld`);
`Procedure.typeCheck_oldNamesFresh`: such a procedure satisfies
`Procedure.Header.oldNamesFresh`.
-/

public section

namespace Core
namespace Procedure

open Imperative.CFG (cycleLabelsWith)
open Imperative.CFG.Dom (dominates)
open Strata (FileRange)

/-- A successful `checkUniqueLabels` run means the CFG's block labels are all
distinct. -/
private theorem checkUniqueLabels_sound
    {procName : CoreIdent} {cfg : DetCFG} {sourceLoc : FileRange}
    (h : checkUniqueLabels procName cfg sourceLoc = .ok ()) :
    cfg.labels.Nodup := by
  unfold checkUniqueLabels at h
  have hc := (Except.ite_error_then_eq_ok.mp h).1
  exact List.nodup_of_nodupB (by simpa using hc)

/-- A successful `checkEntryExists` run means the entry label names an existing
block. -/
private theorem checkEntryExists_sound {procName : CoreIdent} {cfg : DetCFG} {sourceLoc : FileRange}
    (h : checkEntryExists procName cfg sourceLoc = .ok ()) :
    cfg.entry ∈ cfg.labels := by
  unfold checkEntryExists at h
  have hc := (Except.ite_error_then_eq_ok.mp h).1
  exact List.mem_of_elem_eq_true (by simpa using hc)

/-- A successful `checkTargetLabels` run means every transfer target names an
existing block. -/
private theorem checkTargetLabels_sound
    {procName : CoreIdent} {cfg : DetCFG} {sourceLoc : FileRange}
    (h : checkTargetLabels procName cfg sourceLoc = .ok ()) :
    ∀ lbl blk, (lbl, blk) ∈ cfg.blocks →
      ∀ t ∈ blk.transfer.targets, t ∈ cfg.labels := by
  unfold checkTargetLabels at h
  simp only at h
  obtain ⟨⟨⟩, h, -⟩ := (Except.bind_is_ok _ _ _).mp h
  -- Each loop body only yields or fails, so the success of the outer loop gives
  -- the success of each block's inner loop, and that gives each target's check.
  have hblocks := List.forIn_yield_ok_mem cfg.blocks _ _ ?hne h
  case hne =>
    intro x _ hx
    simp only [bind, Except.bind] at hx
    split at hx <;> simp_all [pure, Except.pure]
  intro lbl blk hmem t ht
  have hblk := hblocks (lbl, blk) hmem
  simp only [bind, Except.bind] at hblk
  split at hblk
  · simp at hblk
  · rename_i r hinner
    have htgts := List.forIn_yield_ok_mem blk.transfer.targets _ _ ?hne2 hinner
    case hne2 =>
      intro y _ hy
      split at hy <;> simp_all [pure, Except.pure]
    have ht' := htgts t ht
    split at ht'
    · simp at ht'
    · rename_i hc
      simp only [Bool.not_eq_true', Bool.not_eq_false] at hc
      rw [Std.HashSet.contains_ofList] at hc
      exact List.mem_of_elem_eq_true hc

/-- A local declared by a block's `init`s appears in `cfgInitDeclBlocks` paired
with that block's label. -/
private theorem mem_cfgInitDeclBlocks_of_blockInitVars
    {cfg : DetCFG} {lbl : String} {blk : Imperative.DetBlock String Command Expression}
    {x : Expression.Ident}
    (hmem : (lbl, blk) ∈ cfg.blocks) (hx : x ∈ WF.blockInitVars blk) :
    (x, lbl) ∈ cfgInitDeclBlocks cfg :=
  List.mem_flatMap.mpr ⟨(lbl, blk), hmem, List.mem_map.mpr ⟨x, hx, rfl⟩⟩

/-- An entry `(x, lbl)` in `cfgInitDeclBlocks cfg` comes from a block labelled
`lbl` that declares `x`. -/
private theorem blockInitVars_of_mem_cfgInitDeclBlocks
    {cfg : DetCFG} {x : Expression.Ident} {lbl : String}
    (h : (x, lbl) ∈ cfgInitDeclBlocks cfg) :
    ∃ blk, (lbl, blk) ∈ cfg.blocks ∧ x ∈ WF.blockInitVars blk := by
  obtain ⟨⟨l, blk⟩, hmem, hx⟩ := List.mem_flatMap.mp h
  obtain ⟨y, hy, hyx⟩ := List.mem_map.mp hx
  simp only [Prod.mk.injEq] at hyx
  obtain ⟨rfl, rfl⟩ := hyx
  exact ⟨blk, hmem, hy⟩

/-- A successful `checkBlockInitsNodup` run means no block declares the same
local more than once. -/
private theorem checkBlockInitsNodup_sound
    {procName : CoreIdent} {cfg : DetCFG} {sourceLoc : FileRange}
    (h : checkBlockInitsNodup procName cfg sourceLoc = .ok ()) :
    ∀ lbl blk, (lbl, blk) ∈ cfg.blocks → (WF.blockInitVars blk).Nodup := by
  unfold checkBlockInitsNodup at h
  have hb := (Except.ite_error_else_eq_ok.mp h).1
  simp only [blockInitsNodupB, List.all_eq_true] at hb
  intro lbl blk hmem
  exact List.nodup_of_nodupB (hb (lbl, blk) hmem)

/-- A successful `checkDomScoped` run means every CFG-local that a *reachable*
block reads or assigns is declared in a block that dominates it. -/
private theorem checkDomScoped_sound {procName : CoreIdent} {cfg : DetCFG} {sourceLoc : FileRange}
    (h : checkDomScoped cfg.computeDominators cfg.reachableLabels
      procName cfg sourceLoc = .ok ()) :
    ∀ Blbl Bblk, (Blbl, Bblk) ∈ cfg.blocks →
      cfg.isReachable Blbl = true →
      ∀ x ∈ WF.blockReadVars Bblk ++ WF.blockSetTargets Bblk,
        x ∈ WF.cfgInitVars cfg →
          ∃ Dlbl Dblk, (Dlbl, Dblk) ∈ cfg.blocks ∧ x ∈ WF.blockInitVars Dblk ∧
            dominates cfg.computeDominators Dlbl Blbl = true := by
  unfold checkDomScoped at h
  have hb := (Except.ite_error_else_eq_ok.mp h).1
  simp only [domScopedB, List.all_eq_true] at hb
  intro Blbl Bblk hmem hreach x hx hinit
  -- `hreach` discharges the "unreachable blocks are vacuously fine" disjunct,
  -- leaving the per-local scoping fact for this block.
  rw [Imperative.CFG.isReachable] at hreach
  have hbb := hb (Blbl, Bblk) hmem
  rw [hreach, Bool.not_true, Bool.false_or] at hbb
  rw [List.all_eq_true] at hbb
  have hbx := hbb x hx
  rw [Bool.or_eq_true] at hbx
  rcases hbx with hne | hany
  · rw [Bool.not_eq_true', Std.HashSet.contains_ofList, List.contains_eq_mem,
      decide_eq_false_iff_not] at hne
    exact absurd hinit hne
  · simp only [List.any_eq_true] at hany
    obtain ⟨d, hd_mem, hddom⟩ := hany
    obtain ⟨Dblk, hDmem, hDinit⟩ :=
      blockInitVars_of_mem_cfgInitDeclBlocks (List.of_mem_groupValuesByKey hd_mem)
    exact ⟨d, Dblk, hDmem, hDinit, hddom⟩

/-- A successful `checkInitsIncomparable` run means any two distinct *reachable*
blocks that declare the same local do not dominate each other. -/
private theorem checkInitsIncomparable_sound
    {procName : CoreIdent} {cfg : DetCFG} {sourceLoc : FileRange}
    (h : checkInitsIncomparable cfg.computeDominators cfg.reachableLabels
      procName cfg sourceLoc = .ok ()) :
    ∀ D1 D2 B1 B2, (D1, B1) ∈ cfg.blocks → (D2, B2) ∈ cfg.blocks →
      cfg.isReachable D1 = true → cfg.isReachable D2 = true →
      D1 ≠ D2 → ∀ x, x ∈ WF.blockInitVars B1 → x ∈ WF.blockInitVars B2 →
        dominates cfg.computeDominators D1 D2 = false ∧
        dominates cfg.computeDominators D2 D1 = false := by
  unfold checkInitsIncomparable at h
  have hb := (Except.ite_error_else_eq_ok.mp h).1
  simp only [initsIncomparableB, List.all_eq_true] at hb
  intro D1 D2 B1 B2 hm1 hm2 hc1 hc2 hne x hx1 hx2
  have hp1 := mem_cfgInitDeclBlocks_of_blockInitVars hm1 hx1
  have hp2 := mem_cfgInitDeclBlocks_of_blockInitVars hm2 hx2
  have hg1 := List.mem_groupValuesByKey (keep := cfg.reachableLabels.contains) hp1 hc1
  have hg2 := List.mem_groupValuesByKey (keep := cfg.reachableLabels.contains) hp2 hc2
  -- The guard at declarer `(x, D2)` rules out `D1` dominating `D2`, and the
  -- guard at `(x, D1)` rules out `D2` dominating `D1`.
  have h12 := hb (x, D2) hp2
  have h21 := hb (x, D1) hp1
  simp only [Imperative.CFG.isReachable] at hc1 hc2
  simp only [hc1, hc2, Bool.not_true, Bool.false_or, List.all_eq_true] at h12 h21
  have hne' : D2 ≠ D1 := fun h => hne h.symm
  have a := h12 D1 hg1
  have b := h21 D2 hg2
  simp only [Bool.or_eq_true, beq_iff_eq, hne, hne', false_or,
    Bool.not_eq_true'] at a b
  exact ⟨a, b⟩

/-- A successful `checkNoLoopInits` run means no *reachable* block that declares
a local lies on a cycle. -/
private theorem checkNoLoopInits_sound
    {procName : CoreIdent} {cfg : DetCFG} {sourceLoc : FileRange}
    (h : checkNoLoopInits procName cfg.reachableLabels
      (cycleLabelsWith cfg.succMap cfg.labels) cfg sourceLoc = .ok ()) :
    ∀ lbl blk, (lbl, blk) ∈ cfg.blocks → cfg.isReachable lbl = true →
      WF.blockInitVars blk ≠ [] →
        (cycleLabelsWith cfg.succMap cfg.labels).contains lbl = false := by
  unfold checkNoLoopInits at h
  have hb := (Except.ite_error_else_eq_ok.mp h).1
  simp only [noLoopInitsB, List.all_eq_true] at hb
  intro lbl blk hmem hr hne
  have hl := hb (lbl, blk) hmem
  simp only [Imperative.CFG.isReachable] at hr
  have hemp : (WF.blockInitVars blk).isEmpty = false := by
    cases hv : WF.blockInitVars blk with
    | nil => exact absurd hv hne
    | cons _ _ => rfl
  simp only [hemp, hr, Bool.true_and, Bool.false_or, Bool.not_eq_true'] at hl
  exact hl

/-- No parameter of a procedure that passes `checkParamNames` is named `old x`. -/
private theorem checkParamNames_ioNotOld {proc : Procedure} {sourceLoc : FileRange}
    (h : checkParamNames proc sourceLoc = .ok ()) :
    ∀ id ∈ proc.header.inputs.keys ++ proc.header.outputs.keys,
      ∀ x, id ≠ CoreIdent.mkOld x := by
  intro id hid x heq
  unfold checkParamNames at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  split at h
  · contradiction
  · rename_i hnone
    have hnot := List.find?_eq_none.mp hnone id hid
    exact hnot ((isOldIdent_iff_exists_mkOld id).2 ⟨x, heq⟩)

/-- No parameter of a procedure that passes type checking is named `old x`
    (`WF.WFProcedureProp.ioNotOld`). -/
theorem typeCheck_ioNotOld
    (h : typeCheck C Env p proc md = .ok r) :
    ∀ id ∈ proc.header.inputs.keys ++ proc.header.outputs.keys,
      ∀ x, id ≠ CoreIdent.mkOld x := by
  unfold typeCheck at h
  simp only [bind, Except.bind] at h
  split at h
  · contradiction
  · rename_i hc
    exact checkParamNames_ioNotOld hc

/-- A procedure that passes type checking has no parameter named `old g` for an in-out
    parameter `g`. -/
theorem typeCheck_oldNamesFresh
    (h : typeCheck C Env p proc md = .ok r) : proc.header.oldNamesFresh :=
  fun g _ hmem => typeCheck_ioNotOld h _ hmem g.name rfl

end Procedure

namespace CFG

open Procedure

/-- A CFG body accepted by `CFG.typeCheck` satisfies `WFCFGProp`: its block labels
are distinct, the entry and every branch target name existing blocks, and no
block declares a local twice. Moreover, with "dominates", "on a cycle" and
"reachable" meaning what `computeDominators`, `cycleLabelsWith` and
`reachableLabels` compute (not proved to match the path-based notions): every
local that some block declares and that a reachable block reads or assigns has
a declaring block that dominates it (possibly the same block, even if the use
comes first), two distinct reachable blocks declaring the same local do not
dominate each other, and no reachable declaring block is on a cycle. It makes
no claim about types, about name collisions with the header or globals, about
`checkInitsNotReachable`, or about unreachable blocks.

The property is stated for the input `cfg`, not for the annotated CFG that
`CFG.typeCheck` returns and `Procedure.typeCheck` stores as the procedure body, so by itself
it does not establish `WFProcedureProp.wfcfg` for the stored body. Carrying it
over needs a proof that type checking a command preserves the variables it
reads, assigns and declares, which no lemma provides yet for either body kind. -/
theorem typeCheck_establishes_wfcfg
    {C : Core.Expression.TyContext} {Env : Core.Expression.TyEnv}
    {P : Program} {proc : Procedure} {cfg : DetCFG} {sourceLoc : Strata.FileRange}
    {res : DetCFG × Core.Expression.TyEnv}
    (hrun : CFG.typeCheck C Env P proc cfg sourceLoc = .ok res) :
    WF.WFCFGProp P proc cfg := by
  unfold CFG.typeCheck at hrun
  obtain ⟨hu, hrun⟩ := Except.seq_guard_ok_iff.mp hrun
  obtain ⟨he, hrun⟩ := Except.seq_guard_ok_iff.mp hrun
  obtain ⟨ht, hrun⟩ := Except.seq_guard_ok_iff.mp hrun
  obtain ⟨hbn, hrun⟩ := Except.seq_guard_ok_iff.mp hrun
  obtain ⟨hic, hrun⟩ := Except.seq_guard_ok_iff.mp hrun
  obtain ⟨hds, hrun⟩ := Except.seq_guard_ok_iff.mp hrun
  obtain ⟨hnl, -⟩ := Except.seq_guard_ok_iff.mp hrun
  exact ⟨checkUniqueLabels_sound hu, checkEntryExists_sound he,
    checkTargetLabels_sound ht,
    checkBlockInitsNodup_sound hbn, checkDomScoped_sound hds,
    checkInitsIncomparable_sound hic, checkNoLoopInits_sound hnl⟩

end CFG
end Core

end -- public section
