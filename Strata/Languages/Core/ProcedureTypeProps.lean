/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Languages.Core.WF
public import Strata.Languages.Core.ProcedureType
public import Strata.Util.ExceptProps
import Strata.Util.ListUtilsProps
import Strata.Util.ListMapProps
import all Strata.DL.Imperative.CFG
import all Strata.Languages.Core.ProcedureType
import Strata.Languages.Core.IdentifiersProps
import Strata.Util.Tactics
public import Strata.Languages.Core.CmdType
public import Strata.Languages.Core.StatementType
import Strata.Languages.Core.Typing.Props.CmdTypeProps
import all Strata.Languages.Core.StatementType
import all Strata.Languages.Core.TypeSkolem
import Strata.Languages.Core.Typing.Props.TypeSkolemProps
public import Strata.Languages.Core.ProcedureProps
import all Strata.Languages.Core.ProcedureProps
import all Strata.Languages.Core.Procedure
import all Strata.DL.Lambda.LExprTypeEnv

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

`CFG.typeCheck_blocksRel_aliases`: the CFG that `CFG.typeCheck` returns has the input's entry
and blocks in order with the same labels and targets; each block's metadata has the input's keys,
with each expression value related to the input's; each of its commands is a checked
input command with a type substitution applied, and each of its branch guards is a resolved
input guard with a type substitution applied. `CFG.typeCheck_cmdsRel` is its commands-only
form: any property that checked commands keep carries over to the returned CFG.

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
private theorem checkParamNames_ioNotOld {proc : Procedure} {sourceLoc : FileRange} {u : Unit}
    (h : checkParamNames proc sourceLoc = .ok u) :
    ∀ id ∈ proc.header.inputs.keys ++ proc.header.outputs.keys,
      ∀ x, id ≠ CoreIdent.mkOld x := by
  intro id hid x heq
  unfold checkParamNames at h
  split at h
  · contradiction
  · rename_i hnone
    have hnot := List.find?_eq_none.mp hnone id hid
    exact hnot ((isOldIdent_iff_exists_mkOld id).2 ⟨x, heq⟩)

/-- Renaming a procedure's reserved type parameters keeps its parameter names. -/
private theorem renameReservedTypeArgs_paramKeys (avoid : Unit → List String)
    (proc : Procedure) (annot : Unit → List Lambda.LMonoTy) :
    (proc.renameReservedTypeArgs avoid annot).header.inputs.keys ++
        (proc.renameReservedTypeArgs avoid annot).header.outputs.keys =
      proc.header.inputs.keys ++ proc.header.outputs.keys := by
  unfold Procedure.renameReservedTypeArgs
  rcases renameReservedWith_cases proc.header.typeArgs
      (fun u => proc.mentionedTyVarsIn (annot u) ++ avoid u) proc.renameTypeArgs proc with
    ⟨heq, -⟩ | heq
  · rw [heq]
  · rw [heq]
    simp only [Procedure.renameTypeArgs, Procedure.mapTys, ListMap.keys_map_values]

/-- No parameter of a procedure that passes the checker proper (`typeCheckCore`) is named
    `old x`. -/
theorem typeCheckCore_ioNotOld
    (h : typeCheckCore scope progSigs C Env p proc md tyNames = .ok r) :
    ∀ id ∈ proc.header.inputs.keys ++ proc.header.outputs.keys,
      ∀ x, id ≠ CoreIdent.mkOld x := by
  unfold typeCheckCore at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  elim_err h
  elim_err h
  elim_err h with _ hold
  exact checkParamNames_ioNotOld hold

/-- A procedure that passes the checker proper (`typeCheckCore`) has no parameter named
    `old g` for an in-out parameter `g`. -/
theorem typeCheckCore_oldNamesFresh
    (h : typeCheckCore scope progSigs C Env p proc md tyNames = .ok r) :
    proc.header.oldNamesFresh :=
  fun g _ hmem => typeCheckCore_ioNotOld h _ hmem g.name rfl

/-- A procedure `typeCheckIn` accepts passes the checker proper (`typeCheckCore`) after its
    reserved type parameters are renamed, with rigid constants avoiding the type names the
    procedure mentions. -/
theorem typeCheckIn_core_ok (h : typeCheckIn scope progSigs C Env p proc md = .ok r) :
    typeCheckCore scope progSigs C Env p
      (proc.renameReservedTypeArgs (fun _ => Statement.substTyVars Env ++ scopeTyVars C Env)
        fun _ => procAnnotTys proc) md (fun _ => procTyNames proc (procAnnotTys proc)) =
      .ok r := by
  unfold typeCheckIn at h
  obtain ⟨_, -, hcore⟩ := (Except.bind_is_ok _ _ _).mp h
  exact hcore

/-- A procedure `typeCheck` accepts passes the checker proper (`typeCheckCore`) after its
    reserved type parameters are renamed, with rigid constants avoiding the type names in scope,
    those of the procedure signatures of `p` and those the procedure mentions. -/
theorem typeCheck_core_ok (h : typeCheck C Env p proc md = .ok r) :
    typeCheckCore (scopeTyNameThunk C Env)
      (procSigTyNameThunk p) C Env p
      (proc.renameReservedTypeArgs (fun _ => Statement.substTyVars Env ++ scopeTyVars C Env)
        fun _ => procAnnotTys proc) md (fun _ => procTyNames proc (procAnnotTys proc)) =
      .ok r :=
  typeCheckIn_core_ok h

/-- No parameter of a procedure that passes type checking is named `old x`
    (`WF.WFProcedureProp.ioNotOld`). -/
theorem typeCheck_ioNotOld
    (h : typeCheck C Env p proc md = .ok r) :
    ∀ id ∈ proc.header.inputs.keys ++ proc.header.outputs.keys,
      ∀ x, id ≠ CoreIdent.mkOld x := by
  rw [← renameReservedTypeArgs_paramKeys]
  exact typeCheckCore_ioNotOld (typeCheck_core_ok h)

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
  obtain ⟨-, hrun⟩ := Except.seq_guard_ok_iff.mp hrun
  obtain ⟨hnl, -⟩ := Except.seq_guard_ok_iff.mp hrun
  exact ⟨checkUniqueLabels_sound hu, checkEntryExists_sound he,
    checkTargetLabels_sound ht,
    checkBlockInitsNodup_sound hbn, checkDomScoped_sound hds,
    checkInitsIncomparable_sound hic, checkNoLoopInits_sound hnl⟩

/-! ### Loops of the CFG checker -/

/-- One step of a successful `for` loop over a nonempty list: the body succeeds on the head, and
    either stops there or the loop over the tail succeeds from the new state. -/
private theorem forIn_cons_ok_inv {α σ ε} {a : α} {as : List α} {init res : σ}
    {f : α → σ → Except ε (ForInStep σ)}
    (h : forIn (a :: as) init f = .ok res) :
    ∃ r, f a init = .ok r ∧
      ((∃ b, r = .done b ∧ res = b) ∨ (∃ b, r = .yield b ∧ forIn as b f = .ok res)) := by
  rw [List.forIn_cons, Except.bind_is_ok] at h
  obtain ⟨r, hr, h⟩ := h
  refine ⟨r, hr, ?_⟩
  cases r with
  | done b => exact Or.inl ⟨b, rfl, (Except.ok.inj h).symm⟩
  | yield b => exact Or.inr ⟨b, rfl, h⟩

/-- A loop over labeled items whose body only inserts an entry under the current item's label
    leaves the entry of any label outside the list unchanged. -/
private theorem forIn_insert_other {β γ σ ε}
    (f : String × β → Std.HashMap String γ × σ → Except ε (ForInStep (Std.HashMap String γ × σ)))
    (hf : ∀ x s r, f x s = .ok r → ∃ g s', r = .yield (s.1.insert x.1 g, s')) :
    ∀ (xs : List (String × β)) (init res : Std.HashMap String γ × σ) (k : String),
      k ∉ xs.map Prod.fst → forIn xs init f = .ok res → res.1[k]? = init.1[k]? := by
  intro xs
  induction xs with
  | nil =>
    intro init res k _ h
    rw [List.forIn_nil] at h
    cases h
    rfl
  | cons a as ih =>
    intro init res k hk h
    obtain ⟨r, hr, hcase⟩ := forIn_cons_ok_inv h
    obtain ⟨g, s', rfl⟩ := hf a init r hr
    rcases hcase with ⟨b, hb, -⟩ | ⟨b, hb, hrest⟩
    · cases hb
    · cases hb
      have hka : k ∉ as.map Prod.fst := fun hm => hk (List.mem_cons_of_mem _ hm)
      have hne : (a.1 == k) = false := by
        rw [beq_eq_false_iff_ne]
        intro heq
        exact hk (heq ▸ List.mem_cons_self)
      rw [ih _ res k hka hrest, Std.HashMap.getElem?_insert, hne]
      rfl

/-- A successful loop over items with distinct labels, whose body inserts under each item's label
    an entry related by `R` to the item, ends with every item's label mapped to such an entry. -/
private theorem forIn_insert_spec {β γ σ ε} (R : β → γ → Prop)
    (f : String × β → Std.HashMap String γ × σ → Except ε (ForInStep (Std.HashMap String γ × σ)))
    (hf : ∀ x s r, f x s = .ok r → ∃ g s', r = .yield (s.1.insert x.1 g, s') ∧ R x.2 g) :
    ∀ (xs : List (String × β)) (init res : Std.HashMap String γ × σ),
      (xs.map Prod.fst).Nodup → forIn xs init f = .ok res →
      ∀ x ∈ xs, ∃ g, res.1[x.1]? = some g ∧ R x.2 g := by
  have hf' : ∀ x s r, f x s = .ok r → ∃ g s', r = .yield (s.1.insert x.1 g, s') := by
    intro x s r h
    obtain ⟨g, s', hr, -⟩ := hf x s r h
    exact ⟨g, s', hr⟩
  intro xs
  induction xs with
  | nil => intro _ _ _ _ x hx; cases hx
  | cons a as ih =>
    intro init res hnd h x hx
    obtain ⟨r, hr, hcase⟩ := forIn_cons_ok_inv h
    obtain ⟨g, s', rfl, hR⟩ := hf a init r hr
    rcases hcase with ⟨b, hb, -⟩ | ⟨b, hb, hrest⟩
    · cases hb
    · cases hb
      rw [List.map_cons, List.nodup_cons] at hnd
      rcases List.mem_cons.mp hx with rfl | hx'
      · refine ⟨g, ?_, hR⟩
        rw [forIn_insert_other f hf' as _ res x.1 hnd.1 hrest, Std.HashMap.getElem?_insert_self]
      · exact ih _ res hnd.2 hrest x hx'

/-- Inserting the images of a list's entries leaves a key that no entry has unchanged. -/
private theorem foldl_insert_get_other {γ} (F : String → γ → γ) (k : String) :
    ∀ (L : List (String × γ)) (init : Std.HashMap String γ), k ∉ L.map Prod.fst →
      (L.foldl (fun (acc : Std.HashMap String γ) p => acc.insert p.1 (F p.1 p.2)) init)[k]?
        = init[k]? := by
  intro L
  induction L with
  | nil => intro init _; rfl
  | cons a as ih =>
    intro init hk
    have hne : (a.1 == k) = false := by
      rw [beq_eq_false_iff_ne]
      intro heq
      exact hk (heq ▸ List.mem_cons_self)
    rw [List.foldl_cons, ih _ (fun hm => hk (List.mem_cons_of_mem _ hm)),
      Std.HashMap.getElem?_insert, hne]
    rfl

/-- Inserting the images of the entries of a list with distinct keys maps each key to the image
    of its entry. -/
private theorem foldl_insert_get_mem {γ} (F : String → γ → γ) (k : String) (v : γ) :
    ∀ (L : List (String × γ)) (init : Std.HashMap String γ),
      L.Pairwise (fun a b => (a.1 == b.1) = false) → (k, v) ∈ L →
      (L.foldl (fun (acc : Std.HashMap String γ) p => acc.insert p.1 (F p.1 p.2)) init)[k]?
        = some (F k v) := by
  intro L
  induction L with
  | nil => intro _ _ hm; cases hm
  | cons a as ih =>
    intro init hpw hm
    rw [List.pairwise_cons] at hpw
    rw [List.foldl_cons]
    rcases List.mem_cons.mp hm with rfl | hm'
    · have hk : k ∉ as.map Prod.fst := by
        intro hmem
        obtain ⟨b, hb, hbk⟩ := List.mem_map.mp hmem
        have hfalse := hpw.1 b hb
        rw [hbk, beq_self_eq_true] at hfalse
        exact Bool.noConfusion hfalse
      rw [foldl_insert_get_other F k as _ hk, Std.HashMap.getElem?_insert_self]
    · exact ih _ hpw.2 hm'

/-- Rebuilding a map by inserting the image of each entry maps every key to the image of its
    entry. -/
private theorem fold_insert_get {γ} (m : Std.HashMap String γ) (F : String → γ → γ) (k : String)
    (v : γ) (h : m[k]? = some v) :
    (m.fold (fun (acc : Std.HashMap String γ) l b => acc.insert l (F l b)) ∅)[k]?
      = some (F k v) := by
  rw [Std.HashMap.fold_eq_foldl_toList]
  exact foldl_insert_get_mem F k v m.toList ∅ m.distinct_keys_toList
    (Std.HashMap.mem_toList_iff_getElem?_eq_some.mpr h)

/-- Looking up every item's label in a map that holds, under each label, an entry related by `R`
    to the item yields a list pointwise related to the items, with the same labels. -/
private theorem filterMap_get_rel₂ {β γ} (m : Std.HashMap String γ) (R : β → γ → Prop) :
    ∀ xs : List (String × β), (∀ x ∈ xs, ∃ g, m[x.1]? = some g ∧ R x.2 g) →
      List.Rel₂ (fun x y => x.1 = y.1 ∧ R x.2 y.2) xs
        (xs.filterMap fun x => Option.map (fun b => (x.1, b)) (m.get? x.1)) := by
  intro xs
  induction xs with
  | nil => intro _; exact List.Rel₂.nil
  | cons a as ih =>
    intro h
    obtain ⟨g, hg, hR⟩ := h a List.mem_cons_self
    rw [List.filterMap_cons]
    simp only [Std.HashMap.get?_eq_getElem?, hg, Option.map_some]
    exact List.Rel₂.cons ⟨rfl, hR⟩ (ih fun x hx => h x (List.mem_cons_of_mem _ hx))

/-- A successful loop whose body maps one element to a result and prepends it to the second
    component of the state ends with that component extended by results related by `Q` to the
    elements, in reverse order, when each step preserves an invariant `I` of the first component
    that holds initially. The final first component satisfies `I`. -/
private theorem forIn_collect_spec {σ ε α β} (I : σ → Prop) (Q : α → β → Prop)
    (f : α → σ × List β → Except ε (ForInStep (σ × List β)))
    (hf : ∀ x s r, I s.1 → f x s = .ok r →
      ∃ y s', r = .yield (s', y :: s.2) ∧ I s' ∧ Q x y) :
    ∀ (xs : List α) (init res : σ × List β), I init.1 → forIn xs init f = .ok res →
      I res.1 ∧ ∃ ys, res.2 = ys.reverse ++ init.2 ∧ List.Rel₂ Q xs ys := by
  intro xs
  induction xs with
  | nil =>
    intro init res hI h
    rw [List.forIn_nil] at h
    cases h
    exact ⟨hI, [], rfl, List.Rel₂.nil⟩
  | cons a as ih =>
    intro init res hI h
    obtain ⟨r, hr, hcase⟩ := forIn_cons_ok_inv h
    obtain ⟨y, s', rfl, hI', hQ⟩ := hf a init r hI hr
    rcases hcase with ⟨b, hb, -⟩ | ⟨b, hb, hrest⟩
    · cases hb
    · cases hb
      obtain ⟨hIres, ys, hys, hrel⟩ := ih _ res hI' hrest
      refine ⟨hIres, y :: ys, ?_, List.Rel₂.cons hQ hrel⟩
      rw [hys, List.reverse_cons, List.append_assoc]
      rfl

/-- The command loop of the CFG checker: each result it collects is the command checker's result
    on the command at the same position, so it is related to that command by any `Q` that holds
    between a command and its checked form in an environment with the alias list `A`. The loop
    starts in such an environment, and the command checker keeps the alias list. -/
private theorem forIn_typeCheckCmd_spec {C : Core.Expression.TyContext} {P : Program}
    (A : List Lambda.TypeAlias) (Q : Command → Command → Prop)
    (hQ : ∀ E E' x y, E.context.aliases = A → Statement.typeCheckCmd C E P x = .ok (y, E') →
      Q x y) :
    ∀ (xs : List Command) (init res : Lambda.TEnv Unit × List Command),
      init.1.context.aliases = A →
      forIn xs init (fun cmd (s : Lambda.TEnv Unit × List Command) => do
          let r ← Statement.typeCheckCmd C s.fst P cmd
          pure (ForInStep.yield (r.snd, r.fst :: s.snd))) = .ok res →
      ∃ ys, res.2 = ys.reverse ++ init.2 ∧ List.Rel₂ Q xs ys := by
  intro xs init res hA hloop
  refine (forIn_collect_spec (fun (E : Lambda.TEnv Unit) => E.context.aliases = A) Q _ ?_ xs init
    res hA hloop).2
  intro c st r hI h
  rw [Except.bind_is_ok] at h
  obtain ⟨⟨y, E'⟩, hy, h⟩ := h
  simp only [pure, Except.pure, Except.ok.injEq] at h
  subst h
  exact ⟨y, E', rfl, (Statement.typeCheckCmd_preserves_context _ _ _ _ _ _ hy).2.trans hI,
    hQ _ _ _ _ hI hy⟩

/-- Every state of a pure yielding loop satisfies an invariant that the initial state satisfies
    and each step preserves. -/
private theorem forIn_yield_inv {α σ ε : Type} (I : σ → Prop) (g : α → σ → σ)
    (hg : ∀ a s, I s → I (g a s)) :
    ∀ (xs : List α) (init res : σ), I init →
      forIn xs init (fun a s => (pure (ForInStep.yield (g a s)) : Except ε (ForInStep σ)))
        = .ok res → I res := by
  intro xs
  induction xs with
  | nil =>
    intro init res hI h
    rw [List.forIn_nil] at h
    cases h
    exact hI
  | cons a as ih =>
    intro init res hI h
    obtain ⟨r, hr, hcase⟩ := forIn_cons_ok_inv h
    simp only [pure, Except.pure, Except.ok.injEq] at hr
    subst hr
    rcases hcase with ⟨b, hb, -⟩ | ⟨b, hb, hrest⟩
    · cases hb
    · cases hb
      exact ih _ res (hg a init hI) hrest

/-- The CFG returned by a successful `CFG.typeCheck` run has the input's entry and blocks, with
    the same labels in the same order. Each of its commands is related by `Q` to the input command
    at the same position, and each branch guard by `G` to the input guard, with the same targets.
    Each block's metadata has the same keys, with expression values related by `G`
    to the input's. This holds for any `Q` that holds between a command and the command checker's
    result on it in an environment with the alias list of `Env`, and any `G` that holds between a
    guard or metadata expression and its resolution; both must survive applying a type
    substitution to the result. -/
theorem typeCheck_blocksRel_aliases {C : Core.Expression.TyContext} {Env : Core.Expression.TyEnv}
    {P : Program} {proc : Procedure} {cfg : DetCFG} {sourceLoc : Strata.FileRange}
    {res : DetCFG × Core.Expression.TyEnv} (Q : Command → Command → Prop)
    (G : Core.Expression.Expr → Core.Expression.Expr → Prop)
    (hQ : ∀ E E' x y, E.context.aliases = Env.context.aliases →
      Statement.typeCheckCmd C E P x = .ok (y, E') → Q x y)
    (hsubst : ∀ x y S, Q x y → Q x (Statement.Command.subst S y))
    (hG : ∀ E p pa E', SourceExpr.resolve C E p = .ok (pa, E') → G p pa.unresolved)
    (hGsubst : ∀ p q S, G p q → G p (Lambda.LExpr.applyTypeSubst q S))
    (hrun : CFG.typeCheck C Env P proc cfg sourceLoc = .ok res) :
    DetCFG.BlocksRel Q G cfg res.1 := by
  unfold CFG.typeCheck at hrun
  obtain ⟨hu, hrun⟩ := Except.seq_guard_ok_iff.mp hrun
  have huniq : (cfg.blocks.map Prod.fst).Nodup := checkUniqueLabels_sound hu
  iterate 9 (obtain ⟨-, hrun⟩ := Except.seq_guard_ok_iff.mp hrun)
  rw [Except.bind_is_ok] at hrun
  obtain ⟨r1, -, hrun⟩ := hrun
  obtain ⟨-, hrun⟩ := Except.seq_guard_ok_iff.mp hrun
  dsimp only at hrun
  rw [Except.bind_is_ok] at hrun
  obtain ⟨r2, -, hrun⟩ := hrun
  rw [Except.bind_is_ok] at hrun
  obtain ⟨r3, hr3, hrun⟩ := hrun
  have hscope : ∀ lbl, (r3.getD lbl Env.context).aliases = Env.context.aliases := by
    refine forIn_yield_inv (I := fun (m : Std.HashMap String (Lambda.TContext Unit)) =>
      ∀ lbl, (m.getD lbl Env.context).aliases = Env.context.aliases) _ ?_ _ _ _ ?_ hr3
    · intro lbl m hm k
      rw [Std.HashMap.getD_insert]
      split
      · split
        · rfl
        · split
          · exact hm _
          · exact hm _
      · exact hm k
    · intro lbl
      simp only [Std.HashMap.getD_empty]
  rw [Except.bind_is_ok] at hrun
  obtain ⟨r4, hloop, hrun⟩ := hrun
  simp only [pure, Except.pure, Except.ok.injEq] at hrun
  subst hrun
  have hsubstRel : ∀ (S : Lambda.Subst) {xs ys : List Command}, List.Rel₂ Q xs ys →
      List.Rel₂ Q xs (ys.map (Statement.Command.subst S)) :=
    fun S => List.Rel₂.map_right _ (fun x y hxy => hsubst x y S hxy)
  have hmain := forIn_insert_spec (fun (blk g : Imperative.DetBlock String Command Expression) =>
      List.Rel₂ Q blk.cmds g.cmds ∧ DetTransferRel G blk.transfer g.transfer ∧
        Imperative.MetaData.Rel G blk.md g.md) _ ?hbody
    cfg.blocks _ r4 huniq hloop
  case hbody =>
    intro x s r h
    -- The block's metadata is checked first, in the block's scope, before its commands.
    rw [Except.bind_is_ok] at h
    obtain ⟨s0, hmdloop, h⟩ := h
    rw [← Array.forIn_toList] at hmdloop
    have hmdSpec := forIn_collect_spec (fun (E : Lambda.TEnv Unit) =>
        E.context.aliases = Env.context.aliases)
      (fun (e y : Imperative.MetaDataElem Expression) =>
        e.fld = y.fld ∧ Imperative.MetaDataElem.Value.Rel G e.value y.value) _ ?hmdbody
      x.2.md.toList _ s0 ?hmdstart hmdloop
    case hmdstart =>
      dsimp only
      split
      · exact hscope x.1
      · rfl
    case hmdbody =>
      intro elem st r hI hr
      rcases elem with ⟨fld, value⟩
      cases value with
      | expr e =>
        rw [Except.bind_is_ok] at hr
        obtain ⟨v, hv, hr⟩ := hr
        have hres : SourceExpr.resolve C st.fst e = .ok v :=
          Except.mapError_ok_h' (SourceExpr.orFreeVarError_eq_ok.mp (Except.mapError_ok_h' hv))
        have hctx := (SourceExpr.resolve_context_pop_equiv C st.fst v.snd e v.fst hres).2
        have hrel : Imperative.MetaDataElem.Value.Rel G (.expr e)
            (.expr (Lambda.LExpr.unresolved v.fst)) :=
          hG _ _ _ _ hres
        split at hr <;> split at hr <;> first
          | (rw [Except.bind_is_ok] at hr
             obtain ⟨b, -, hr⟩ := hr
             cases hr
             exact ⟨_, _, rfl, hctx.trans hI, rfl, hrel⟩)
          | (cases hr
             exact ⟨_, _, rfl, hctx.trans hI, rfl, hrel⟩)
      | _ =>
        simp only [pure, Except.pure, Except.ok.injEq] at hr
        subst hr
        refine ⟨_, _, rfl, hI, rfl, ?_⟩
        apply Imperative.MetaDataElem.Value.Rel.refl_of_ne_expr
        intro e hne
        cases hne
    obtain ⟨hs0aliases, zs, hzs, hmdrel⟩ := hmdSpec
    rw [List.append_nil] at hzs
    have hmdRel : Imperative.MetaData.Rel G x.2.md s0.2.reverse.toArray := by
      show List.Rel₂ _ x.2.md.toList s0.2.reverse.toArray.toList
      rw [List.toList_toArray, hzs, List.reverse_reverse]
      exact hmdrel
    rw [Except.bind_is_ok] at h
    obtain ⟨s1, hinner, h⟩ := h
    have hloopSpec := forIn_typeCheckCmd_spec Env.context.aliases Q hQ x.2.cmds _ s1 hs0aliases
      hinner
    obtain ⟨ys, hys, hrel⟩ := hloopSpec
    rw [List.append_nil] at hys
    have hrev : s1.2.reverse = ys := by rw [hys, List.reverse_reverse]
    simp only [bind, Except.bind, pure, Except.pure] at h
    cases htr : x.2.transfer with
    | condGoto p lt lf md =>
      rw [htr] at h
      dsimp only at h
      split at h
      · contradiction
      · rename_i v hv
        split at h
        · contradiction
        · rename_i v1 hv1
          have hres : SourceExpr.resolve C s1.fst p = .ok v :=
            SourceExpr.orFreeVarError_eq_ok.mp (Except.mapError_ok_h' hv)
          have hguard : G p v.fst.unresolved := hG _ _ _ _ hres
          split at h
          · cases h
            exact ⟨_, _, rfl, hrev ▸ hrel, ⟨hguard, rfl, rfl, rfl⟩, hmdRel⟩
          · cases h
            refine ⟨_, _, rfl, hrev ▸ hsubstRel _ hrel, ?_, ?_⟩
            · exact ⟨hGsubst _ _ _ hguard, rfl, rfl, rfl⟩
            · exact Imperative.MetaData.Rel.mapExprs_right _ (fun p q hpq => hGsubst p q _ hpq)
                hmdRel
    | finish md =>
      rw [htr] at h
      dsimp only at h
      split at h
      · cases h
        exact ⟨_, _, rfl, hrev ▸ hrel, rfl, hmdRel⟩
      · cases h
        exact ⟨_, _, rfl, hrev ▸ hsubstRel _ hrel, rfl,
          Imperative.MetaData.Rel.mapExprs_right _ (fun p q hpq => hGsubst p q _ hpq) hmdRel⟩
  refine ⟨rfl, filterMap_get_rel₂ _ (fun (blk g : Imperative.DetBlock String Command Expression) =>
      List.Rel₂ Q blk.cmds g.cmds ∧ DetTransferRel G blk.transfer g.transfer ∧
        Imperative.MetaData.Rel G blk.md g.md) cfg.blocks ?_⟩
  intro x hx
  obtain ⟨g0, hg0, hrel0⟩ := hmain x hx
  refine ⟨_, fold_insert_get _ _ x.1 g0 hg0, ?_⟩
  cases hr : (Imperative.CFG.reachableLabels cfg).contains x.fst
  · simp only [Bool.false_eq_true, ↓reduceIte]
    exact hrel0
  · simp only [↓reduceIte]
    obtain ⟨hc, ht, hm⟩ := hrel0
    refine ⟨hsubstRel _ hc, ?_,
      Imperative.MetaData.Rel.mapExprs_right _ (fun p q hpq => hGsubst p q _ hpq) hm⟩
    simp only [Statement.DetBlock.subst]
    cases htr : g0.transfer with
    | condGoto p' lt' lf' md' =>
      cases htx : x.2.transfer with
      | condGoto p lt lf md =>
        rw [htx, htr] at ht
        obtain ⟨hg, hlt, hlf, hmd⟩ := ht
        exact ⟨hGsubst _ _ _ hg, hlt, hlf, hmd⟩
      | finish md => rw [htx, htr] at ht; exact ht.elim
    | finish md' =>
      cases htx : x.2.transfer with
      | condGoto p lt lf md => rw [htx, htr] at ht; exact ht.elim
      | finish md => rw [htx, htr] at ht; exact ht

/-- The CFG returned by a successful `CFG.typeCheck` run has the input's blocks, with the same
    labels in the same order, and each of its commands is related by `Q` to the input command at
    the same position, for any `Q` that holds between a command and the command checker's result
    on it and survives applying a type substitution to that result. -/
theorem typeCheck_cmdsRel {C : Core.Expression.TyContext} {Env : Core.Expression.TyEnv}
    {P : Program} {proc : Procedure} {cfg : DetCFG} {sourceLoc : Strata.FileRange}
    {res : DetCFG × Core.Expression.TyEnv} (Q : Command → Command → Prop)
    (hQ : ∀ E E' x y, Statement.typeCheckCmd C E P x = .ok (y, E') → Q x y)
    (hsubst : ∀ x y S, Q x y → Q x (Statement.Command.subst S y))
    (hrun : CFG.typeCheck C Env P proc cfg sourceLoc = .ok res) :
    DetCFG.CmdsRel Q cfg res.1 := by
  have hb := typeCheck_blocksRel_aliases Q (fun _ _ => True) (fun E E' x y _ h => hQ E E' x y h)
    hsubst (fun _ _ _ _ _ => trivial)
    (fun _ _ _ _ => trivial) hrun
  exact List.Rel₂.imp (fun _ _ h => ⟨h.1, h.2.1⟩) hb.2

end CFG
end Core

end -- public section
