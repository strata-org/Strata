/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.WP.WPOverEffects
public import Strata.DL.Imperative.CmdCallFormals
import Strata.DL.Imperative.StmtProps
import Strata.Transform.WP.WPOverEmit
import Strata.Util.ExceptProps

/-! # The names the WP output declares

The guarded program of the WP phase declares every name at most once, and every name it declares
is a loop-free local of the input or a fresh name outside the names the phase avoids
(`wpEntry_decls`).

The proof follows the names the walk outputs declare (`wDecls`): a walk from `st` to `st'` of a
fragment with the loop-free locals `I` declares each name once, each a name the walk draws, a
local of `I` recorded as declared by the walk, or a renaming at `st`, and none a renaming at `st'`
(`DeclW`).  These facts compose along consecutive walks whose state changes keep the avoided
names and the recorded declarations and add only drawn renamings (`DeclStep`), from a state whose
renamings are drawn names (`NmOK`) (`DeclW.seq`), and hold for every walk of a statement or a list
(`wpStmt_declW`, `wpList_declW`).  Resolution, merging of obligation runs and nesting declare a
sublist of the names the items declare (`emit_decls_sublist`).

Key definitions: `DeclStep`, `DeclW`, `NmOK`.

Key theorems: `DeclW.seq`, `wpStmt_declW`, `wpList_declW`, `emit_decls_sublist`,
`wpEntry_decls`. -/

namespace Imperative
namespace WP

open Strata.Util

open BigStep

public section

variable {P : PureExpr} [iDE : DecidableEq P.Ident] [iBE : BEq P.Ident] [iLB : LawfulBEq P.Ident]
  [iHB : HasBool P] [iHF : HasFvar P] [iSF : HasSubstFvar P] [iHI : HasIdent P]
  [iHa : Hashable P.Ident] [iHFs : HasFvars P] [iWL : WPLang P]

/-! ## Declarations of resolved items -/

/-- The names the flat items declare, at any depth. -/
private def itemDecls : List (Item P) → List P.Ident
  | [] => []
  | .plain s :: rest => Stmt.definedVars s false ++ itemDecls rest
  | .obls _ cs :: rest => Block.definedVars cs false ++ itemDecls rest
  | .branch t e :: rest => itemDecls t ++ itemDecls e ++ itemDecls rest

omit iLB iHI in
/-- The items of a resolution declare the names the resolved items declare. -/
private theorem resolveItems_decls {T : Std.HashMap P.Ident P.Ty}
    {Y : Std.HashMap P.Ident P.Ident} :
    ∀ (l : List (WItem P)) {ir : List (Item P)}, resolveItems T Y l = .ok ir →
      itemDecls ir = wDecls l
  | [], ir, h => by cases h; simp [itemDecls, wDecls]
  | it :: rest, ir, h => by
    obtain ⟨ia, il, ha, hl, rfl⟩ := resolveItems_cons_ok h
    have ih := resolveItems_decls rest hl
    cases it with
    | branch t e =>
      simp only [resolveItem, Except.bind_is_ok, Except.pure_is_ok] at ha
      obtain ⟨rt, ht, re, he, rfl⟩ := ha
      simp [itemDecls, wDecls, resolveItems_decls t ht, resolveItems_decls e he, ih]
    | obls r cs =>
      simp only [resolveItem, Except.bind_is_ok, Except.pure_is_ok] at ha
      obtain ⟨cs', hcs, rfl⟩ := ha
      have h0 : Block.definedVars cs' false = [] := by
        clear h hl ih
        induction cs generalizing cs' with
        | nil => cases hcs; rfl
        | cons c cs ihc =>
          simp only [List.mapM_cons, Except.bind_is_ok, Except.pure_is_ok] at hcs
          obtain ⟨c', hc, cs'', hcs, rfl⟩ := hcs
          obtain ⟨e, -, rfl⟩ := hc
          cases c.1 <;> simp [ihc _ hcs, HasVarsImp.definedVars, CmdExt.definedVars,
            Cmd.definedVars]
      simp [itemDecls, wDecls, h0, ih]
    | init x ty e =>
      obtain ⟨ty', v, rfl⟩ : ∃ ty' v, ia = .plain (mkInit x ty' v) := by
        cases ty <;> simp only [resolveItem, Except.bind_is_ok, Except.pure_is_ok] at ha <;>
          grind
      simp [itemDecls, wDecls, ih, mkInit, HasVarsImp.definedVars, CmdExt.definedVars,
        Cmd.definedVars]
    | set x e =>
      simp only [resolveItem, Except.bind_is_ok, Except.pure_is_ok] at ha
      obtain ⟨v, -, rfl⟩ := ha
      simp [itemDecls, wDecls, ih, HasVarsImp.definedVars, CmdExt.definedVars, Cmd.definedVars]
    | assume l e md =>
      simp only [resolveItem, Except.bind_is_ok, Except.pure_is_ok] at ha
      obtain ⟨v, -, rfl⟩ := ha
      simp [itemDecls, wDecls, ih, HasVarsImp.definedVars, CmdExt.definedVars, Cmd.definedVars]

omit iBE iLB iHB iSF iHI iHa iWL in
/-- Merging adjacent obligation runs keeps the declared names. -/
private theorem itemDecls_mergeObls : ∀ l : List (Item P), itemDecls (mergeObls l) = itemDecls l
  | [] => by simp [mergeObls, itemDecls]
  | .plain s :: rest => by simp [mergeObls, itemDecls, itemDecls_mergeObls rest]
  | .branch t e :: rest => by
    simp [mergeObls, itemDecls, itemDecls_mergeObls t, itemDecls_mergeObls e,
      itemDecls_mergeObls rest]
  | .obls r cs :: rest => by
    have ih := itemDecls_mergeObls rest
    simp only [mergeObls]
    split
    · rename_i r' cs' rest' heq
      rw [heq] at ih
      split <;> simp [itemDecls, Block.definedVars_append, ← ih]
    · simp [itemDecls, ih]

omit iBE iLB iHI iHa in
mutual
/-- Nesting flat items declares a sublist of the names they declare. -/
private theorem nest_decls :
    ∀ l : List (Item P), (Block.definedVars (nest l) false).Sublist (itemDecls l)
  | [] => by simp [nest, itemDecls]
  | it :: rest => by
    rw [nest]
    exact nestCons_decls it rest (nest rest) (nest_decls rest)
/-- `nestCons it rest nr` declares a sublist of the names `it :: rest` declares when `nr` declares
    a sublist of those of `rest`. -/
private theorem nestCons_decls : ∀ (it : Item P) (rest : List (Item P)) (nr : PStmts P),
    (Block.definedVars nr false).Sublist (itemDecls rest) →
      (Block.definedVars (nestCons it rest nr) false).Sublist (itemDecls (it :: rest))
  | .plain s, rest, nr, h => by
    simp only [nestCons, itemDecls]
    split
    · simpa using h
    · simp
  | .obls r cs, rest, nr, h => by
    have hr : Block.definedVars (reachPre r) false = [] := by
      rcases r with _ | ((_ | _ | _ | _)) <;> simp [reachPre, HasVarsImp.definedVars,
        CmdExt.definedVars, Cmd.definedVars]
    simp only [nestCons, itemDecls]
    split
    · simpa [Block.definedVars_append, hr] using h
    · simp [Block.definedVars_append, hr]
  | .branch t e, rest, nr, _ => by
    have ht := nest_decls t
    have he := nest_decls e
    simp only [nestCons, itemDecls]
    split
    · exact (he.trans (List.sublist_append_right _ _)).trans (List.sublist_append_left _ _)
    · exact (ht.trans (List.sublist_append_left _ _)).trans (List.sublist_append_left _ _)
    · simpa using ((ht.append he).trans (List.sublist_append_left _ _))
end

omit iLB iHI in
/-- The guarded program `emit` builds from items declares a sublist of the names the items
    declare. -/
theorem emit_decls_sublist {T : Std.HashMap P.Ident P.Ty} {Y : Std.HashMap P.Ident P.Ident}
    {s : Rope (WItem P)} {lay : PStmts P} (h : emit T Y s = .ok lay) :
    (Block.definedVars lay false).Sublist (wDecls s.toList) := by
  simp only [emit, Except.bind_is_ok, Except.pure_is_ok] at h
  obtain ⟨ir, hr, rfl⟩ := h
  rw [← resolveItems_decls _ hr, ← itemDecls_mergeObls]
  exact nest_decls _

/-! ## Declaration facts of walks -/

/-- How a walk from `st` to `st'` changes the parts of the state the declared names depend on:
    the avoided names are kept, the counter does not decrease, the names recorded as declared
    stay recorded, and a renaming after it is one before it or a name drawn by the walk. -/
structure DeclStep (st st' : WSt P) : Prop where
  avoid : st'.avoid = st.avoid
  next : st.next ≤ st'.next
  taken : ∀ y : P.Ident, st.taken.contains y = true → st'.taken.contains y = true
  nm : ∀ z n : P.Ident, st'.nm[z]? = some n → st.nm[z]? = some n ∨ NewIn st st' n

/-- The declaration facts of a walk from `st` to `st'` of a fragment with the loop-free locals
    `I`, for the list `D` of the names its output declares: each name occurs at most once in
    `D`; each is drawn by the walk, or a local of `I` recorded as declared after the walk and not
    before it, or a renaming before the walk; none is a renaming after the walk. -/
structure DeclW (I : List P.Ident) (st st' : WSt P) (D : List P.Ident) : Prop where
  once : ∀ y : P.Ident, D.count y ≤ 1
  cls : ∀ y ∈ D, NewIn st st' y ∨
    (y ∈ I ∧ st.taken.contains y = false ∧ st'.taken.contains y = true) ∨
    ∃ z : P.Ident, st.nm[z]? = some y
  notNm : ∀ y ∈ D, ∀ z : P.Ident, st'.nm[z]? ≠ some y

section
omit iWL
variable {I I1 I2 D D1 D2 : List P.Ident} {st st1 st2 : WSt P}
  {y : P.Ident}

/-- `DeclStep` steps compose. -/
private theorem DeclStep.trans (h1 : DeclStep st st1) (h2 : DeclStep st1 st2) :
    DeclStep st st2 where
  avoid := h2.avoid.trans h1.avoid
  next := Nat.le_trans h1.next h2.next
  taken y hy := h2.taken y (h1.taken y hy)
  nm z n hn := (h2.nm z n hn).elim (fun h => (h1.nm z n h).imp_right (·.up h2.next))
    (.inr <| ·.widen h1.avoid h1.next (Nat.le_refl _))

/-- A `WalkCore` step to a well-formed state is a `DeclStep`. -/
private theorem DeclStep.of_core [LawfulHasIdent P] {Dc : List P.Ident} (h : WalkCore Dc st st1)
    (hw : WFSt st1) : DeclStep st st1 where
  avoid := h.avoid
  next := h.next
  taken := h.taken
  nm z n hn := (h.nm z n hn).imp_right fun ⟨b, j, e, ha, hj⟩ => by
    obtain ⟨-, b', j', e', hj', -⟩ := hw.nm_fresh z n hn
    exact ⟨b, j, e, ha, hj, freshName_counter_inj (e.symm.trans e') ▸ hj'⟩

/-- A step keeping the avoided names, the renamings and the names recorded as declared, with a
    counter that does not decrease, is a `DeclStep`. -/
private theorem DeclStep.of_eq (ha : st1.avoid = st.avoid) (hn : st.next ≤ st1.next)
    (ht : st1.taken = st.taken) (hnm : st1.nm = st.nm) : DeclStep st st1 :=
  ⟨ha, hn, fun _ h => ht ▸ h, fun _ _ h => .inl (hnm ▸ h)⟩

/-- A `DeclStep` after a step keeping the avoided names, the renamings and the names recorded as
    declared, with a counter that does not decrease, is a `DeclStep`. -/
private theorem DeclStep.eq_pre (S : DeclStep st1 st2) (ha : st1.avoid = st.avoid)
    (hn : st.next ≤ st1.next) (ht : st1.taken = st.taken) (hnm : st1.nm = st.nm) :
    DeclStep st st2 := (DeclStep.of_eq ha hn ht hnm).trans S

/-- No name is declared by an empty output. -/
private theorem DeclW.nil : DeclW I st st1 [] := ⟨fun _ => by simp, nofun, nofun⟩

/-- The declaration facts hold for any list declaring each name at most as often. -/
private theorem DeclW.sub (h : DeclW I st st1 D) {D' : List P.Ident}
    (hc : ∀ y, D'.count y ≤ D.count y) :
    DeclW I st st1 D' := by
  have hm : ∀ y ∈ D', y ∈ D := fun y hy =>
    List.count_pos_iff.1 (Nat.lt_of_lt_of_le (List.count_pos_iff.2 hy) (hc y))
  exact ⟨fun y => Nat.le_trans (hc y) (h.once y), fun y hy => h.cls y (hm y hy),
    fun y hy => h.notNm y (hm y hy)⟩

/-- The declaration facts hold for a larger list of locals. -/
private theorem DeclW.monoI (h : DeclW I st st1 D) {I' : List P.Ident} (hI : ∀ x ∈ I, x ∈ I') :
    DeclW I' st st1 D :=
  ⟨h.once, fun y hy => (h.cls y hy).imp_right (·.imp_left fun ⟨h1, h2⟩ => ⟨hI y h1, h2⟩),
    h.notNm⟩

/-- Every renaming of `st` is a fresh name with a counter below `st.next`, not avoided. -/
@[expose] def NmOK (st : WSt P) : Prop :=
  ∀ z m : P.Ident, st.nm[z]? = some m →
    ∃ b j, m = freshName b j ∧ j < st.next ∧ st.avoid.contains m = false

/-- A well-formed state has the renaming facts `NmOK`. -/
private theorem WFSt.nmOK (hw : WFSt st) : NmOK st := fun z m hz => (hw.nm_fresh z m hz).2

/-- A `DeclStep` keeps the renaming facts `NmOK`. -/
private theorem NmOK.step (h : NmOK st) (S : DeclStep st st1) : NmOK st1 := fun z m hz =>
  (S.nm z m hz).elim (fun h' => (h z m h').elim fun b ⟨j, e, hj, ha⟩ =>
      ⟨b, j, e, Nat.lt_of_lt_of_le hj S.next, S.avoid ▸ ha⟩)
    fun ⟨b, j, e, ha, _, hj⟩ => ⟨b, j, e, hj, S.avoid ▸ ha⟩

/-- A name a walk from `st` (with the renaming facts) to `st1` declares is not drawn from `st1`
    on. -/
private theorem DeclW.not_new [LawfulHasIdent P] (h : DeclW I st st1 D) (S : DeclStep st st1)
    (hw : NmOK st) (hI : ∀ x ∈ I, AvoidedIfFresh st x) (hy : y ∈ D) {s : WSt P}
    (hn : NewIn st1 s y) : False := by
  obtain ⟨b, j, rfl, ha, hj, -⟩ := hn
  rcases h.cls _ hy with h1 | ⟨h1, -⟩ | ⟨z, hz⟩
  · obtain ⟨b', j', e, -, -, hj'⟩ := h1
    exact absurd (freshName_counter_inj e) (by omega)
  · simp [S.avoid ▸ hI _ h1 b j rfl] at ha
  · obtain ⟨b', j', e, hj', -⟩ := hw z _ hz
    exact absurd (freshName_counter_inj e) (by have := S.next; omega)

/-- The declaration facts of two consecutive walks give those of the walk through both, for the
    names both outputs declare. -/
theorem DeclW.seq [LawfulHasIdent P] (S1 : DeclStep st st1) (S2 : DeclStep st1 st2)
    (hw : NmOK st) (hI : ∀ x ∈ I1 ++ I2, AvoidedIfFresh st x) (h1 : DeclW I1 st st1 D1)
    (h2 : DeclW I2 st1 st2 D2) : DeclW (I1 ++ I2) st st2 (D1 ++ D2) := by
  have hI1 : ∀ x ∈ I1, AvoidedIfFresh st x := fun x hx => hI x (List.mem_append_left _ hx)
  have hdis : ∀ y ∈ D1, y ∉ D2 := fun y hy1 hy2 => by
    rcases h2.cls y hy2 with h | ⟨hyI, ht, -⟩ | ⟨z, hz⟩
    · exact h1.not_new S1 hw hI1 hy1 h
    · rcases h1.cls y hy1 with ⟨b, j, rfl, ha, -⟩ | ⟨-, -, ht'⟩ | ⟨z, hz⟩
      · simp [hI _ (List.mem_append_right _ hyI) b j rfl] at ha
      · simp [ht] at ht'
      · obtain ⟨b, j, rfl, -, ha⟩ := hw z _ hz
        simp [hI _ (List.mem_append_right _ hyI) b j rfl] at ha
    · exact h1.notNm y hy1 z hz
  refine ⟨fun y => ?_, fun y hy => ?_, fun y hy z hz => ?_⟩
  · rw [List.count_append]
    by_cases hy1 : y ∈ D1
    · rw [List.count_eq_zero_of_not_mem (hdis y hy1)]
      exact h1.once y
    · rw [List.count_eq_zero_of_not_mem hy1, Nat.zero_add]
      exact h2.once y
  · rcases List.mem_append.1 hy with hy | hy
    · rcases h1.cls y hy with h | ⟨hyI, ht, ht'⟩ | h
      · exact .inl (h.up S2.next)
      · exact .inr (.inl ⟨List.mem_append_left _ hyI, ht, S2.taken y ht'⟩)
      · exact .inr (.inr h)
    · rcases h2.cls y hy with h | ⟨hyI, ht, ht'⟩ | ⟨z, hz⟩
      · exact .inl (h.widen S1.avoid S1.next (Nat.le_refl _))
      · refine .inr (.inl ⟨List.mem_append_right _ hyI, ?_, ht'⟩)
        exact Bool.eq_false_iff.2 fun h => by simp [S1.taken y h] at ht
      · exact (S1.nm z y hz).elim (fun h => .inr (.inr ⟨z, h⟩)) (.inl <| ·.up S2.next)
  · rcases List.mem_append.1 hy with hy | hy
    · exact (S2.nm z y hz).elim (h1.notNm y hy z) (h1.not_new S1 hw hI1 hy)
    · exact h2.notNm y hy z hz

end

/-! ## The state primitives -/

section
variable [iLI : LawfulHasIdent P] {I D : List P.Ident} {st st1 st' : WSt P} {x n : P.Ident}
  {κ : RE P} {d : Nat} {r : WRes P}

omit iWL in
/-- A name drawn by a step keeping the renamings, from a state with the renaming facts, is
    declared once by it. -/
private theorem DeclW.drawn (hb : NmOK st) (hnm : st1.nm = st.nm) (hx : NewIn st st1 x) :
    DeclW I st st1 [x] := by
  refine ⟨fun _ => List.count_le_length, fun z hz => .inl (List.mem_singleton.1 hz ▸ hx),
    fun z hz w hw => ?_⟩
  obtain ⟨b, j, e, -, hj, -⟩ := List.mem_singleton.1 hz ▸ hx
  obtain ⟨b', j', e', hj', -⟩ := hb w z (hnm ▸ hw)
  exact absurd (freshName_counter_inj (e.symm.trans e')) (by omega)

omit iWL in
/-- A run of `wFreshBool` is a `DeclStep` declaring once the name it draws. -/
private theorem wFreshBool_d {b : String} (h : (wFreshBool b).run st = .ok (x, st1))
    (hb : NmOK st) :
    DeclStep st st1 ∧ DeclW I st st1 [x] := by
  obtain ⟨m, hx⟩ := wFreshBool_w (D := []) h
  cases (wFreshBool_run b st).symm.trans h
  exact ⟨.of_eq rfl m.next rfl rfl, .drawn hb rfl hx⟩

/-- A run of `wFreshLike` is a `DeclStep` declaring once the name it draws. -/
private theorem wFreshLike_d {y : P.Ident} (h : (wFreshLike y).run st = .ok (x, st1))
    (hb : NmOK st) : DeclStep st st1 ∧ DeclW I st st1 [x] := by
  obtain ⟨m, hx⟩ := wFreshLike_w (D := []) h
  cases (wFreshLike_run y st).symm.trans h
  exact ⟨.of_eq rfl m.next rfl rfl, .drawn hb rfl hx⟩

/-- A run of `wRen` is a `DeclStep`. -/
private theorem wRen_d {e : P.Expr} {p : WExpr P × List P.Ident}
    (h : (wRen e).run st = .ok (p, st1)) :
    DeclStep st st1 :=
  have m := wRen_w (D := []) h
  ⟨m.avoid, m.next, fun _ h' => (wRen_keep h).1 ▸ h', m.nm⟩

/-- A run of `wDecl x` from a well-formed state, `x` avoided if of fresh-name form, is a
    `DeclStep` declaring once the name it returns. -/
private theorem wDecl_d (h : (wDecl x).run st = .ok (n, st1)) (hw : WFSt st)
    (hx : AvoidedIfFresh st x) : DeclStep st st1 ∧ DeclW [x] st st1 [n] := by
  obtain ⟨m, ht, -, hn⟩ := wDecl_k (D := []) h
  refine ⟨⟨m.avoid, m.next, fun y hy => by simp [ht, hy], m.nm⟩, ⟨?_, fun y hy => ?_,
    fun y hy => List.mem_singleton.1 hy ▸ wDecl_notNm hw hx h⟩⟩
  · exact fun _ => List.count_le_length
  obtain rfl := List.mem_singleton.1 hy
  rcases hn with hn | ⟨rfl, hn⟩ | hn
  · exact .inr (.inr ⟨x, hn⟩)
  · exact .inr (.inl ⟨List.mem_singleton_self _, hn, by simp [ht]⟩)
  · exact .inl hn

omit iLI iWL in
/-- A run of `liveAdd` is a `DeclStep`. -/
private theorem liveAdd_d {xs : List P.Ident} {u : Unit} (h : (liveAdd xs).run st = .ok (u, st1)) :
    DeclStep st st1 := by
  obtain ⟨live, clock, rfl, -⟩ := liveAdd_step h
  exact .of_eq rfl (Nat.le_refl _) rfl rfl

omit iLI iWL in
/-- A run of `liveDel` is a `DeclStep`. -/
private theorem liveDel_d {u : Unit} (h : (liveDel x).run st = .ok (u, st1)) : DeclStep st st1 := by
  cases (liveDel_run x st).symm.trans h
  exact .of_eq rfl (Nat.le_refl _) rfl rfl

omit iLI iWL in
/-- A name avoided if of fresh-name form stays so when the avoided names are kept. -/
private theorem AvoidedIfFresh.of_avoid (h : AvoidedIfFresh st x) (ha : st1.avoid = st.avoid) :
    AvoidedIfFresh st1 x := fun b j e => ha ▸ h b j e

omit iLI iWL in
/-- The declaration facts of a walk from `st1` hold from `st` before a `DeclStep` to `st1`. -/
private theorem DeclW.pre (S : DeclStep st st1) (hn : st1.next ≤ st'.next) (h : DeclW I st1 st' D) :
    DeclW I st st' D := by
  refine ⟨h.once, fun y hy => ?_, h.notNm⟩
  rcases h.cls y hy with h | ⟨hyI, ht, ht'⟩ | ⟨z, hz⟩
  · exact .inl (h.widen S.avoid S.next (Nat.le_refl _))
  · exact .inr (.inl ⟨hyI, Bool.eq_false_iff.2 fun h => by simp [S.taken y h] at ht, ht'⟩)
  · exact (S.nm z y hz).elim (fun h => .inr (.inr ⟨z, h⟩)) (.inl <| ·.up hn)

omit iWL in
/-- The declaration facts of a walk to `st1` hold to `st'` after a `DeclStep` from `st1`. -/
private theorem DeclW.post (S0 : DeclStep st st1) (S : DeclStep st1 st') (hw : NmOK st)
    (hI : ∀ x ∈ I, AvoidedIfFresh st x) (h : DeclW I st st1 D) : DeclW I st st' D := by
  simpa using DeclW.seq S0 S hw (by simpa using hI) h (DeclW.nil (I := []))

omit iDE iBE iLB iHB iHF iSF iHI iHa iHFs iLI iWL in
/-- The empty output declares nothing. -/
private theorem wDecls_nil : wDecls (Rope.nil : Rope (WItem P)).toList = [] := by
  simp [Rope.toList_nil, wDecls]

omit iLI iWL in
/-- The declaration facts hold for the names an empty output declares. -/
private theorem DeclW.of_nil {o : Rope (WItem P)} (h : o = .nil) :
    DeclW I st st1 (wDecls o.toList) := by
  subst h
  rw [wDecls_nil]
  exact .nil

omit iLI iWL in
/-- A step changing only the declared types is a `DeclStep`. -/
private theorem DeclStep.tys (st : WSt P) (T : Std.HashMap P.Ident P.Ty) :
    DeclStep st { st with tys := T } := .of_eq rfl (Nat.le_refl _) rfl rfl

omit iDE iBE iLB iHB iHF iSF iHI iHa iHFs iLI iWL in
/-- `setReach` declares nothing. -/
private theorem wDecls_setReach (κ : RE P) (X : WExpr P) : wDecls (setReach κ X).toList = [] := by
  cases κ <;> simp [setReach, Rope.toList_one, Rope.toList_nil, wDecls]

omit iLI iWL in
/-- The declaration facts hold for a list equal to the empty list. -/
private theorem DeclW.of_eq_nil (h : D = []) : DeclW I st st1 D := h ▸ .nil

omit iDE iBE iLB iHB iHF iSF iHI iHa iHFs iLI iWL in
/-- The names declared by concatenated items are those of the parts. -/
private theorem wDecls_append : ∀ (a b : List (WItem P)), wDecls (a ++ b) = wDecls a ++ wDecls b
  | [], _ => by simp [wDecls]
  | it :: a, b => by cases it <;> simp [wDecls, wDecls_append a b]

omit iDE iBE iLB iHB iHF iSF iHI iHa iHFs iLI iWL in
/-- Appending ropes by a fold step that declares nothing declares nothing. -/
private theorem wDecls_foldl {α : Type} (F : Rope (WItem P) → α → Rope (WItem P))
    (hF : ∀ acc a, wDecls (F acc a).toList = wDecls acc.toList) :
    ∀ (L : List α) (acc : Rope (WItem P)), wDecls (L.foldl F acc).toList = wDecls acc.toList
  | [], _ => rfl
  | a :: L, acc => by rw [List.foldl_cons, wDecls_foldl F hF L, hF]

omit iDE iBE iLB iHB iHF iSF iHI iHa iHFs iLI iWL in
/-- Appending one assignment per element of a list declares no new name. -/
private theorem wDecls_foldl_sets {α : Type} (g : α → WItem P) (hg : ∀ a, ∃ y v, g a = .set y v)
    (L : List α) (acc : Rope (WItem P)) :
    wDecls (L.foldl (fun acc a => acc.app (Rope.one (g a))) acc).toList = wDecls acc.toList :=
  wDecls_foldl _ (fun acc a => by
    obtain ⟨y, v, hy⟩ := hg a
    simp [Rope.toList_app, Rope.toList_one, wDecls_append, hy, wDecls]) L acc

omit iDE iLB iHB iHF iSF iHI iHa iHFs iLI iWL in
/-- A list that is empty under a condition has each element at most as often as the list. -/
private theorem count_ite_nil_le {c : Prop} [Decidable c] (a : List P.Ident) (y : P.Ident) :
    (if c then [] else a).count y ≤ a.count y := by
  split <;> simp

omit iDE iBE iLB iHB iHF iSF iHI iHa iHFs iLI iWL in
/-- The names a conditional rope declares are those of the branch it selects. -/
private theorem wDecls_ite {c : Prop} [Decidable c] (a b : Rope (WItem P)) :
    wDecls (if c then a else b).toList = if c then wDecls a.toList else wDecls b.toList := by
  split <;> rfl

omit iWL in
/-- Two consecutive walks with their declaration facts for the locals `I` compose. -/
private theorem DeclW.cat (h1 : DeclStep st st1 ∧ DeclW I st st1 D) {st2 : WSt P}
    {D2 : List P.Ident}
    (h2 : DeclStep st1 st2 ∧ DeclW I st1 st2 D2) (hw : NmOK st)
    (hI : ∀ x ∈ I, AvoidedIfFresh st x) : DeclStep st st2 ∧ DeclW I st st2 (D ++ D2) :=
  ⟨h1.1.trans h2.1, (h1.2.seq h1.1 h2.1 hw (by simpa using hI) h2.2).monoI (by simp)⟩

omit iLI iWL in
/-- A state is a `DeclStep` from itself. -/
private theorem DeclStep.refl (st : WSt P) : DeclStep st st := .of_eq rfl (Nat.le_refl _) rfl rfl

omit iDE iLB iHB iHF iSF iHI iHa iHFs iLI iWL in
/-- Counts bounded on two parts bound the counts of their concatenations. -/
private theorem count_app_le {a b A B : List P.Ident} (h1 : ∀ y, a.count y ≤ A.count y)
    (h2 : ∀ y, b.count y ≤ B.count y) : ∀ y, (a ++ b).count y ≤ (A ++ B).count y :=
  fun y => by simp only [List.count_append]; exact Nat.add_le_add (h1 y) (h2 y)

/-! ## Commands -/

/-- The declaration facts of the walk of an `init`. -/
private theorem init_dw {f : Bool} {ty : P.Ty} {e : ExprOrNondet P} {md : MetaData P}
    (h : (wpStmt κ d f (.cmd (.cmd (.init x ty e md)))).run st = .ok (r, st')) (hw : WFSt st)
    (hx : AvoidedIfFresh st x) : DeclW [x] st st' (wDecls r.out.toList) := by
  cases f
  · cases e <;> simp only [wpStmt, Bool.not_false, ↓reduceIte] at h <;>
      obtain ⟨rfl, rfl⟩ := wm_run_pure_ok h <;> exact .of_nil rfl
  cases e with
  | det e =>
    simp only [wpStmt, Bool.not_true, Bool.false_eq_true, ↓reduceIte, pure_bind] at h
    peel h ⟨⟨we, rd⟩, s1, h1⟩ ⟨n, s2, h2⟩ _
    have S1 := wRen_d h1
    have hw1 := (wRen_walk h1).wf hw nofun
    obtain ⟨S2, D2⟩ := wDecl_d h2 hw1 (hx.of_avoid S1.avoid)
    have hx1 : ∀ y ∈ [x], AvoidedIfFresh st y := by simpa using hx
    have S3 := (S1.trans S2).trans (DeclStep.tys s2 (s2.tys.insert n ty))
    have D2' := (D2.pre S1 S2.next).post (S1.trans S2) (DeclStep.tys s2 (s2.tys.insert n ty))
      hw.nmOK hx1
    split at h
    · peel h ⟨_, s5, h5⟩ ⟨_, s6, h6, ⟨⟩⟩
      simpa [Rope.toList_one, wDecls] using
        D2'.post S3 ((liveDel_d h5).trans (liveAdd_d h6)) hw.nmOK hx1
    · peel h ⟨xd, s4, h4⟩ _ ⟨_, s5, h5⟩ ⟨_, s6, h6, ⟨⟩⟩
      obtain ⟨m4, hx4⟩ := wFresh_w (D := []) h4
      have e4 : s4.nm = s2.nm ∧ s4.taken = s2.taken := by
        cases (wFresh_run _ _).symm.trans h4
        exact ⟨rfl, rfl⟩
      have S4 := DeclStep.of_eq m4.avoid m4.next e4.2 e4.1
      have D4 := DeclW.drawn (I := []) (hw.nmOK.step S3) e4.1 hx4
      have D := (D2'.seq S3 S4 hw.nmOK (by simpa using hx) D4).post (S3.trans S4)
        ((DeclStep.tys s4 _).trans ((liveDel_d h5).trans (liveAdd_d h6))) hw.nmOK
        (by simpa using hx)
      exact D.sub fun y => by
        simp only [Rope.toList_app, Rope.toList_one, List.cons_append, List.nil_append, wDecls,
          List.count_cons, List.count_nil, beq_iff_eq, Nat.zero_add]
        omega
  | nondet =>
    simp only [wpStmt, Bool.not_true, Bool.false_eq_true, ↓reduceIte] at h
    peel h ⟨n, s2, h2⟩ _ ⟨_, s4, h4, ⟨⟩⟩
    obtain ⟨S2, D2⟩ := wDecl_d h2 hw hx
    simpa [Rope.toList_one, wDecls] using
      D2.post S2 ((DeclStep.tys s2 _).trans (liveDel_d h4)) hw.nmOK (by simpa using hx)

/-- The declaration facts of the walk of a `set`. -/
private theorem set_dw {f : Bool} {e : ExprOrNondet P} {md : MetaData P}
    (h : (wpStmt κ d f (.cmd (.cmd (.set x e md)))).run st = .ok (r, st')) (hw : WFSt st) :
    DeclW [] st st' (wDecls r.out.toList) := by
  cases f
  · cases e <;> simp only [wpStmt, Bool.not_false, ↓reduceIte] at h <;>
      obtain ⟨rfl, rfl⟩ := wm_run_pure_ok h <;> exact .of_nil rfl
  cases e with
  | det e =>
    simp only [wpStmt, Bool.not_true, Bool.false_eq_true, ↓reduceIte, pure_bind] at h
    peel h ⟨⟨we, rd⟩, s1, h1⟩ ⟨n, s2, h2⟩
    split at h <;> peel h ⟨_, s3, h3⟩ ⟨_, s4, h4, ⟨⟩⟩ <;>
      exact .of_eq_nil (by simp [Rope.toList_one, wDecls])
  | nondet =>
    simp only [wpStmt, Bool.not_true, Bool.false_eq_true, ↓reduceIte, pure_bind] at h
    peel h ⟨n, s2, h2⟩ ⟨xh, s3, h3⟩
    have m2 := (wName_w (D := []) h2).1
    have S2 : DeclStep st s2 := ⟨m2.avoid, m2.next, fun _ h' => (wName_keep h2).1 ▸ h', m2.nm⟩
    obtain ⟨S3, D3⟩ := wFreshLike_d (I := []) h3 (hw.nmOK.step S2)
    split at h <;> peel h ⟨_, s4, h4, ⟨⟩⟩
    all_goals
      have S4 : DeclStep s3 st' := by first | exact liveDel_d h4 | exact liveAdd_d h4
      simpa [Rope.toList_one, Rope.toList_app, wDecls] using
        (D3.pre S2 S3.next).post (S2.trans S3) S4 hw.nmOK (by simp)

/-- The declaration facts of the walk of an `exit`. -/
private theorem exit_dw {f : Bool} {l : String} {md : MetaData P}
    (h : (wpStmt κ d f (.exit l md)).run st = .ok (r, st')) (hw : WFSt st) :
    DeclW [] st st' (wDecls r.out.toList) := by
  cases κ
  · simp only [wpStmt] at h
    obtain ⟨rfl, rfl⟩ := wm_run_pure_ok h
    exact .of_nil rfl
  all_goals
    simp only [wpStmt] at h
    run_peel h
    cases ht : st.labelDepth[l]? <;> cases f <;>
      simp only [ht, Bool.not_false, Bool.not_true, ↓reduceIte, Bool.false_eq_true] at h
  case' name.refl.some.true | neg.refl.some.true | andNeg.refl.some.true =>
    peel h ⟨e, s2, h2⟩ _ ⟨_, s4, h4, ⟨⟩⟩
    obtain ⟨S2, D2⟩ := wFreshBool_d (I := []) h2 hw.nmOK
    simpa [Rope.toList_one, Rope.toList_app, wDecls, wDecls_setReach] using
      D2.post S2 ((liveAdd_d h4).eq_pre rfl (Nat.le_refl _) rfl rfl) hw.nmOK (by simp)
  all_goals
    obtain ⟨rfl, rfl⟩ := wm_run_pure_ok h
    exact .of_eq_nil (by simp [Rope.toList_nil, wDecls_setReach, wDecls])

/-! ## Blocks -/

/-- The declaration facts of the walk of a block, from those of the walks of its body. -/
private theorem block_dw {f : Bool} {l : String} {body : PStmts P} {md : MetaData P}
    (hB : ∀ κB s0 B s1, (wpList κB (d + 1) f body).run s0 = .ok (B, s1) → WFSt s0 →
      (∀ y ∈ stmtsInits body, AvoidedIfFresh s0 y) →
      DeclW (stmtsInits body) s0 s1 (wDecls B.out.toList))
    (h : (wpStmt κ d f (.block l body md)).run st = .ok (r, st')) (hw : WFSt st)
    (hI : ∀ y ∈ stmtsInits body, AvoidedIfFresh st y) :
    DeclW (stmtsInits body) st st' (wDecls r.out.toList) := by
  have hw0 := wfSt_blk hw l d st.clock
  have S0 : DeclStep st _ := DeclStep.of_eq (st1 := { st with
    labelDepth := st.labelDepth.insert l (d + 1), pending := st.pending.insert l [],
    stampAt := st.stampAt.insert (d + 1) st.clock, carries := st.carries.insert (d + 1) [] })
    rfl (Nat.le_refl _) rfl rfl
  cases κ
  case top =>
    simp only [wpStmt] at h
    peel h _ _ ⟨rr, sB, h1⟩
    simp only [pure_bind] at h
    peel h ⟨B, s4, hB4⟩ _ _ ⟨_, s5, h5, ⟨⟩⟩
    obtain ⟨S1, D1⟩ := wFreshBool_d (I := []) h1 hw0.nmOK
    have hw1 := (wFreshBool_walk h1).wf hw0 nofun
    have DB := hB _ _ _ _ hB4 hw1 fun y hy => (hI y hy).of_avoid S1.avoid
    have WB := wpList_walkOK hB4
    have SB := DeclStep.of_core WB.toWalkCore
      (WB.wf hw1 fun y hy => (hI y hy).of_avoid S1.avoid)
    have D := ((D1.seq S1 SB hw0.nmOK (fun y hy => hI y (by simpa using hy)) DB).pre S0
      (Nat.le_trans S1.next SB.next)).post ((S0.trans S1).trans SB)
      ((liveAdd_d h5).eq_pre rfl (Nat.le_refl _) rfl rfl) hw.nmOK (by simpa using hI)
    refine (D.monoI (by simp)).sub fun y => ?_
    simp only [Rope.toList_app, wDecls_append, wDecls_ite,
      wDecls_foldl_sets _ (fun _ => ⟨_, _, rfl⟩), wDecls_nil]
    refine Nat.le_trans (count_ite_nil_le _ _) ?_
    cases f <;> simp [Rope.toList_one, wDecls, List.count_cons]
  all_goals
    simp only [wpStmt] at h
    iterate 2 run_peel h
    simp only [pure_bind] at h
    peel h ⟨B, s4, hB4⟩ _ _ ⟨_, s5, h5, ⟨⟩⟩
    have DB := hB _ _ _ _ hB4 hw0 fun y hy => (hI y hy).of_avoid rfl
    have WB := wpList_walkOK hB4
    have SB := DeclStep.of_core WB.toWalkCore (WB.wf hw0 fun y hy => (hI y hy).of_avoid rfl)
    have D := (DB.pre S0 SB.next).post (S0.trans SB)
      ((liveAdd_d h5).eq_pre rfl (Nat.le_refl _) rfl rfl) hw.nmOK hI
    refine D.sub fun y => ?_
    simp only [Rope.toList_app, wDecls_append, wDecls_ite,
      wDecls_foldl_sets _ (fun _ => ⟨_, _, rfl⟩), wDecls_nil, wDecls_setReach]
    simp

/-! ## Real branches -/

omit iLI iWL in
/-- Clearing the live set and the label maps keeps well-formedness. -/
private theorem WFSt.clear (hw : WFSt st) (L : Std.HashMap String Nat)
    (Q : Std.HashMap String (List P.Ident))
    (hQ : ∀ l e, e ∈ Q.getD l [] → e ∈ st.pending.getD l []) (V : Std.HashMap P.Ident Nat)
    (hV : ∀ (n : P.Ident) (s : Nat), V[n]? = some s → s < st.clock) :
    WFSt { st with live := V, labelDepth := L, pending := Q } :=
  { hw with live_stamp := hV, pending_fresh := fun l e he => hw.pending_fresh l e (hQ l e he) }

/-- The declaration facts of the walk of a real branch, from those of the walks of its arms. -/
private theorem real_dw {c : P.Expr} {tss ess : PStmts P}
    (hT : ∀ s0 R s1, (wpList .top d false tss).run s0 = .ok (R, s1) → WFSt s0 →
      (∀ y ∈ stmtsInits tss, AvoidedIfFresh s0 y) →
      DeclW (stmtsInits tss) s0 s1 (wDecls R.out.toList))
    (hE : ∀ s0 R s1, (wpList .top d false ess).run s0 = .ok (R, s1) → WFSt s0 →
      (∀ y ∈ stmtsInits ess, AvoidedIfFresh s0 y) →
      DeclW (stmtsInits ess) s0 s1 (wDecls R.out.toList))
    (h : (wpIteReal κ d c tss ess).run st = .ok (r, st')) (hw : WFSt st)
    (hI : ∀ y ∈ stmtsInits tss ++ stmtsInits ess, AvoidedIfFresh st y) :
    DeclW (stmtsInits tss ++ stmtsInits ess) st st' (wDecls r.out.toList) := by
  unfold wpIteReal at h
  peel h _ _ ⟨E, s1, h1⟩ _ _ ⟨T, s3, h3⟩ _ _
  split at h
  · obtain ⟨rfl, rfl⟩ := wm_run_pure_ok h
    exact .of_nil rfl
  peel h ⟨⟨wc, rdc⟩, s5, h5⟩ ⟨g, s6, h6⟩ ⟨_, s7, h7, ⟨⟩⟩
  have hIE : ∀ y ∈ stmtsInits ess, AvoidedIfFresh st y := fun y hy => hI y (by simp [hy])
  have hIT : ∀ y ∈ stmtsInits tss, AvoidedIfFresh st y := fun y hy => hI y (by simp [hy])
  have hwa := hw.clear {} {} (by simp) {} (by simp)
  have WE := wpList_walkOK h1
  have hw1 := WE.wf hwa hIE
  have SE := DeclStep.of_core WE.toWalkCore hw1
  have DE := hE _ _ _ h1 hwa hIE
  have hw1' := hw1.clear s1.labelDepth s1.pending (fun _ _ h => h) {} (by simp)
  have WT := wpList_walkOK h3
  have hIT' : ∀ y ∈ stmtsInits tss, AvoidedIfFresh { s1 with live := {} } y :=
    fun y hy => (hIT y hy).of_avoid (WE.avoid)
  have ST := DeclStep.of_core WT.toWalkCore (WT.wf hw1' hIT')
  have DT := hT _ _ _ h3 hw1' hIT'
  have Sa : DeclStep st { st with live := {}, labelDepth := {}, pending := {} } :=
    .of_eq rfl (Nat.le_refl _) rfl rfl
  have S1 : DeclStep s1 { s1 with live := {} } := .of_eq rfl (Nat.le_refl _) rfl rfl
  have S5 := (wRen_d h5).eq_pre (st := s3) rfl (Nat.le_refl _) rfl rfl
  have hb := hw.nmOK
  have SaT := ((Sa.trans SE).trans S1).trans ST
  obtain ⟨S6, D6⟩ := wFreshBool_d (I := stmtsInits tss ++ stmtsInits ess) h6
    (hb.step (SaT.trans S5))
  have C := DeclW.cat ⟨(Sa.trans SE).trans S1, (((DE.pre Sa SE.next).post (Sa.trans SE) S1 hb
    hIE).monoI fun x hx => by simp [hx])⟩ ⟨ST.trans S5, (DT.post ST S5 hw1'.nmOK hIT').monoI
    fun x hx => by simp [hx]⟩ hb hI
  have D := (DeclW.cat C ⟨S6, D6⟩ hb hI).2.post (SaT.trans (S5.trans S6)) (liveAdd_d h7) hb hI
  refine D.sub fun y => ?_
  simp only [wDecls_ite, Rope.toList_app, Rope.toList_one]
  split <;> (try split) <;>
    simp only [List.cons_append, List.nil_append, wDecls, List.append_nil, List.count_cons,
      List.count_append, beq_iff_eq, List.append_assoc, List.count_nil, Nat.zero_add,
      Nat.le_add_left, Nat.add_le_add_iff_left] <;>
    omega

/-! ## Laid-out `ite`s -/

/-- A run of `saveRestore` is a `DeclStep` declaring once the save and copy names its saves and
    copies declare; its restores declare nothing. -/
private theorem saveRestore_d {xs : List P.Ident} {sv cp rs : Rope (WItem P)}
    {cps : List (P.Ident × P.Ident)} (h : (saveRestore xs).run st = .ok ((sv, cp, rs, cps), st1))
    (hb : NmOK st) :
    (DeclStep st st1 ∧ DeclW [] st st1 (wDecls sv.toList ++ wDecls cp.toList)) ∧
      wDecls rs.toList = [] := by
  unfold saveRestore at h
  obtain ⟨⟨sv1, cp1, rs1, cps1⟩, s1, hl, h⟩ := wm_run_bind_ok h
  cases h
  refine wm_forIn_inv (fun _ (b : Rope (WItem P) × Rope (WItem P) × Rope (WItem P) ×
      List (P.Ident × P.Ident)) s2 => (DeclStep st s2 ∧ DeclW [] st s2 (wDecls b.1.toList ++
      wDecls b.2.1.toList)) ∧ wDecls b.2.2.1.toList = []) _ ?_ xs [] _ st _ _
    ⟨⟨.refl st, by simpa [wDecls_nil] using DeclW.nil⟩, wDecls_nil⟩ hl
  intro S y b s2 b' s3 ⟨⟨S2, D2⟩, hrs⟩ hb'
  peel hb' ⟨n1, t1, g1⟩ ⟨n2, t2, g2⟩
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Except.ok.inj hb')
  have hb2 := hb.step S2
  obtain ⟨S3, D3⟩ := wFreshLike_d (I := []) g1 hb2
  obtain ⟨S4, D4⟩ := wFreshLike_d (I := []) g2 (hb2.step S3)
  have D := (DeclW.cat (DeclW.cat ⟨S2, D2⟩ ⟨S3, D3⟩ hb (by simp)) ⟨S4, D4⟩ hb (by simp))
  refine ⟨_, rfl, ⟨D.1, D.2.sub fun z => ?_⟩, ?_⟩
  · simp only [Rope.toList_app, Rope.toList_one, wDecls_append, wDecls, List.append_assoc,
      List.cons_append, List.nil_append, List.count_append, List.count_cons, List.count_nil,
      beq_iff_eq, Nat.zero_add, Nat.add_le_add_iff_left]
    omega
  · simp [Rope.toList_app, Rope.toList_one, wDecls_append, wDecls, hrs]

omit iWL in
/-- An optional draw is a `DeclStep` declaring once the name it draws, and keeps
    well-formedness. -/
private theorem OptDraw.decl {b : String} {o : Option P.Ident} (h : OptDraw b st st1 o)
    (hb : NmOK st) :
    (DeclStep st st1 ∧ DeclW I st st1 o.toList) ∧ (WFSt st → WFSt st1) := by
  cases o with
  | none => exact h ▸ ⟨⟨.refl _, .nil⟩, id⟩
  | some x => exact ⟨wFreshBool_d h hb, fun hw => (wFreshBool_walk h).wf hw nofun⟩

/-- The declaration facts of the walk of a laid-out `ite`, from those of the walks of its
    arms. -/
private theorem laid_dw {c : P.Expr} {tss ess : PStmts P}
    (hT : ∀ κ' s0 R s1, (wpList κ' d true tss).run s0 = .ok (R, s1) → WFSt s0 →
      (∀ y ∈ stmtsInits tss, AvoidedIfFresh s0 y) →
      DeclW (stmtsInits tss) s0 s1 (wDecls R.out.toList))
    (hE : ∀ κ' s0 R s1, (wpList κ' d true ess).run s0 = .ok (R, s1) → WFSt s0 →
      (∀ y ∈ stmtsInits ess, AvoidedIfFresh s0 y) →
      DeclW (stmtsInits ess) s0 s1 (wDecls R.out.toList))
    (h : (wpIteLaid κ d c tss ess).run st = .ok (r, st')) (hw : WFSt st)
    (hI : ∀ y ∈ stmtsInits tss ++ stmtsInits ess, AvoidedIfFresh st y) :
    DeclW (stmtsInits tss ++ stmtsInits ess) st st' (wDecls r.out.toList) := by
  refine wpIteLaid_inv h _ fun wc rdc s1 g s2 rT s3 κE rE s4 E s5 T s6 sv3 cp3 rs3 cps3 s7 svT cpT
    rsT cpsT s8 svE cpE rsE cpsE s9 gm s10 qm s11 rEm s12 h1 h2 h3 hc h5 h6 h7 h8 h9 h10 _ h11
    _ h12 _ hEnd => ?_
  let I := stmtsInits tss ++ stmtsInits ess
  have hb := hw.nmOK
  have S1 := wRen_d h1
  have hw1 := (wRen_walk h1).wf hw nofun
  have hw2 := (wFreshBool_walk h2).wf hw1 nofun
  have hw3 := (wFreshBool_walk h3).wf hw2 nofun
  have R2 := wFreshBool_d (I := I) h2 hw1.nmOK
  have R3 := wFreshBool_d (I := I) h3 hw2.nmOK
  obtain ⟨R4, hw4⟩ : (DeclStep s3 s4 ∧ DeclW I s3 s4 rE.toList) ∧ WFSt s4 := by
    rcases hc with ⟨-, -, rfl, rfl⟩ | ⟨-, rfl, rfl⟩ | ⟨-, x, -, rfl, h4⟩
    · exact ⟨⟨.refl _, .nil⟩, hw3⟩
    · exact ⟨⟨.refl _, .nil⟩, hw3⟩
    · exact ⟨wFreshBool_d h4 hw3.nmOK, (wFreshBool_walk h4).wf hw3 nofun⟩
  have S04 := S1.trans (R2.1.trans (R3.1.trans R4.1))
  have hI4 : ∀ y ∈ I, AvoidedIfFresh s4 y := fun y hy => (hI y hy).of_avoid S04.avoid
  have WE := wpList_walkOK h5
  have hw5 := WE.wf hw4 fun y hy => hI4 y (by simp [I, hy])
  have R5 : DeclStep s4 s5 ∧ DeclW I s4 s5 (wDecls E.out.toList) :=
    ⟨.of_core WE.toWalkCore hw5,
      (hE κE s4 E s5 h5 hw4 fun y hy => hI4 y (by simp [I, hy])).monoI fun x hx => by simp [I, hx]⟩
  have WT := wpList_walkOK h6
  have hw6 := WT.wf hw5 fun y hy => (hI4 y (by simp [I, hy])).of_avoid R5.1.avoid
  have R6 : DeclStep s5 s6 ∧ DeclW I s5 s6 (wDecls T.out.toList) :=
    ⟨.of_core WT.toWalkCore hw6, (hT (.name rT) s5 T s6 h6 hw5
      fun y hy => (hI4 y (by simp [I, hy])).of_avoid R5.1.avoid).monoI
      fun x hx => by simp [I, hx]⟩
  obtain ⟨R7, hrs3⟩ := saveRestore_d h7 hw6.nmOK
  obtain ⟨R8, hrsT⟩ := saveRestore_d h8 (hw6.nmOK.step R7.1)
  obtain ⟨R9, hrsE⟩ := saveRestore_d h9 ((hw6.nmOK.step R7.1).step R8.1)
  have hb9 := ((hw6.nmOK.step R7.1).step R8.1).step R9.1
  obtain ⟨R10, -⟩ := OptDraw.decl (I := I) h10 hb9
  obtain ⟨R11, -⟩ := OptDraw.decl (I := I) h11 (hb9.step R10.1)
  obtain ⟨R12, -⟩ := OptDraw.decl (I := I) h12 ((hb9.step R10.1).step R11.1)
  have hI0 : ∀ y ∈ I, AvoidedIfFresh st y := hI
  have C := DeclW.cat (DeclW.cat (DeclW.cat ⟨S1, .nil⟩ R2 hb hI0) R3 hb hI0) R4 hb hI0
  have C := DeclW.cat (DeclW.cat C R5 hb hI0) R6 hb hI0
  have C := DeclW.cat (DeclW.cat C ⟨R7.1, R7.2.monoI nofun⟩ hb hI0) ⟨R8.1, R8.2.monoI nofun⟩ hb
    hI0
  have C := DeclW.cat (DeclW.cat C ⟨R9.1, R9.2.monoI nofun⟩ hb hI0) R10 hb hI0
  have C := DeclW.cat (DeclW.cat C R11 hb hI0) R12 hb hI0
  rcases hEnd with ⟨-, rfl, rfl⟩ | ⟨-, hF, rfl⟩
  · exact .of_nil rfl
  have D := C.2.post C.1 ((liveAdd_d hF).eq_pre rfl (Nat.le_refl _) rfl rfl) hb hI0
  refine D.sub fun y => Nat.le_trans (?_ : _ ≤ List.count y ([g] ++ ([rT] ++ (gm.toList ++
    (qm.toList ++ (wDecls sv3.toList ++ (wDecls svT.toList ++ (wDecls T.out.toList ++ (wDecls
    cp3.toList ++ (wDecls cpT.toList ++ (rE.toList ++ (rEm.toList ++ (wDecls svE.toList ++
    (wDecls E.out.toList ++ (wDecls cpE.toList ++ []))))))))))))))) (Nat.le_of_eq ?_)
  · simp only [Rope.toList_app, Rope.toList_one, Rope.toList_foldl_app, Rope.toList_nil,
      List.flatMap_cons, List.flatMap_nil, List.nil_append, List.append_nil, wDecls_append, hrs3,
      hrsT, hrsE]
    revert y
    refine count_app_le ?_ (count_app_le ?_ (count_app_le ?_ (count_app_le ?_ (count_app_le ?_
      (count_app_le ?_ (count_app_le ?_ (count_app_le ?_ (count_app_le ?_ (count_app_le ?_
      (count_app_le ?_ (count_app_le ?_ (count_app_le ?_ ?_))))))))))))
    all_goals intro y
    all_goals try exact Nat.le_refl _
    · simp [wDecls]
    · rw [wDecls_ite, wDecls_nil]
      exact Nat.le_trans (count_ite_nil_le _ _) (by simp [wDecls, Rope.toList_one])
    · cases gm <;> simp [wDecls, Rope.toList_nil, Rope.toList_one]
    · split <;> simp [wDecls, Rope.toList_nil, Rope.toList_one]
    · split
      · rw [wDecls_ite, wDecls_nil]
        exact Nat.le_trans (count_ite_nil_le _ _) (by simp [wDecls, Rope.toList_one])
      · simp [wDecls, Rope.toList_nil]
    · split <;> simp [wDecls, Rope.toList_nil, Rope.toList_one]
    · rw [wDecls_foldl _ ?_]
      · split <;> (try split) <;>
          simp [wDecls, Rope.toList_nil, Rope.toList_one, wDecls_setReach]
      · intro acc a
        simp [Rope.toList_app, Rope.toList_one, wDecls_append, wDecls]
  · simp only [List.count_append, List.count_nil, Nat.zero_add]
    ac_rfl

/-! ## Statements and lists -/

mutual
/-- **The declaration facts of a statement walk.**  The walk of a statement from a well-formed
    state, its declared locals avoided if of fresh-name form, declares each name at most once, a
    name it draws, a local of the statement it records as declared, or a renaming before it, and
    no renaming after it. -/
theorem wpStmt_declW : ∀ (s : PStmt P) (κ : RE P) (d : Nat) (f : Bool) {st st' : WSt P}
    {a : WRes P}, (wpStmt κ d f s).run st = .ok (a, st') → WFSt st →
      (∀ y ∈ stmtsInits [s], AvoidedIfFresh st y) →
      DeclW (stmtsInits [s]) st st' (wDecls a.out.toList)
  | .cmd (.cmd (.init x ty e md)), _, _, _, _, _, _, h, hw, hI =>
    (init_dw h hw (hI x (by simp [stmtsInits]))).monoI (by simp [stmtsInits])
  | .cmd (.cmd (.set x e md)), _, _, _, _, _, _, h, hw, _ => (set_dw h hw).monoI nofun
  | .exit l md, _, _, _, _, _, _, h, hw, _ => (exit_dw h hw).monoI nofun
  | .block l body md, _, d, f, _, _, _, h, hw, hI =>
    (block_dw (fun κB _ _ _ hB => wpList_declW body κB (d + 1) f hB) h hw
      (by simpa [stmtsInits] using hI)).monoI (by simp [stmtsInits])
  | .ite (.det c) tss ess md, κ, d, f, st, _, _, h, hw, hI => by
    have hI' : ∀ y ∈ stmtsInits tss ++ stmtsInits ess, AvoidedIfFresh st y := by
      simpa [stmtsInits] using hI
    simp only [wpStmt] at h
    cases f
    · exact (real_dw (fun _ _ _ hT => wpList_declW tss .top d false hT)
        (fun _ _ _ hE => wpList_declW ess .top d false hE) h hw hI').monoI
        (by simp [stmtsInits])
    · exact (laid_dw (fun κ' _ _ _ hT => wpList_declW tss κ' d true hT)
        (fun κ' _ _ _ hE => wpList_declW ess κ' d true hE) h hw hI').monoI
        (by simp [stmtsInits])
  | .cmd (.cmd (.assume ..)), _, _, f, _, _, _, h, _, _
  | .cmd (.cmd (.assert ..)), _, _, f, _, _, _, h, _, _
  | .cmd (.cmd (.cover ..)), _, _, f, _, _, _, h, _, _
  | .cmd (.call ..), _, _, f, _, _, _, h, _, _ | .typeDecl .., _, _, f, _, _, _, h, _, _
  | .loop .., _, _, f, _, _, _, h, _, _ | .ite .nondet .., _, _, f, _, _, _, h, _, _ => by
    unfold wpStmt at h
    cases f <;>
      (try simp only [Bool.not_true, Bool.not_false, Bool.false_eq_true, ↓reduceIte] at h)
    all_goals first
      | (peel h ⟨p, s1, h1⟩ ⟨_, s2, h2⟩ rfl
         exact .of_eq_nil (by simp [Rope.toList_one, wDecls]))
      | (obtain ⟨rfl, rfl⟩ := wm_run_pure_ok h
         exact .of_nil rfl)
      | cases h

/-- **The declaration facts of a list walk.**  The walk of a list from a well-formed state, its
    declared locals avoided if of fresh-name form, declares each name at most once, a name it
    draws, a local of the list it records as declared, or a renaming before it, and no renaming
    after it. -/
theorem wpList_declW : ∀ (ss : PStmts P) (κ : RE P) (d : Nat) (fEnd : Bool) {st st' : WSt P}
    {r : WRes P}, (wpList κ d fEnd ss).run st = .ok (r, st') → WFSt st →
      (∀ y ∈ stmtsInits ss, AvoidedIfFresh st y) →
      DeclW (stmtsInits ss) st st' (wDecls r.out.toList)
  | [], _, _, _, _, _, _, h, _, _ => by
    unfold wpList at h
    obtain ⟨rfl, rfl⟩ := wm_run_pure_ok h
    exact .of_nil rfl
  | s :: rest, κ, d, fEnd, st, _, _, h, hw, hI => by
    obtain ⟨r, st1, a, st2, h1, h2, hc⟩ := wpList_run_cons h
    rw [stmtsInits_cons_eq] at hI ⊢
    have hIr : ∀ y ∈ stmtsInits rest, AvoidedIfFresh st y := fun y hy => hI y (by simp [hy])
    have WR := wpList_walkOK h1
    have hw1 := WR.wf hw hIr
    have SR := DeclStep.of_core WR.toWalkCore hw1
    have hIs : ∀ y ∈ stmtsInits [s], AvoidedIfFresh st1 y :=
      fun y hy => (hI y (by simp [hy])).of_avoid SR.avoid
    have WA := wpStmt_walkOK h2
    have SA := DeclStep.of_core WA.toWalkCore (WA.wf hw1 hIs)
    have hcm : ∀ x ∈ stmtsInits rest ++ stmtsInits [s], x ∈ stmtsInits [s] ++ stmtsInits rest :=
      fun _ h => List.perm_append_comm.subset h
    have D := (DeclW.seq SR SA hw.nmOK (fun _ h => hI _ (hcm _ h))
      (wpList_declW rest κ d fEnd h1 hw hIr) (wpStmt_declW s κ d _ h2 hw1 hIs)).monoI hcm
    rcases hc with ⟨-, rfl, rfl⟩ | ⟨-, -, rfl, rfl⟩ | ⟨-, -, rfl, rfl⟩
    · exact D.sub fun y => by simp [List.count_append]
    · have S3 : DeclStep st2 { st2 with dead := r.regs.toList.foldl (·.insert ·) st2.dead } :=
        .of_eq rfl (Nat.le_refl _) rfl rfl
      exact (D.post (SR.trans SA) S3 hw.nmOK hI).sub fun y => by simp [List.count_append]
    · exact D.sub fun y => by
        simp only [WRes.combine, Rope.toList_app, wDecls_append, List.count_append]
        omega
end

end

/-! ## The WP phase -/

variable [LawfulHasIdent P]

/-- **The names the WP output declares.**  The guarded program of the WP phase of a loop-free
    list `ss` declares each name at most once, and each name it declares is declared by `ss` or
    is a fresh name outside the names the phase avoids. -/
theorem wpEntry_decls {G : IdSet P} {tys : Tys P} {ss : PStmts P} {w : WOut P}
    (h : wpEntry G tys ss = .ok w) :
    (Block.definedVars w.lay false).Nodup ∧
    ∀ y ∈ Block.definedVars w.lay false, y ∈ Block.definedVars ss false ∨
      ∃ b k, y = freshName b k ∧ (inputAvoid G tys ss).contains y = false := by
  simp only [wpEntry, wpBody, Except.bind_is_ok, Except.pure_is_ok] at h
  obtain ⟨⟨r, st1⟩, h1, lay, h2, rfl⟩ := h
  have D := wpList_declW ss .top 0 false h1
    (by constructor
        case tys_keys =>
          grind [TyKey, inputAvoid, AvoidSet.contains, IdSet.ofList, → foldr_insert_key]
        all_goals simp)
    fun y hy b j _ => by
      grind [inputAvoid, AvoidSet.contains, IdSet.ofList, stmtsInits_mem_idents y hy]
  have hsub := emit_decls_sublist h2
  have hdv : ∀ {ss : PStmts P}, ∀ y ∈ stmtsInits ss, y ∈ Block.definedVars ss false := by
    intro ss
    induction ss using stmtsInits.induct <;> intro y hy <;>
      simp only [stmtsInits, List.not_mem_nil, List.mem_cons, Block.definedVars,
        Stmt.definedVars, HasVarsImp.definedVars, CmdExt.definedVars, Cmd.definedVars,
        List.cons_append, List.nil_append, List.append_assoc, List.mem_append,
        Bool.false_eq_true, ↓reduceIte] at hy ⊢ <;>
      grind
  refine ⟨(List.nodup_iff_count.2 D.once).sublist hsub, fun y hy => ?_⟩
  rcases D.cls y (hsub.subset hy) with ⟨b, j, e, ha, -⟩ | ⟨hy, -⟩ | ⟨z, hz⟩
  · exact .inr ⟨b, j, e, ha⟩
  · exact .inl (hdv y hy)
  · simp at hz

end

end WP
end Imperative
