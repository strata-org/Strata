/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.GuardFwdProps
public import Strata.Transform.Passive.Typed
public import Strata.Transform.Passive.WellTyped
import Strata.DL.Imperative.CmdSemanticsProps
import all Strata.Transform.GuardFwdProps

/-! # Guard forwarding keeps right-hand sides typed

The rewrite replaces a variable only by a candidate of the name: the recorded right-hand side of
its `init`, or an arm of it, which has the declared type of the name; and the annotations of the
input agree with the declared types. So under the typing laws `TypedOpLaws` the rewrite keeps the
type of an expression (`rw_typed`), and guard forwarding keeps every `init` of a list in passive
form typed when the input's annotations agree with a typing (`guardFwd_initsTyped`). When
`true` has the Boolean type, it also keeps the conditions of the `assume`s, `assert`s and
`cover`s Boolean (`guardFwd_condsTyped`).

Key theorems: `rw_typed`, `guardFwd_initsTyped`, `guardFwd_condsTyped`. -/

namespace Imperative
namespace GuardFwd

open WP BigStep

public section

variable {P : PureExpr} [BEq P.Ident] [Hashable P.Ident] [LawfulBEq P.Ident] [HasFvar P]
  [HasFvars P] [DecidableEq P.Ident] [HasBool P] [HasSubstFvar P] [WPLang P] [HasOps P]
  [GuardOps P] {Typ : P.Expr → P.Ty → Prop} {oe : WPOps.OpEnv P}

/-- Every recorded right-hand side of the scope has the type `Γ` gives its name. -/
@[expose] def ScopeTyped (Typ : P.Expr → P.Ty → Prop) (Γ : VarTyping P) (sc : Scope P) : Prop :=
  ∀ (y : P.Ident) d, sc[y]? = some (some d) → ∃ T, Γ y = some T ∧ Typ d T

/-- Every atomic rewrite recorded in the memo has the type `Γ` gives its name. -/
@[expose] def MemoTyped (Typ : P.Expr → P.Ty → Prop) (Γ : VarTyping P) (M : Memo P) : Prop :=
  ∀ (y : P.Ident) r, M[y]? = some (some r) → ∃ T, Γ y = some T ∧ Typ r T

omit [LawfulBEq P.Ident] [HasOps P] [GuardOps P] in
/-- A candidate of a name has the type `Γ` gives the name, when the scope's recorded right-hand
    sides do. -/
private theorem cand_typed (hL : TypedOpLaws Typ oe) {Γ : VarTyping P} {sc : Scope P}
    (hs : ScopeTyped Typ Γ sc) {K : Guards P} {y : P.Ident} {r : P.Expr}
    (h : cand sc K y = some r) : ∃ T, Γ y = some T ∧ Typ r T := by
  unfold cand at h
  repeat' split at h
  all_goals cases h
  all_goals obtain ⟨T, hT, hdT⟩ := hs y _ ‹_›
  all_goals first
    | exact ⟨T, hT, hdT⟩
    | exact ⟨T, hT, ((hL.iteView ‹_›).1 hdT).2.1⟩
    | exact ⟨T, hT, ((hL.iteView ‹_›).1 hdT).2.2⟩

omit [BEq P.Ident] [Hashable P.Ident] [LawfulBEq P.Ident] [GuardOps P] in
/-- A variable `y` of type `ty` whose annotations agree with `Γ` has the type `Γ` gives `y`. -/
private theorem var_ty (hL : TypedOpLaws Typ oe) {dv df : P.Ident → Bool} {Γ : VarTyping P}
    {e : P.Expr} {ty : P.Ty} {y : P.Ident} (hy : HasFvar.getFvar e = some y) (he : Typ e ty)
    (hok : ExprOK dv df Γ e) : Γ y = some ty :=
  hok.2.1 y ty (hL.getFvar hy he)

/-- **The rewrite keeps the type** of an expression whose annotations agree with `Γ`, when the
    recorded right-hand sides and the memo have the types `Γ` gives their names, and its memo
    keeps that. -/
theorem rw_typed (hS : GuardFwdSynLaws P) (hL : TypedOpLaws Typ oe) {dv df : P.Ident → Bool}
    {Γ : VarTyping P} {sc : Scope P} (hs : ScopeOK dv df Γ sc) (hst : ScopeTyped Typ Γ sc)
    (fuel : Nat) (deep cond : Bool) (cnt : Std.HashMap P.Ident Nat) (K : Guards P) (M : Memo P)
    (e : P.Expr) : MemoOK dv df Γ M → MemoTyped Typ Γ M → ExprOK dv df Γ e → ∀ {ty}, Typ e ty →
      Typ (rw fuel deep cond sc cnt K M e).1 ty ∧
        MemoTyped Typ Γ (rw fuel deep cond sc cnt K M e).2.2 := by
  have hins {M : Memo P} (hM : MemoTyped Typ Γ M) {y : P.Ident} {o : Option P.Expr}
      (ho : ∀ r, o = some r → ∃ T, Γ y = some T ∧ Typ r T) :
      MemoTyped Typ Γ (M.insert y o) := fun z r hz => by
    rw [Std.HashMap.getElem?_insert] at hz
    split at hz <;> first | exact hM z r hz | exact beq_iff_eq.1 ‹_› ▸ ho r (Option.some.inj hz)
  have hempty : MemoTyped Typ Γ ({} : Memo P) := fun _ _ h => by simp at h
  have hemptyOK : MemoOK dv df Γ ({} : Memo P) := fun _ _ h => by simp at h
  fun_induction rw fuel deep cond sc cnt K M e
  case case1 _ _ _ _ _ _ _ _ hv _ iht | case2 _ _ _ _ _ _ _ _ hv _ iht =>
    intro hM hMt he ty hT
    have hp := (ExprOK.iteView_iff hS hv).1 he
    have ht := (hL.iteView hv).1 hT
    first | exact iht hM hMt hp.2.1 ht.2.1 | exact iht hM hMt hp.2.2 ht.2.2
  case case3 de _ K M _ c _ _ hv _ _ _ _ hc' _ ihc iht
    | case4 de _ K M _ c _ _ hv _ _ _ _ hc' _ ihc iht =>
    intro hM hMt he ty hT
    have hp := (ExprOK.iteView_iff hS hv).1 he
    have ht := (hL.iteView hv).1 hT
    have hok := rw_ok hS hs ‹Nat› de true cnt K M c hM hp.1
    rw [hc'] at ihc hok
    obtain ⟨-, hMt1⟩ := ihc hM hMt hp.1 ht.1
    first | exact iht hok.2 hMt1 hp.2.1 ht.2.1 | exact iht hok.2 hMt1 hp.2.2 ht.2.2
  case case5 _ _ _ _ _ _ _ _ hv _ _ _ _ hc' _ _ _ _ _ _ ht' _ _ _ hf' ihc iht ihf =>
    intro hM hMt he ty hT
    have hp := (ExprOK.iteView_iff hS hv).1 he
    have ht := (hL.iteView hv).1 hT
    have h1 := (hc' ▸ ihc hM hMt hp.1 ht.1).1
    have h2 := (ht' ▸ iht hemptyOK hempty hp.2.1 ht.2.1).1
    have h3 := (hf' ▸ ihf hemptyOK hempty hp.2.2 ht.2.2).1
    refine ⟨?_, hempty⟩
    split <;> first | exact h2 | exact hL.ite.2 ⟨h1, h2, h3⟩
  case case6 de _ K M _ c t _ hv _ _ K1 M1 hc' _ _ _ _ _ ht' _ _ _ hf' ihc iht ihf =>
    intro hM hMt he ty hT
    have hp := (ExprOK.iteView_iff hS hv).1 he
    have ht := (hL.iteView hv).1 hT
    have hok1 := rw_ok hS hs ‹Nat› de true cnt K M c hM hp.1
    rw [hc'] at ihc hok1
    have hok2 := rw_ok hS hs ‹Nat› de false cnt K1 M1 t hok1.2 hp.2.1
    rw [ht'] at iht hok2
    obtain ⟨h1, hM1⟩ := ihc hM hMt hp.1 ht.1
    obtain ⟨h2, hM2⟩ := iht hok1.2 hM1 hp.2.1 ht.2.1
    obtain ⟨h3, hM3⟩ := hf' ▸ ihf hok2.2 hM2 hp.2.2 ht.2.2
    refine ⟨?_, hM3⟩
    split <;> first | exact h2 | exact hL.ite.2 ⟨h1, h2, h3⟩
  case case7 _ _ _ _ _ _ _ _ hy _ hr =>
    intro hM hMt he ty hT
    refine ⟨?_, hMt⟩
    split
    · obtain ⟨T, hT', hrT⟩ := cand_typed hL hst hr
      exact Option.some.inj ((var_ty hL hy hT he).symm.trans hT') ▸ hrT
    · exact hT
  case case8 | case10 | case13 => exact fun _ hMt _ _ hT => ⟨hT, hMt⟩
  case case9 _ _ _ _ _ _ _ _ hy _ _ _ hm =>
    intro hM hMt he ty hT
    obtain ⟨T, hT', hrT⟩ := hMt _ _ hm
    exact ⟨Option.some.inj ((var_ty hL hy hT he).symm.trans hT') ▸ hrT, hMt⟩
  case case11 _ _ _ _ _ _ _ _ _ hy _ _ _ _ _ hd _ _ _ hrw ha ih
    | case12 _ _ _ _ _ _ _ _ _ hy _ _ _ _ _ hd _ _ _ hrw ha ih =>
    intro hM hMt he ty hT
    simp only [wfParam] at hrw ih
    obtain ⟨T, hT', hdT⟩ := hst _ _ hd
    obtain rfl := Option.some.inj ((var_ty hL hy hT he).symm.trans hT')
    obtain ⟨h1, hM1⟩ := hrw ▸ ih hM hMt (hs _ _ hd) hdT
    first
    | exact ⟨h1, hins hM1 fun r h => by cases h; exact ⟨_, hT', h1⟩⟩
    | exact ⟨hT, hins hM1 fun r h => by cases h⟩
  case case14 K M e hv hy =>
    intro hM hMt he ty hT
    refine ⟨hL.substFn _ hT fun p hp v hv => ?_, hMt⟩
    obtain ⟨T, hT', hvT⟩ := cand_typed hL hst (Option.filter_eq_some_iff.1 hv).1
    exact Option.some.inj (hT'.symm.trans (he.2.1 p.1 p.2 hp)) ▸ hvT

omit [LawfulBEq P.Ident] [HasFvar P] [HasFvars P] [DecidableEq P.Ident] [HasBool P] [HasSubstFvar P]
  [WPLang P] [HasOps P]
  [GuardOps P] in
/-- The types of the recorded right-hand sides after an `init` of `x` at type `ty`: the typing
    grows by `x`, recorded with a right-hand side of type `ty`, if any. -/
private theorem scopeTyped_push [LawfulBEq P.Ident] {Γ : VarTyping P} {st : GSt P}
    (hs : ScopeTyped Typ Γ st.scope) {x : P.Ident} {ty : P.Ty} {val : Option P.Expr}
    (hv : ∀ d, val = some d → Typ d ty) :
    ScopeTyped Typ (Γ.extend [(x, ty)]) (st.push x val).scope := by
  intro y d hy
  simp only [GSt.push, Std.HashMap.getElem?_insert] at hy
  split at hy <;> rename_i hxy
  · obtain rfl : x = y := beq_iff_eq.1 hxy
    exact ⟨ty, by simp [VarTyping.extend_singleton], hv d (Option.some.inj hy)⟩
  · obtain ⟨T, hT, hdT⟩ := hs y d hy
    exact ⟨T, by simp [VarTyping.extend_singleton, hT, Ne.symm (mt beq_iff_eq.2 hxy)], hdT⟩

/-- **The walk keeps `init`s typed** on a list in passive form that is def-use well formed and
    whose annotations agree with `Γ`, when the recorded right-hand sides of the scope pass the
    checks and have the types `Γ` gives their names. -/
theorem walk_typed [LawfulHasFvars P] (hS : GuardFwdSynLaws P) (hL : TypedOpLaws Typ oe)
    (cx : Ctx P) (df : P.Ident → Bool) (ss : PStmts P) (hp : Block.passiveForm ss = true) :
    ∀ (st : GSt P) (dv : P.Ident → Bool) (Γ : VarTyping P),
    Block.defUseWellFormed dv df ss = true → Block.fvarTypesWellAnnotated Γ ss →
    ScopeOK dv df Γ st.scope → ScopeTyped Typ Γ st.scope → Block.initsTyped Typ ss →
    Block.initsTyped Typ (walk cx st ss).1 := by
  induction ss using Block.passiveForm.induct <;> intro st dv Γ hd hf hs hst hT
  case' case2 _ _ e _ _ _ => rcases e with e | _
  all_goals simp only [walk, walkS, Block.defUseWellFormed, Stmt.defUseWellFormed,
    Block.fvarTypesWellAnnotated, Stmt.fvarTypesWellAnnotated, HasVarsImp.readVars,
    CmdExt.readVars, Cmd.getVars, ExprOrNondet.getVars, HasVarsImp.modifiedVars,
    CmdExt.modifiedVars, Cmd.modifiedVars, HasVarsImp.definedVars, CmdExt.definedVars,
    Cmd.definedVars, HasOpsImp.getOps, CmdExt.getOps, Cmd.getOps, ExprOrNondet.getOps,
    Stmt.definedVars, HasTypedVarsImp.typedReadVars, CmdExt.typedReadVars, Cmd.getTypedVars,
    ExprOrNondet.getTypedVars, Stmt.typedDefinedVars, HasTypedVarsImp.typedDefinedVars,
    CmdExt.typedDefinedVars, Cmd.typedDefinedVars, Bool.and_eq_true, List.all_eq_true,
    List.all_cons, List.all_nil, Bool.and_true, decide_eq_true_eq, ↓reduceIte, Block.initsTyped,
    Stmt.initsTyped, CmdExt.initsTyped, Block.passiveForm] at hp hd hf hT ⊢
  case case2.det x _ _ _ ih =>
    obtain ⟨⟨⟨hfv, hx⟩, hops⟩, hrest⟩ := hd
    have hok : ExprOK dv df Γ e := ⟨hfv, hf.1, hops⟩
    have he' := (rw_ok hS hs (initFuel cx st x) false false cx.cnt ∅ ∅ e
      (fun _ _ h => by simp at h) hok).1
    have ht' := (rw_typed hS hL hs hst (initFuel cx st x) false false cx.cnt ∅ ∅ e
      (fun _ _ h => by simp at h) (fun _ _ h => by simp at h) hok hT.1).1
    refine ⟨ht', ih hp _ _ _ hrest hf.2 (scopeOK_push hs (Bool.eq_false_iff.2 hx)
      (val := if recordable cx st.scope (rwRoot (initFuel cx st x) st.scope cx.cnt e) = true
        then some (rwRoot (initFuel cx st x) st.scope cx.cnt e) else none)
      (fun d hd => by split at hd <;> cases hd; exact he') fun z hz => by simp [hz])
      (scopeTyped_push hst fun d hd => by split at hd <;> cases hd; exact ht') hT.2⟩
  case case2.nondet ih =>
    exact ⟨trivial, ih hp _ _ _ hd.2 hf.2
      (scopeOK_push hs (Bool.eq_false_iff.2 hd.1.2) (val := none) (fun _ h => by cases h)
        fun z hz => by simp [hz]) (scopeTyped_push hst (val := none) fun _ h => by cases h)
      hT.2⟩
  case case3 ih | case4 ih | case5 ih =>
    exact ⟨trivial, ih hp st _ _ hd.2 hf.2 (hs.mono (fun z hz => by simp [hz]) fun _ _ => rfl)
      hst hT.2⟩
  case case6 t e _ _ iht ihe ihr =>
    obtain ⟨⟨hpt, hpe⟩, hpr⟩ := hp
    obtain ⟨⟨⟨-, hdt⟩, hde⟩, hdr⟩ := hd
    obtain ⟨⟨-, hft, hfe⟩, hfr⟩ := hf
    obtain ⟨t1, k1, s1⟩ := (walk_frame cx st t).undo
    obtain ⟨-, -, s2⟩ := (GFrame.congr t1 k1 s1 (walk_frame cx _ e)).undo
    have hc {st' : GSt P} (h : ∀ x : P.Ident, st'.scope[x]? = st.scope[x]?) :
        ScopeOK dv df Γ st'.scope := fun y d hy => hs y d ((h y).symm.trans hy)
    have hct {st' : GSt P} (h : ∀ x : P.Ident, st'.scope[x]? = st.scope[x]?) :
        ScopeTyped Typ Γ st'.scope := fun y d hy => hst y d ((h y).symm.trans hy)
    exact ⟨⟨iht hpt st dv Γ hdt hft hs hst hT.1.1, ihe hpe _ dv Γ hde hfe (hc s1) (hct s1)
      hT.1.2⟩, ihr hpr _ _ _ hdr hfr ((hc s2).mono (fun z hz => by simp [hz]) fun _ _ => rfl)
      (hct s2) hT.2⟩
  case case7 => simp_all

/-- **Guard forwarding keeps `init`s typed.** Under the typing laws `TypedOpLaws`, on a list in
    passive form that is def-use well formed (from the defined-names predicate `dv` and the
    declared-functions predicate `df`) and whose annotations agree with a typing `Γ`, every
    `init` of `guardFwd ss` has a right-hand side of its declared type when every `init` of `ss`
    has. -/
theorem guardFwd_initsTyped [LawfulHasFvars P] (hS : GuardFwdSynLaws P) (hL : TypedOpLaws Typ oe)
    {ss : PStmts P} (hp : Block.passiveForm ss = true) {dv df : P.Ident → Bool}
    {Γ : VarTyping P} (hd : Block.defUseWellFormed dv df ss = true)
    (hf : Block.fvarTypesWellAnnotated Γ ss) (hT : Block.initsTyped Typ ss) :
    Block.initsTyped Typ (guardFwd ss) :=
  walk_typed hS hL _ df ss hp {} dv Γ hd hf (fun _ _ h => by simp at h)
    (fun _ _ h => by simp at h) hT


omit [LawfulBEq P.Ident] [HasOps P] in
/-- **The exact rewrite keeps a Boolean condition Boolean**, when its annotations agree with `Γ`,
    the recorded right-hand sides have the types `Γ` gives their names and `true` is Boolean. -/
private theorem rwExact_typed (hL : TypedOpLaws Typ oe) (htt : Typ HasBool.tt HasBool.boolTy)
    {Γ : VarTyping P} {sc : Scope P} (hst : ScopeTyped Typ Γ sc) {e : P.Expr}
    (ha : Γ.annotates (HasFvars.getTypedFvars e)) (he : Typ e HasBool.boolTy) :
    Typ (rwExact sc e) HasBool.boolTy := by
  have h' := hL.substFn (fun y => match sc[y]? with
    | some (some d) => if atomic d then some d else none
    | _ => none) he fun p hp v hv => by
      split at hv <;> try cases hv
      split at hv <;> cases hv
      obtain ⟨T, hT, hdT⟩ := hst _ _ ‹_›
      exact Option.some.inj (hT.symm.trans (ha p.1 p.2 hp)) ▸ hdT
  unfold rwExact
  dsimp only
  repeat' split
  all_goals first | exact h' | exact htt

/-- **The walk keeps the conditions Boolean** on a list in passive form that is def-use well
    formed, whose annotations agree with `Γ` and whose `init`s are typed, when the recorded
    right-hand sides of the scope pass the checks and have the types `Γ` gives their names, and
    `true` is Boolean: every `assume`, `assert` and `cover` of the output has a Boolean condition
    when every one of the input has. -/
private theorem walk_condsTyped [LawfulHasFvars P] (hS : GuardFwdSynLaws P)
    (hL : TypedOpLaws Typ oe) (htt : Typ HasBool.tt HasBool.boolTy) (cx : Ctx P)
    (df : P.Ident → Bool) (ss : PStmts P) (hp : Block.passiveForm ss = true) :
    ∀ (st : GSt P) (dv : P.Ident → Bool) (Γ : VarTyping P),
    Block.defUseWellFormed dv df ss = true → Block.fvarTypesWellAnnotated Γ ss →
    ScopeOK dv df Γ st.scope → ScopeTyped Typ Γ st.scope → Block.initsTyped Typ ss →
    Block.condsTyped Typ ss → Block.condsTyped Typ (walk cx st ss).1 := by
  induction ss using Block.passiveForm.induct <;> intro st dv Γ hd hf hs hst hT hc
  case' case2 _ _ e _ _ _ => rcases e with e | _
  all_goals simp only [walk, walkS, Block.defUseWellFormed, Stmt.defUseWellFormed,
    Block.fvarTypesWellAnnotated, Stmt.fvarTypesWellAnnotated, HasVarsImp.readVars,
    CmdExt.readVars, Cmd.getVars, ExprOrNondet.getVars, HasVarsImp.modifiedVars,
    CmdExt.modifiedVars, Cmd.modifiedVars, HasVarsImp.definedVars, CmdExt.definedVars,
    Cmd.definedVars, HasOpsImp.getOps, CmdExt.getOps, Cmd.getOps, ExprOrNondet.getOps,
    Stmt.definedVars, HasTypedVarsImp.typedReadVars, CmdExt.typedReadVars, Cmd.getTypedVars,
    ExprOrNondet.getTypedVars, Stmt.typedDefinedVars, HasTypedVarsImp.typedDefinedVars,
    CmdExt.typedDefinedVars, Cmd.typedDefinedVars, Bool.and_eq_true, List.all_eq_true,
    List.all_cons, List.all_nil, Bool.and_true, decide_eq_true_eq, ↓reduceIte, Block.initsTyped,
    Stmt.initsTyped, CmdExt.initsTyped, Block.condsTyped, Stmt.condsTyped, CmdExt.condsTyped,
    Block.passiveForm] at hp hd hf hT hc ⊢
  case case2.det x _ _ _ ih =>
    obtain ⟨⟨⟨hfv, hx⟩, hops⟩, hrest⟩ := hd
    have hok : ExprOK dv df Γ e := ⟨hfv, hf.1, hops⟩
    have he' := (rw_ok hS hs (initFuel cx st x) false false cx.cnt ∅ ∅ e
      (fun _ _ h => by simp at h) hok).1
    have ht' := (rw_typed hS hL hs hst (initFuel cx st x) false false cx.cnt ∅ ∅ e
      (fun _ _ h => by simp at h) (fun _ _ h => by simp at h) hok hT.1).1
    refine ⟨trivial, ih hp _ _ _ hrest hf.2 (scopeOK_push hs (Bool.eq_false_iff.2 hx)
      (val := if recordable cx st.scope (rwRoot (initFuel cx st x) st.scope cx.cnt e) = true
        then some (rwRoot (initFuel cx st x) st.scope cx.cnt e) else none)
      (fun d hd => by split at hd <;> cases hd; exact he') fun z hz => by simp [hz])
      (scopeTyped_push hst fun d hd => by split at hd <;> cases hd; exact ht') hT.2 hc.2⟩
  case case2.nondet ih =>
    exact ⟨trivial, ih hp _ _ _ hd.2 hf.2
      (scopeOK_push hs (Bool.eq_false_iff.2 hd.1.2) (val := none) (fun _ h => by cases h)
        fun z hz => by simp [hz]) (scopeTyped_push hst (val := none) fun _ h => by cases h)
      hT.2 hc.2⟩
  case case3 _ e _ _ ih =>
    obtain ⟨⟨hfv, hops⟩, hrest⟩ := hd
    exact ⟨(rw_typed hS hL hs hst st.trailLen false false cx.cnt ∅ ∅ e
      (fun _ _ h => by simp at h) (fun _ _ h => by simp at h) ⟨hfv, hf.1, hops⟩ hc.1).1,
      ih hp st _ _ hrest hf.2 (hs.mono (fun z hz => by simp [hz]) fun _ _ => rfl) hst hT.2 hc.2⟩
  case case4 _ e _ _ ih | case5 _ e _ _ ih =>
    exact ⟨rwExact_typed hL htt hst hf.1 hc.1, ih hp st _ _ hd.2 hf.2
      (hs.mono (fun z hz => by simp [hz]) fun _ _ => rfl) hst hT.2 hc.2⟩
  case case6 t e _ _ iht ihe ihr =>
    obtain ⟨⟨hpt, hpe⟩, hpr⟩ := hp
    obtain ⟨⟨⟨-, hdt⟩, hde⟩, hdr⟩ := hd
    obtain ⟨⟨-, hft, hfe⟩, hfr⟩ := hf
    obtain ⟨t1, k1, s1⟩ := (walk_frame cx st t).undo
    obtain ⟨-, -, s2⟩ := (GFrame.congr t1 k1 s1 (walk_frame cx _ e)).undo
    have hcs {st' : GSt P} (h : ∀ x : P.Ident, st'.scope[x]? = st.scope[x]?) :
        ScopeOK dv df Γ st'.scope := fun y d hy => hs y d ((h y).symm.trans hy)
    have hct {st' : GSt P} (h : ∀ x : P.Ident, st'.scope[x]? = st.scope[x]?) :
        ScopeTyped Typ Γ st'.scope := fun y d hy => hst y d ((h y).symm.trans hy)
    exact ⟨⟨iht hpt st dv Γ hdt hft hs hst hT.1.1 hc.1.1, ihe hpe _ dv Γ hde hfe (hcs s1)
      (hct s1) hT.1.2 hc.1.2⟩, ihr hpr _ _ _ hdr hfr
      ((hcs s2).mono (fun z hz => by simp [hz]) fun _ _ => rfl) (hct s2) hT.2 hc.2⟩
  case case7 => simp_all

/-- **Guard forwarding keeps the conditions Boolean.** Under the typing laws `TypedOpLaws` of a
    typing predicate `Typ` that types `true` as Boolean, on a list in passive form that is def-use
    well formed (from `dv` and `df`), whose annotations agree with a typing `Γ` and whose `init`s
    are typed, every `assume`, `assert` and `cover` of `guardFwd ss` has a Boolean condition when
    every one of `ss` has. -/
theorem guardFwd_condsTyped [LawfulHasFvars P] (hS : GuardFwdSynLaws P)
    (hL : TypedOpLaws Typ oe) (htt : Typ HasBool.tt HasBool.boolTy)
    {ss : PStmts P} (hp : Block.passiveForm ss = true) {dv df : P.Ident → Bool}
    {Γ : VarTyping P} (hd : Block.defUseWellFormed dv df ss = true)
    (hf : Block.fvarTypesWellAnnotated Γ ss) (hT : Block.initsTyped Typ ss)
    (hc : Block.condsTyped Typ ss) : Block.condsTyped Typ (guardFwd ss) :=
  walk_condsTyped hS hL htt _ df ss hp {} dv Γ hd hf (fun _ _ h => by simp at h)
    (fun _ _ h => by simp at h) hT hc

end -- public section

end GuardFwd
end Imperative
