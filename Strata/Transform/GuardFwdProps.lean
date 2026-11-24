/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.GuardFwd
public import Strata.DL.Imperative.CmdSemanticsProps

/-! # Properties of guard forwarding

The rewrite gives back the guard map it was given, up to lookups (`rw_guards`).  The walk only
extends the undo log, and undoing the extension gives back the lookups of the scope it started
from (`walk_frame`, `GFrame.undo`).

On a list in passive form the output has the shape of the input: it is in passive form, defines
the same names with the same types, and is in tree form when the input is (`walk_shape`).  Every
expression of the output has its free variables, annotated occurrences and operators among those
of the input and of the recorded right-hand sides it reads (`rw_ok`), so the output passes the
def-use and annotation checks of the initial-environment gate wherever the input does
(`walk_gate`).

Key theorems: `rw_guards`, `walk_frame`, `GFrame.undo`, `walk_shape`, `rw_ok`, `walk_gate`.

Key definitions: `GFrame`, `GuardFwdSynLaws`, `ExprOK`, `ScopeOK`. -/

namespace Imperative
namespace GuardFwd

open WP BigStep

public section

variable {P : PureExpr} [BEq P.Ident] [Hashable P.Ident]

/-- The rewrite gives back the guard map it was given, up to lookups. -/
theorem rw_guards [LawfulBEq P.Ident] [HasBool P] [HasFvar P] [WPOps P] [GuardOps P]
    (fuel : Nat) (deep cond : Bool) (sc : Scope P) (cnt : Std.HashMap P.Ident Nat) (K : Guards P)
    (M : Memo P) (e : P.Expr) :
    ∀ x : P.Ident, (rw fuel deep cond sc cnt K M e).2.1[x]? = K[x]? := by
  fun_induction rw fuel deep cond sc cnt K M e <;> intro x <;> grind

/-! ## The undo log -/

/-- Undoing the same log in two scopes with the same lookups gives the same log and two scopes
    with the same lookups. -/
private theorem undoGo_congr [LawfulBEq P.Ident] :
    ∀ (k : Nat) (tr : List (P.Ident × Option (Option P.Expr)))
    {sc1 sc2 : Scope P}, (∀ x : P.Ident, sc1[x]? = sc2[x]?) →
    (undoGo k tr sc1).1 = (undoGo k tr sc2).1 ∧
      ∀ x : P.Ident, (undoGo k tr sc1).2[x]? = (undoGo k tr sc2).2[x]?
  | 0, _, _, _, h | _ + 1, [], _, _, h => ⟨rfl, h⟩
  | k + 1, (x, old) :: tr, _, _, h => undoGo_congr k tr fun y => by cases old <;> grind [undoGo]

/-- Undoing the `a.length + k` newest entries of `a ++ b` undoes `a`, then `k` entries of `b`. -/
private theorem undoGo_append : ∀ (a b : List (P.Ident × Option (Option P.Expr)))
    (sc : Scope P) (k : Nat),
    undoGo (a.length + k) (a ++ b) sc = undoGo k b (undoGo a.length a sc).2
  | [], _, _, _ => by simp [undoGo]
  | (x, old) :: a, b, sc, k => by simpa [Nat.add_right_comm, undoGo] using undoGo_append a b _ k

/-- The walk from `st` to `st'` extends the undo log by entries whose undoing gives back the
    lookups of the scope of `st`. -/
@[expose] def GFrame (st st' : GSt P) : Prop :=
  ∃ ext, st'.trail = ext ++ st.trail ∧ st'.trailLen = st.trailLen + ext.length ∧
    ∀ x : P.Ident, (undoGo ext.length ext st'.scope).2[x]? = st.scope[x]?

/-- A state frames itself. -/
theorem GFrame.refl (st : GSt P) : GFrame st st := ⟨[], rfl, rfl, fun _ => rfl⟩

/-- Frames compose. -/
theorem GFrame.trans [LawfulBEq P.Ident] {s1 s2 s3 : GSt P} (h1 : GFrame s1 s2)
    (h2 : GFrame s2 s3) :
    GFrame s1 s3 := by
  obtain ⟨e1, t1, k1, u1⟩ := h1
  obtain ⟨e2, t2, k2, u2⟩ := h2
  refine ⟨e2 ++ e1, by simp [t2, t1], by rw [k2, k1, List.length_append]; omega, fun x => ?_⟩
  rw [List.length_append, undoGo_append, (undoGo_congr _ _ u2).2, u1]

/-- Entering a name in the scope frames the state. -/
theorem GFrame.push [LawfulBEq P.Ident] (st : GSt P) (x : P.Ident) (v : Option P.Expr) :
    GFrame st (st.push x v) := by
  simp only [GSt.push]
  exact ⟨[_], rfl, rfl, fun y => by cases h : st.scope[x]? <;> grind [undoGo]⟩

/-- Undoing, after a walk from `st`, the entries logged since `st` gives back the log and its
    length of `st` and the lookups of its scope. -/
theorem GFrame.undo {st st' : GSt P} (h : GFrame st st') :
    (st'.undoTo st.trailLen).trail = st.trail ∧ (st'.undoTo st.trailLen).trailLen = st.trailLen ∧
      ∀ x : P.Ident, (st'.undoTo st.trailLen).scope[x]? = st.scope[x]? := by
  obtain ⟨ext, ht, hk, hu⟩ := h
  have hg : undoGo (st'.trailLen - st.trailLen) st'.trail st'.scope =
      undoGo 0 st.trail (undoGo ext.length ext st'.scope).2 := by
    rw [hk, ht, Nat.add_sub_cancel_left]
    exact undoGo_append ext st.trail st'.scope 0
  refine ⟨?_, rfl, fun x => ?_⟩
  all_goals simp only [GSt.undoTo, hg, undoGo, hu]

/-- A state with the log of `st` and the lookups of its scope frames what `st` frames. -/
theorem GFrame.congr {st st1 st' : GSt P} (ht : st1.trail = st.trail)
    (hk : st1.trailLen = st.trailLen) (hs : ∀ x : P.Ident, st1.scope[x]? = st.scope[x]?)
    (h : GFrame st1 st') : GFrame st st' := by
  obtain ⟨ext, t1, k1, u1⟩ := h
  exact ⟨ext, ht ▸ t1, hk ▸ k1, fun x => (u1 x).trans (hs x)⟩

section Walk

variable [LawfulBEq P.Ident] [HasBool P] [HasFvar P] [HasFvars P] [WPOps P] [GuardOps P]

mutual
/-- **The walk frames the state**: it only extends the undo log, by entries whose undoing gives
    back the lookups of the scope it started from. -/
theorem walk_frame (cx : Ctx P) : ∀ (st : GSt P) (ss : PStmts P), GFrame st (walk cx st ss).2
  | st, [] => GFrame.refl st
  | st, s :: rest => (walkS_frame cx st s).trans (walk_frame cx _ rest)
/-- The walk over a statement frames the state. -/
private theorem walkS_frame (cx : Ctx P) : ∀ (st : GSt P) (s : PStmt P), GFrame st (walkS cx st s).2
  | st, .cmd (.cmd (.init x ty (.det e) md)) => GFrame.push _ _ _
  | st, .cmd (.cmd (.init x ty .nondet md)) => GFrame.push _ _ _
  | st, .cmd (.cmd (.set _ _ _)) | st, .cmd (.cmd (.assume _ _ _))
  | st, .cmd (.cmd (.assert _ _ _)) | st, .cmd (.cmd (.cover _ _ _)) | st, .cmd (.call _ _ _ _)
  | st, .loop _ _ _ _ _ | st, .exit _ _ | st, .typeDecl _ _ => GFrame.refl st
  | st, .ite c tss ess md => by
    obtain ⟨t1, k1, s1⟩ := (walk_frame cx st tss).undo
    exact ⟨[], (GFrame.congr t1 k1 s1 (walk_frame cx _ ess)).undo⟩
  | st, .block l ss md => ⟨[], (walk_frame cx st ss).undo⟩
end

/-! ## The shape of the output

On a list in passive form the walk keeps every statement and only rewrites `init` right-hand
sides and `assume` conditions, so the output is in passive form and has the definitions, the
declared types and the tree shape of the input. -/

omit [BEq P.Ident] [Hashable P.Ident] [LawfulBEq P.Ident] [HasFvar P] [HasFvars P] [WPOps P]
  [HasBool P] [GuardOps P] in
/-- A list in passive form has only commands and `ite *` at any depth. -/
theorem Block.passiveForm_allSubstmts {f : Stmt P (CmdExt P) → Bool}
    (hc : ∀ c : Cmd P, f (.cmd (.cmd c)) = true) (hi : ∀ t e md, f (.ite .nondet t e md) = true) :
    ∀ {ss : Block P (CmdExt P)}, Block.passiveForm ss = true → Block.allSubstmts f ss = true := by
  intro ss h
  induction ss using Block.passiveForm.induct <;>
    simp_all [Block.passiveForm, Block.allSubstmts, Stmt.allSubstmts]

omit [LawfulBEq P.Ident] in
/-- The walk keeps an empty list empty and a nonempty one nonempty. -/
private theorem walk_isEmpty (cx : Ctx P) (st : GSt P) (ss : PStmts P) :
    (walk cx st ss).1.isEmpty = ss.isEmpty := by
  cases ss <;> rfl

omit [LawfulBEq P.Ident] in
/-- **The shape of the output.**  On a list in passive form, the output of the walk is in
    passive form, defines the same names with the same declared types, and is in tree form when
    the input is. -/
theorem walk_shape (cx : Ctx P) (ss : PStmts P) (hp : Block.passiveForm ss = true) :
    ∀ st : GSt P, Block.passiveForm (walk cx st ss).1 = true ∧
      (∀ b, Block.definedVars (walk cx st ss).1 b = Block.definedVars ss b) ∧
      Block.initTypes (walk cx st ss).1 = Block.initTypes ss ∧
      Block.treeForm (walk cx st ss).1 = Block.treeForm ss := by
  induction ss using Block.passiveForm.induct <;> intro st
  case' case2 _ _ e _ _ _ => rcases e with e | _
  all_goals simp_all [walk, walkS, Block.passiveForm, Block.treeForm, Block.definedVars,
    walk_isEmpty, Stmt.definedVars, Block.initTypes, Stmt.initTypes, HasVarsImp.definedVars,
    CmdExt.definedVars, Cmd.definedVars, HasInitTypesImp.initTypes, CmdExt.initTypes, Cmd.initTypes]

/-! ## Free variables, annotations and operators of the output

Every expression of the output is built from expressions of the input: a rewritten expression has
its free variables, annotated occurrences and operators among those of the input expression and
of the recorded right-hand sides it reads (`rw_ok`).  So the output passes the def-use check and
the annotation check of the initial-environment gate wherever the input does (`walk_gate`). -/

end Walk

section Gate

variable [LawfulBEq P.Ident] [HasFvar P] [HasFvars P] [DecidableEq P.Ident] [HasBool P]
  [HasSubstFvar P] [WPLang P] [HasOps P] [GuardOps P]

/-- The laws of the syntax of expressions that the gate of guard forwarding's output needs: the
    annotated occurrences and the operators of a conditional are those of its parts, a
    substitution by images without operators adds no operator, a variable or a literal has no
    operator, and the literal `true` has no annotated variable and no operator. -/
structure GuardFwdSynLaws (P : PureExpr) [DecidableEq P.Ident] [HasBool P] [HasFvar P]
    [HasFvars P] [HasSubstFvar P] [WPLang P] [HasOps P] [GuardOps P] : Prop where
  typed_ite : ∀ (c t f : P.Expr) p, p ∈ HasFvars.getTypedFvars (WPOps.ite c t f) ↔
    p ∈ HasFvars.getTypedFvars c ∨ p ∈ HasFvars.getTypedFvars t ∨ p ∈ HasFvars.getTypedFvars f
  /-- The operators of a conditional recognized by `iteView?` are those of the canonical
      conditional of its parts; the root location carries no operator. -/
  ops_iteView : ∀ {e c t f : P.Expr} (o), WPOps.iteView? e = some (c, t, f) →
    (o ∈ HasOps.getOps e ↔ o ∈ HasOps.getOps (WPOps.ite c t f))
  ops_ite : ∀ (c t f : P.Expr) o, o ∈ HasOps.getOps (WPOps.ite c t f) ↔
    o ∈ HasOps.getOps c ∨ o ∈ HasOps.getOps t ∨ o ∈ HasOps.getOps f
  ops_substFn : ∀ (e : P.Expr) (g : P.Ident → Option P.Expr),
    (∀ x r, g x = some r → HasOps.getOps r = []) →
    ∀ o ∈ HasOps.getOps (WPOps.substFn e g), o ∈ HasOps.getOps e
  ops_atomic : ∀ r : P.Expr, atomic r = true → HasOps.getOps r = []
  typed_tt : HasFvars.getTypedFvars (HasBool.tt (P := P)) = []
  ops_tt : HasOps.getOps (HasBool.tt (P := P)) = []

/-- The expression `e` passes the checks of the gate at a position where the names `dv` are
    defined, the operators `df` declared and `Γ` types the variables: its free variables are
    defined, its annotated occurrences agree with `Γ`, and its operators are declared. -/
@[expose] def ExprOK (dv df : P.Ident → Bool) (Γ : VarTyping P) (e : P.Expr) : Prop :=
  (∀ z ∈ HasFvars.getFvars e, dv z = true) ∧ Γ.annotates (HasFvars.getTypedFvars e) ∧
    ∀ o ∈ HasOps.getOps e, df o = true

omit [LawfulBEq P.Ident] [BEq P.Ident] [Hashable P.Ident] in
/-- A conditional passes the checks exactly when its parts do. -/
theorem ExprOK.ite_iff (hS : GuardFwdSynLaws P) {dv df : P.Ident → Bool} {Γ : VarTyping P}
    {c t f : P.Expr} : ExprOK dv df Γ (WPOps.ite c t f) ↔
      ExprOK dv df Γ c ∧ ExprOK dv df Γ t ∧ ExprOK dv df Γ f := by
  simp only [ExprOK, WPLang.getFvars_ite, hS.typed_ite, hS.ops_ite, VarTyping.annotates]
  grind

omit [LawfulBEq P.Ident] [BEq P.Ident] [Hashable P.Ident] in
/-- **A conditional recognized by `iteView?` passes the checks exactly when its parts do.**  The
    three ingredients of `ExprOK` — the free variables, the annotated occurrences and the
    operators — are each independent of a conditional's root location, so the checks transport
    from the recognized conditional to the canonical conditional of its parts. -/
theorem ExprOK.iteView_iff (hS : GuardFwdSynLaws P) {dv df : P.Ident → Bool} {Γ : VarTyping P}
    {e c t f : P.Expr} (hv : WPOps.iteView? e = some (c, t, f)) :
    ExprOK dv df Γ e ↔ ExprOK dv df Γ c ∧ ExprOK dv df Γ t ∧ ExprOK dv df Γ f := by
  simpa only [ExprOK, WPLang.iteView?_getFvars _ hv, WPLang.typedFvars_iteView _ hv,
    VarTyping.annotates, hS.ops_iteView _ hv] using ExprOK.ite_iff hS

omit [LawfulBEq P.Ident] [BEq P.Ident] [Hashable P.Ident] [DecidableEq P.Ident] [HasBool P]
  [HasSubstFvar P] [WPLang P] [GuardOps P] in
/-- The checks pass at a position with more defined names and a typing that agrees on the free
    variables. -/
theorem ExprOK.mono [LawfulHasFvars P] {dv dv' df : P.Ident → Bool} {Γ Γ' : VarTyping P}
    {e : P.Expr} (hd : ∀ z, dv z = true → dv' z = true)
    (hΓ : ∀ z, dv z = true → Γ' z = Γ z) (h : ExprOK dv df Γ e) : ExprOK dv' df Γ' e :=
  ⟨fun z hz => hd z (h.1 z hz), fun x ty hx =>
    (hΓ x (h.1 x (LawfulHasFvars.mem_getFvars_of_typed e x ty hx))).trans (h.2.1 x ty hx), h.2.2⟩

/-- Every recorded right-hand side of the scope passes the checks. -/
@[expose] def ScopeOK (dv df : P.Ident → Bool) (Γ : VarTyping P) (sc : Scope P) : Prop :=
  ∀ (y : P.Ident) d, sc[y]? = some (some d) → ExprOK dv df Γ d

/-- Every atomic rewrite recorded in the memo passes the checks. -/
@[expose] def MemoOK (dv df : P.Ident → Bool) (Γ : VarTyping P) (M : Memo P) : Prop :=
  ∀ (y : P.Ident) r, M[y]? = some (some r) → ExprOK dv df Γ r

omit [LawfulBEq P.Ident] in
/-- A candidate passes the checks when the scope does. -/
private theorem cand_ok (hS : GuardFwdSynLaws P) {dv df : P.Ident → Bool} {Γ : VarTyping P}
    {sc : Scope P} (hs : ScopeOK dv df Γ sc) {K : Guards P} {y : P.Ident} {r : P.Expr}
    (h : cand sc K y = some r) : ExprOK dv df Γ r := by
  unfold cand at h
  repeat' split at h
  all_goals cases h
  all_goals first
    | exact hs y _ ‹_›
    | exact ((ExprOK.iteView_iff hS ‹_›).1 (hs y _ ‹_›)).2.1
    | exact ((ExprOK.iteView_iff hS ‹_›).1 (hs y _ ‹_›)).2.2

omit [LawfulBEq P.Ident] [Hashable P.Ident] [WPLang P] [HasBool P] [HasFvar P] [HasSubstFvar P]
  [HasFvars P] [BEq P.Ident] [HasOps P] [GuardOps P] in
/-- The finite map of the images of a lookup function on a list finds the image of each name of
    the list. -/
theorem find?_filterMap (look : P.Ident → Option P.Expr) :
    ∀ (L : List P.Ident) (x : P.Ident), (x ∈ L ∨ look x = none) →
      Map.find? (L.filterMap fun y => (look y).map (y, ·)) x = look x
  | [], x, h => by simp_all [Map.find?]
  | y :: L, x, h => by cases hy : look y <;> grind [Map.find?, find?_filterMap look L x]

omit [LawfulBEq P.Ident] [BEq P.Ident] [Hashable P.Ident] in
/-- A substitution by atomic images that pass the checks passes them when its input does. -/
private theorem substFn_ok (hS : GuardFwdSynLaws P) {dv df : P.Ident → Bool} {Γ : VarTyping P}
    {e : P.Expr} (look : P.Ident → Option P.Expr)
    (hlook : ∀ {k r}, look k = some r → ExprOK dv df Γ r ∧ atomic r = true)
    (he : ExprOK dv df Γ e) : ExprOK dv df Γ (WPOps.substFn e look) := by
  let sm := (HasFvars.getFvars e).filterMap fun y => (look y).map (y, ·)
  have hfind : ∀ x ∈ HasFvars.getFvars e, look x = Map.find? sm x :=
    fun x hx => (Map.find?_filterMap_self look _ x hx).symm
  refine ⟨fun z hz => ?_, fun x ty hx => ?_, fun o ho => he.2.2 o ?_⟩
  · rw [WPLang.substFn_eq e look sm hfind] at hz
    rcases WPLang.getFvars_substFvars e sm z hz with ⟨hz, -⟩ | ⟨x, v, hx, hv, hz⟩
    · exact he.1 z hz
    · exact (hlook ((hfind x hx).trans hv)).1.1 z hz
  · rcases WPLang.getTypedFvars_substFn e look (x, ty) hx with ⟨hx, -⟩ | ⟨z, v, -, hv, hx⟩
    · exact he.2.1 x ty hx
    · exact (hlook hv).1.2.1 x ty hx
  · exact hS.ops_substFn e look (fun x r h => hS.ops_atomic r (hlook h).2) o ho

/-- **The rewrite passes the checks** when its input, the recorded right-hand sides and the memo
    do, and its memo passes them. -/
theorem rw_ok (hS : GuardFwdSynLaws P) {dv df : P.Ident → Bool} {Γ : VarTyping P}
    {sc : Scope P} (hs : ScopeOK dv df Γ sc) (fuel : Nat) (deep cond : Bool)
    (cnt : Std.HashMap P.Ident Nat) (K : Guards P) (M : Memo P) (e : P.Expr) :
    MemoOK dv df Γ M → ExprOK dv df Γ e →
      ExprOK dv df Γ (rw fuel deep cond sc cnt K M e).1 ∧
        MemoOK dv df Γ (rw fuel deep cond sc cnt K M e).2.2 := by
  have hins {M : Memo P} (hM : MemoOK dv df Γ M) {y : P.Ident} {o : Option P.Expr}
      (ho : ∀ r, o = some r → ExprOK dv df Γ r) : MemoOK dv df Γ (M.insert y o) := by grind [MemoOK]
  fun_induction rw fuel deep cond sc cnt K M e
  case case1 _ _ _ _ _ _ _ _ hv _ iht | case2 _ _ _ _ _ _ _ _ hv _ iht =>
    intro hM he
    have hp := (ExprOK.iteView_iff hS hv).1 he
    first | exact iht hM hp.2.1 | exact iht hM hp.2.2
  case case3 _ _ _ _ _ _ _ _ hv _ _ _ _ hc' _ ihc iht
    | case4 _ _ _ _ _ _ _ _ hv _ _ _ _ hc' _ ihc iht =>
    intro hM he
    have hp := (ExprOK.iteView_iff hS hv).1 he
    obtain ⟨-, hM1⟩ := hc' ▸ ihc hM hp.1
    first | exact iht hM1 hp.2.1 | exact iht hM1 hp.2.2
  case case5 _ _ _ _ _ _ _ _ hv _ _ _ _ hc' _ _ _ _ _ _ ht' _ _ _ hf' ihc iht ihf =>
    intro hM he
    have hp := (ExprOK.iteView_iff hS hv).1 he
    have h1 := (hc' ▸ ihc hM hp.1).1
    have h2 := (ht' ▸ iht (fun _ _ h => by simp at h) hp.2.1).1
    have h3 := (hf' ▸ ihf (fun _ _ h => by simp at h) hp.2.2).1
    refine ⟨?_, fun _ _ h => by simp at h⟩
    split <;> first | exact h2 | exact (ExprOK.ite_iff hS).2 ⟨h1, h2, h3⟩
  case case6 _ _ _ _ _ _ _ _ hv _ _ _ _ hc' _ _ _ _ _ ht' _ _ _ hf' ihc iht ihf =>
    intro hM he
    have hp := (ExprOK.iteView_iff hS hv).1 he
    obtain ⟨h1, hM1⟩ := hc' ▸ ihc hM hp.1
    obtain ⟨h2, hM2⟩ := ht' ▸ iht hM1 hp.2.1
    obtain ⟨h3, hM3⟩ := hf' ▸ ihf hM2 hp.2.2
    refine ⟨?_, hM3⟩
    split <;> first | exact h2 | exact (ExprOK.ite_iff hS).2 ⟨h1, h2, h3⟩
  case case7 _ _ _ _ _ _ _ _ _ _ hr =>
    intro hM he
    refine ⟨?_, hM⟩
    split <;> first | exact cand_ok hS hs hr | exact he
  case case8 | case10 | case13 => exact fun hM he => ⟨he, hM⟩
  case case9 _ _ _ _ _ _ _ _ _ _ _ _ hm =>
    exact fun hM _ => ⟨hM _ _ hm, hM⟩
  case case11 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hd _ _ _ hrw ha ih
    | case12 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hd _ _ _ hrw ha ih =>
    intro hM he
    simp only [wfParam] at hrw ih
    obtain ⟨h1, hM1⟩ := hrw ▸ ih hM (hs _ _ hd)
    first
    | exact ⟨h1, hins hM1 fun r h => by cases h; exact h1⟩
    | exact ⟨he, hins hM1 fun r h => by cases h⟩
  case case14 K M e hv hy =>
    intro hM he
    refine ⟨substFn_ok hS _ (fun h => ?_) he, hM⟩
    exact ⟨cand_ok hS hs (Option.filter_eq_some_iff.1 h).1, (Option.filter_eq_some_iff.1 h).2⟩

omit [LawfulBEq P.Ident] in
/-- **The exact rewrite passes the checks** when its input and the recorded right-hand sides
    do. -/
private theorem rwExact_ok (hS : GuardFwdSynLaws P) {dv df : P.Ident → Bool} {Γ : VarTyping P}
    {sc : Scope P} (hs : ScopeOK dv df Γ sc) (e : P.Expr) (he : ExprOK dv df Γ e) :
    ExprOK dv df Γ (rwExact sc e) := by
  let look : P.Ident → Option P.Expr := fun y => match sc[y]? with
    | some (some d) => if atomic d then some d else none
    | _ => none
  have hlook {k r} (h : look k = some r) : ExprOK dv df Γ r ∧ atomic r = true := by
    simp only [look] at h
    split at h <;> try cases h
    split at h <;> cases h
    exact ⟨hs _ _ ‹_›, ‹_›⟩
  have h' := substFn_ok hS look hlook he
  unfold rwExact
  dsimp only
  repeat' split
  all_goals first
    | exact h'
    | exact ⟨by simp [WPLang.getFvars_tt], by simp [VarTyping.annotates, hS.typed_tt],
        by simp [hS.ops_tt]⟩

omit [LawfulBEq P.Ident] [DecidableEq P.Ident] [HasBool P] [HasSubstFvar P] [WPLang P]
  [GuardOps P] in
/-- The checks of the recorded right-hand sides pass at a position with more defined names and a
    typing that agrees on the defined names. -/
theorem ScopeOK.mono [LawfulHasFvars P] {dv dv' df : P.Ident → Bool} {Γ Γ' : VarTyping P}
    {sc : Scope P} (hs : ScopeOK dv df Γ sc) (hd : ∀ z, dv z = true → dv' z = true)
    (hΓ : ∀ z, dv z = true → Γ' z = Γ z) : ScopeOK dv' df Γ' sc :=
  fun y d hy => (hs y d hy).mono hd hΓ

omit [LawfulBEq P.Ident] [HasBool P] [HasSubstFvar P] [WPLang P] [GuardOps P] in
/-- The checks of the recorded right-hand sides after an `init`: the defined names and the
    typing grow by the variable, which the position before does not define. -/
private theorem scopeOK_push [LawfulBEq P.Ident] [LawfulHasFvars P] {dv dv' df : P.Ident → Bool}
    {Γ : VarTyping P} {st : GSt P} (hs : ScopeOK dv df Γ st.scope) {x : P.Ident} {ty : P.Ty}
    {val : Option P.Expr} (hx : dv x = false) (hv : ∀ d, val = some d → ExprOK dv df Γ d)
    (hd : ∀ z, dv z = true → dv' z = true) :
    ScopeOK dv' df (Γ.extend [(x, ty)]) (st.push x val).scope := by
  have hΓ : ∀ z, dv z = true → Γ.extend [(x, ty)] z = Γ z := by grind [VarTyping.extend_singleton]
  intro y d hy
  simp only [GSt.push, Std.HashMap.getElem?_insert] at hy
  split at hy <;>
    first | exact (hs y d hy).mono hd hΓ | exact (hv d (Option.some.inj hy)).mono hd hΓ

omit [LawfulBEq P.Ident] in
/-- **The output passes the def-use and annotation checks** of the gate wherever the input does,
    when the recorded right-hand sides of the scope pass the checks. -/
theorem walk_gate [LawfulBEq P.Ident] [LawfulHasFvars P] (hS : GuardFwdSynLaws P) (cx : Ctx P)
    (df : P.Ident → Bool) (ss : PStmts P) (hp : Block.passiveForm ss = true) :
    ∀ (st : GSt P) (dv : P.Ident → Bool) (Γ : VarTyping P),
    Block.defUseWellFormed dv df ss = true → Block.fvarTypesWellAnnotated Γ ss →
    ScopeOK dv df Γ st.scope →
    Block.defUseWellFormed dv df (walk cx st ss).1 = true ∧
      Block.fvarTypesWellAnnotated Γ (walk cx st ss).1 := by
  induction ss using Block.passiveForm.induct <;> intro st dv Γ hd hf hs
  case' case2 _ _ e _ _ _ => rcases e with e | _
  all_goals simp only [walk, walkS, Block.defUseWellFormed, Stmt.defUseWellFormed,
    Block.fvarTypesWellAnnotated, Stmt.fvarTypesWellAnnotated, HasVarsImp.readVars,
    CmdExt.readVars, Cmd.getVars, ExprOrNondet.getVars, HasVarsImp.modifiedVars,
    CmdExt.modifiedVars, Cmd.modifiedVars, HasVarsImp.definedVars, CmdExt.definedVars,
    Cmd.definedVars, HasOpsImp.getOps, CmdExt.getOps, Cmd.getOps, ExprOrNondet.getOps,
    Stmt.definedVars, HasTypedVarsImp.typedReadVars, CmdExt.typedReadVars, Cmd.getTypedVars,
    ExprOrNondet.getTypedVars, Stmt.typedDefinedVars, HasTypedVarsImp.typedDefinedVars,
    CmdExt.typedDefinedVars, Cmd.typedDefinedVars, Bool.and_eq_true, List.all_eq_true,
    List.all_cons, List.all_nil, Bool.and_true, decide_eq_true_eq, ↓reduceIte,
    Block.passiveForm] at hp hd hf ⊢
  case case1 => exact ⟨trivial, trivial⟩
  case case2.det x _ _ _ ih =>
    obtain ⟨⟨⟨hfv, hx⟩, hops⟩, hrest⟩ := hd
    have he' := (rw_ok hS hs (initFuel cx st x) false false cx.cnt ∅ ∅ e
      (fun _ _ h => by simp at h) ⟨hfv, hf.1, hops⟩).1
    obtain ⟨h1, h2⟩ := ih hp _ _ _ hrest hf.2 (scopeOK_push hs (Bool.eq_false_iff.2 hx)
      (val := if recordable cx st.scope (rwRoot (initFuel cx st x) st.scope cx.cnt e) = true
        then some (rwRoot (initFuel cx st x) st.scope cx.cnt e) else none)
      (fun d hd => by split at hd <;> cases hd; exact he') fun z hz => by simp [hz])
    exact ⟨⟨⟨⟨he'.1, hx⟩, he'.2.2⟩, h1⟩, he'.2.1, h2⟩
  case case2.nondet ih =>
    obtain ⟨h1, h2⟩ := ih hp _ _ _ hd.2 hf.2
      (scopeOK_push hs (Bool.eq_false_iff.2 hd.1.2) (val := none) (fun _ h => by cases h)
        fun z hz => by simp [hz])
    exact ⟨⟨hd.1, h1⟩, hf.1, h2⟩
  case case3 _ e _ _ ih | case4 _ e _ _ ih | case5 _ e _ _ ih =>
    obtain ⟨⟨hfv, hops⟩, hrest⟩ := hd
    obtain ⟨h1, h2⟩ := ih hp st _ _ hrest hf.2 (hs.mono (fun z hz => by simp [hz]) fun _ _ => rfl)
    have hw := (rw_ok hS hs st.trailLen false false cx.cnt ∅ ∅ e (fun _ _ h => by simp at h)
      ⟨hfv, hf.1, hops⟩).1
    have hr := rwExact_ok hS hs e ⟨hfv, hf.1, hops⟩
    first | exact ⟨⟨⟨hw.1, hw.2.2⟩, h1⟩, hw.2.1, h2⟩ | exact ⟨⟨⟨hr.1, hr.2.2⟩, h1⟩, hr.2.1, h2⟩
  case case6 t e _ _ iht ihe ihr =>
    obtain ⟨⟨hpt, hpe⟩, hpr⟩ := hp
    obtain ⟨⟨⟨-, hdt⟩, hde⟩, hdr⟩ := hd
    obtain ⟨⟨-, hft, hfe⟩, hfr⟩ := hf
    obtain ⟨t1, k1, s1⟩ := (walk_frame cx st t).undo
    obtain ⟨-, -, s2⟩ := (GFrame.congr t1 k1 s1 (walk_frame cx _ e)).undo
    have hc {st' : GSt P} (h : ∀ x : P.Ident, st'.scope[x]? = st.scope[x]?) :
        ScopeOK dv df Γ st'.scope := fun y d hy => hs y d ((h y).symm.trans hy)
    obtain ⟨ht1, ht2⟩ := iht hpt st dv Γ hdt hft hs
    obtain ⟨he1, he2⟩ := ihe hpe _ dv Γ hde hfe (hc s1)
    obtain ⟨hr1, hr2⟩ := ihr hpr _ _ _ hdr hfr
      ((hc s2).mono (fun z hz => by simp [hz]) fun _ _ => rfl)
    exact ⟨⟨⟨⟨trivial, ht1⟩, he1⟩, hr1⟩, ⟨nofun, ht2, he2⟩, hr2⟩
  case case7 => simp_all

end Gate

end -- public section

end GuardFwd
end Imperative
