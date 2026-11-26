/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.DefInline
public import Strata.Transform.GuardFwdProps

/-! # Properties of the inlining of single-use definitions

The walk only extends the undo log of guard forwarding, and undoing the extension gives back the
lookups of the scope it started from (`walk_frame`, with `GuardFwd.GFrame.undo`).

On a list in passive form the output has the shape of the input: it is in passive form, defines
the same names with the same types, and is in tree form when the input is (`walk_shape`).  Every
rewritten expression has its free variables, annotated occurrences and operators among those of
the input expression and of the recorded right-hand sides it reads (`rwE_ok`), so the output
passes the def-use and annotation checks of the initial-environment gate wherever the input does
(`walk_gate`).

Key theorems: `walk_frame`, `walk_shape`, `rwE_ok`, `walk_gate`.

Key definition: `DefInlineSynLaws`. -/

namespace Imperative
namespace DefInline

open WP BigStep GuardFwd

public section

variable {P : PureExpr} [BEq P.Ident] [Hashable P.Ident]

section Walk

variable [LawfulBEq P.Ident] [HasFvars P] [WPOps P]

omit [LawfulBEq P.Ident] [HasFvars P] [WPOps P] in
/-- The expression `look` substitutes for `y` is the right-hand side the scope records for it. -/
theorem look_some {sc : Scope P} {y : P.Ident} {d : P.Expr} (h : look sc y = some d) :
    sc[y]? = some (some d) := by
  simp only [look] at h
  split at h <;> cases h
  assumption

omit [LawfulBEq P.Ident] in
/-- An entry is the rewrite `e'`, recorded only when each free variable of `e` is in the scope or
    defined by no `init` of the list. -/
theorem entry_some {cx : ICtx P} {sc : Scope P} {x : P.Ident} {e e' d : P.Expr}
    (h : entry cx sc x e e' = some d) :
    d = e' ∧ ∀ z ∈ HasFvars.getFvars e, sc.contains z = true ∨ cx.ini.contains z = false := by
  simp only [entry] at h
  split at h <;> cases h
  rename_i hc
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true'] at hc
  exact ⟨rfl, hc.2⟩

mutual
/-- **The walk frames the state**: it only extends the undo log, by entries whose undoing gives
    back the lookups of the scope it started from. -/
theorem walk_frame (norm : SubstNorm P) (cx : ICtx P) :
    ∀ (st : GSt P) (ss : PStmts P), GFrame st (walk norm cx st ss).2
  | st, [] => GFrame.refl st
  | st, s :: rest => (walkS_frame norm cx st s).trans (walk_frame norm cx _ rest)
/-- The walk over a statement frames the state. -/
theorem walkS_frame (norm : SubstNorm P) (cx : ICtx P) :
    ∀ (st : GSt P) (s : PStmt P), GFrame st (walkS norm cx st s).2
  | st, .cmd (.cmd (.init x ty (.det e) md)) => GFrame.push _ _ _
  | st, .cmd (.cmd (.init x ty .nondet md)) => GFrame.push _ _ _
  | st, .cmd (.cmd (.set _ _ _)) | st, .cmd (.cmd (.assume _ _ _))
  | st, .cmd (.cmd (.assert _ _ _)) | st, .cmd (.cmd (.cover _ _ _)) | st, .cmd (.call _ _ _ _)
  | st, .loop _ _ _ _ _ | st, .exit _ _ | st, .typeDecl _ _ => GFrame.refl st
  | st, .ite c tss ess md => by
    obtain ⟨t1, k1, s1⟩ := (walk_frame norm cx st tss).undo
    obtain ⟨t2, k2, s2⟩ := (GFrame.congr t1 k1 s1 (walk_frame norm cx _ ess)).undo
    exact ⟨[], by simpa [walkS] using t2, by simpa [walkS] using k2,
      by simpa [walkS, undoGo] using s2⟩
  | st, .block l ss md => by
    obtain ⟨t1, k1, s1⟩ := (walk_frame norm cx st ss).undo
    exact ⟨[], by simpa [walkS] using t1, by simpa [walkS] using k1,
      by simpa [walkS, undoGo] using s1⟩
end

omit [LawfulBEq P.Ident] in
/-- The walk keeps an empty list empty and a nonempty one nonempty. -/
private theorem walk_isEmpty (norm : SubstNorm P) (cx : ICtx P) (st : GSt P) (ss : PStmts P) :
    (walk norm cx st ss).1.isEmpty = ss.isEmpty := by
  cases ss <;> rfl

omit [LawfulBEq P.Ident] in
/-- **The shape of the output.**  On a list in passive form, the output of the walk is in
    passive form, defines the same names with the same declared types, and is in tree form when
    the input is. -/
theorem walk_shape [HasFvar P] (norm : SubstNorm P) (cx : ICtx P) (ss : PStmts P)
    (hp : Block.passiveForm ss = true) :
    ∀ st : GSt P, Block.passiveForm (walk norm cx st ss).1 = true ∧
      (∀ b, Block.definedVars (walk norm cx st ss).1 b = Block.definedVars ss b) ∧
      Block.initTypes (walk norm cx st ss).1 = Block.initTypes ss ∧
      Block.treeForm (walk norm cx st ss).1 = Block.treeForm ss := by
  induction ss using Block.passiveForm.induct
  case' case2 _ _ e _ _ _ => cases e
  all_goals
    intro st
    simp_all [walk, walkS, Block.passiveForm, Block.treeForm, walk_isEmpty, Block.initTypes,
      Stmt.initTypes, HasVarsImp.definedVars, CmdExt.definedVars, Cmd.definedVars,
      HasInitTypesImp.initTypes, CmdExt.initTypes, Cmd.initTypes]

end Walk

section Gate

variable [LawfulBEq P.Ident] [HasFvar P] [HasFvars P] [DecidableEq P.Ident] [HasBool P]
  [HasSubstFvar P] [WPLang P] [HasOps P] [GuardOps P]

/-- The laws of the syntax of expressions that the gate of the output needs: an operator of a
    substitution is one of the expression or of an image, and the substituting normalization
    `norm` adds no free variable, annotated occurrence or operator to the substituted
    expression. -/
structure DefInlineSynLaws (P : PureExpr) [DecidableEq P.Ident] [HasBool P] [HasFvar P]
    [HasFvars P] [HasSubstFvar P] [WPLang P] [HasOps P] (norm : SubstNorm P) : Prop where
  ops_substFn : ∀ (e : P.Expr) (g : P.Ident → Option P.Expr) o,
    o ∈ HasOps.getOps (WPOps.substFn e g) →
      o ∈ HasOps.getOps e ∨ ∃ x r, g x = some r ∧ o ∈ HasOps.getOps r
  norm_fvars : ∀ g e y, y ∈ HasFvars.getFvars (norm g e) →
    y ∈ HasFvars.getFvars (WPOps.substFn e g)
  norm_typed : ∀ g e p, p ∈ HasFvars.getTypedFvars (norm g e) →
    p ∈ HasFvars.getTypedFvars (WPOps.substFn e g)
  norm_ops : ∀ g e o, o ∈ HasOps.getOps (norm g e) → o ∈ HasOps.getOps (WPOps.substFn e g)

variable {norm : SubstNorm P}

omit [LawfulBEq P.Ident] [GuardOps P] in
/-- **The rewrite passes the checks** when its input and the recorded right-hand sides do. -/
theorem rwE_ok (hS : DefInlineSynLaws P norm) {dv df : P.Ident → Bool} {Γ : VarTyping P}
    {sc : Scope P} (hs : ScopeOK dv df Γ sc) (e : P.Expr) (he : ExprOK dv df Γ e) :
    ExprOK dv df Γ (rwE norm sc e) := by
  have hlook {k r} (h : look sc k = some r) : ExprOK dv df Γ r := hs _ _ (look_some h)
  let sm := (HasFvars.getFvars e).filterMap fun y => (look sc y).map (y, ·)
  have hfind : ∀ x ∈ HasFvars.getFvars e, look sc x = Map.find? sm x :=
    fun x hx => (find?_filterMap (look sc) _ x (.inl hx)).symm
  refine ⟨fun z hz => ?_, fun x ty hx => ?_, fun o ho => ?_⟩
  · replace hz := hS.norm_fvars _ _ z hz
    rw [WPLang.substFn_eq e (look sc) sm hfind] at hz
    rcases WPLang.getFvars_substFvars e sm z hz with ⟨hz, -⟩ | ⟨x, v, hx, hv, hz⟩
    · exact he.1 z hz
    · exact (hlook ((hfind x hx).trans hv)).1 z hz
  · rcases WPLang.getTypedFvars_substFn e (look sc) (x, ty) (hS.norm_typed _ _ _ hx) with
      ⟨hx, -⟩ | ⟨z, v, -, hv, hx⟩
    · exact he.2.1 x ty hx
    · exact (hlook hv).2.1 x ty hx
  · rcases hS.ops_substFn e (look sc) o (hS.norm_ops _ _ o ho) with ho | ⟨x, r, hr, ho⟩
    · exact he.2.2 o ho
    · exact (hlook hr).2.2 o ho

omit [LawfulBEq P.Ident] [HasBool P] [HasSubstFvar P] [WPLang P] [GuardOps P] in
/-- The checks of the recorded right-hand sides after an `init`: the defined names and the
    typing grow by the variable, which the position before does not define. -/
private theorem scopeOK_push [LawfulBEq P.Ident] [LawfulHasFvars P] {dv dv' df : P.Ident → Bool}
    {Γ : VarTyping P} {st : GSt P} (hs : ScopeOK dv df Γ st.scope) {x : P.Ident} {ty : P.Ty}
    {val : Option P.Expr} (hx : dv x = false) (hv : ∀ d, val = some d → ExprOK dv df Γ d)
    (hd : ∀ z, dv z = true → dv' z = true) :
    ScopeOK dv' df (Γ.extend [(x, ty)]) (st.push x val).scope := by
  have hΓ : ∀ z, dv z = true → Γ.extend [(x, ty)] z = Γ z := fun z hz => by
    have hxz : z ≠ x := by
      rintro rfl
      simp_all
    simp [VarTyping.extend_singleton, hxz]
  intro y d hy
  simp only [GSt.push, Std.HashMap.getElem?_insert] at hy
  split at hy
  · cases hy
    exact (hv d rfl).mono hd hΓ
  · exact (hs y d hy).mono hd hΓ

omit [LawfulBEq P.Ident] [GuardOps P] in
/-- **The output passes the def-use and annotation checks** of the gate wherever the input does,
    when the recorded right-hand sides of the scope pass the checks. -/
theorem walk_gate [LawfulBEq P.Ident] [LawfulHasFvars P] (hS : DefInlineSynLaws P norm)
    (cx : ICtx P) (df : P.Ident → Bool) (ss : PStmts P) (hp : Block.passiveForm ss = true) :
    ∀ (st : GSt P) (dv : P.Ident → Bool) (Γ : VarTyping P),
    Block.defUseWellFormed dv df ss = true → Block.fvarTypesWellAnnotated Γ ss →
    ScopeOK dv df Γ st.scope →
    Block.defUseWellFormed dv df (walk norm cx st ss).1 = true ∧
      Block.fvarTypesWellAnnotated Γ (walk norm cx st ss).1 := by
  induction ss using Block.passiveForm.induct
  case' case2 x ty e md rest ih => rcases e with e | _
  case' case3 l e md rest ih | case4 l e md rest ih | case5 l e md rest ih => skip
  all_goals intro st dv Γ hd hf hs
  case case1 => exact ⟨rfl, trivial⟩
  case case7 => simp_all [Block.passiveForm]
  case' case6 t e md rest iht ihe ihr => skip
  case' case2.det | case2.nondet | case3 | case4 | case5 | case6 =>
    simp only [Block.passiveForm, Bool.and_eq_true] at hp
    simp only [walk, walkS, Block.defUseWellFormed, Stmt.defUseWellFormed,
      Block.fvarTypesWellAnnotated, Stmt.fvarTypesWellAnnotated, HasVarsImp.readVars,
      CmdExt.readVars, Cmd.getVars, ExprOrNondet.getVars, HasVarsImp.modifiedVars,
      CmdExt.modifiedVars, Cmd.modifiedVars, HasVarsImp.definedVars, CmdExt.definedVars,
      Cmd.definedVars, HasOpsImp.getOps, CmdExt.getOps, Cmd.getOps,
      Stmt.definedVars, HasTypedVarsImp.typedReadVars, CmdExt.typedReadVars, Cmd.getTypedVars,
      ExprOrNondet.getTypedVars, Stmt.typedDefinedVars, HasTypedVarsImp.typedDefinedVars,
      CmdExt.typedDefinedVars, Cmd.typedDefinedVars, Bool.and_eq_true, List.all_eq_true,
      List.all_cons, List.all_nil, Bool.and_true, decide_eq_true_eq, ExprOrNondet.getOps,
      ↓reduceIte] at hd hf ⊢
  case case2.det =>
    obtain ⟨⟨⟨hfv, hx⟩, hops⟩, hrest⟩ := hd
    have he' := rwE_ok hS hs e ⟨hfv, hf.1, hops⟩
    obtain ⟨h1, h2⟩ := ih hp _ _ _ hrest hf.2 (scopeOK_push hs (Bool.eq_false_iff.2 hx)
      (val := entry cx st.scope x e (rwE norm st.scope e))
      (fun d hd => (entry_some hd).1 ▸ he') fun z hz => by simp [hz])
    exact ⟨⟨⟨⟨he'.1, hx⟩, he'.2.2⟩, h1⟩, he'.2.1, h2⟩
  case case2.nondet =>
    obtain ⟨h1, h2⟩ := ih hp _ _ _ hd.2 hf.2
      (scopeOK_push hs (Bool.eq_false_iff.2 hd.1.2) (val := none) (fun _ h => by cases h)
        fun z hz => by simp [hz])
    exact ⟨⟨hd.1, h1⟩, hf.1, h2⟩
  case case3 | case4 | case5 =>
    obtain ⟨⟨hfv, hops⟩, hrest⟩ := hd
    obtain ⟨h1, h2⟩ := ih hp st _ _ hrest hf.2 (hs.mono (fun z hz => by simp [hz]) fun _ _ => rfl)
    have he' := rwE_ok hS hs e ⟨hfv, hf.1, hops⟩
    exact ⟨⟨⟨he'.1, he'.2.2⟩, h1⟩, he'.2.1, h2⟩
  case case6 =>
    obtain ⟨⟨hpt, hpe⟩, hpr⟩ := hp
    obtain ⟨⟨⟨-, hdt⟩, hde⟩, hdr⟩ := hd
    obtain ⟨⟨-, hft, hfe⟩, hfr⟩ := hf
    obtain ⟨t1, k1, s1⟩ := (walk_frame norm cx st t).undo
    obtain ⟨-, -, s2⟩ := (GFrame.congr t1 k1 s1 (walk_frame norm cx _ e)).undo
    have hc {st' : GSt P} (h : ∀ x : P.Ident, st'.scope[x]? = st.scope[x]?) :
        ScopeOK dv df Γ st'.scope := fun y d hy => hs y d ((h y).symm.trans hy)
    obtain ⟨ht1, ht2⟩ := iht hpt st dv Γ hdt hft hs
    obtain ⟨he1, he2⟩ := ihe hpe _ dv Γ hde hfe (hc s1)
    obtain ⟨hr1, hr2⟩ := ihr hpr _ _ _ hdr hfr
      ((hc s2).mono (fun z hz => by simp [hz]) fun _ _ => rfl)
    exact ⟨⟨⟨⟨trivial, ht1⟩, he1⟩, hr1⟩, ⟨nofun, ht2, he2⟩, hr2⟩

end Gate

end -- public section

end DefInline
end Imperative
