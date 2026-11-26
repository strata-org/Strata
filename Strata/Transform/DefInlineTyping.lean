/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.DefInlineProps
public import Strata.Transform.GuardFwdTyping
public import Strata.Transform.Passive.WellTyped
import all Strata.Transform.GuardFwdTyping

/-! # The inlining of single-use definitions keeps right-hand sides typed

The rewrite substitutes for a name only the recorded rewritten right-hand side of its `init`, which
has the declared type of the name, and the annotations of the input agree with the declared types.
So under the typing laws `TypedOpLaws`, for a substituting normalization that keeps the type of
the substituted expression (`SubstNormTyped`), the
rewrite keeps the type of an expression (`rwE_typed`), and the inlining keeps every `init` of a
list in passive form typed when the input's annotations agree with a typing
(`defInline_initsTyped`), and every `assume`, `assert` and `cover` condition of Boolean type
when the input's are (`defInline_condsTyped`).

Key definitions: `NormTyped`, `SubstNormTyped`.

Key theorems: `rwE_typed`, `defInline_initsTyped`, `defInline_condsTyped`,
`defInlineWith_condsTyped`. -/

namespace Imperative
namespace DefInline

open WP BigStep GuardFwd

public section

variable {P : PureExpr} [BEq P.Ident] [Hashable P.Ident] [LawfulBEq P.Ident] [HasFvar P]
  [HasFvars P] [DecidableEq P.Ident] [HasBool P] [HasSubstFvar P] [WPLang P]
  {Typ : P.Expr → P.Ty → Prop} {oe : WPOps.OpEnv P} {norm : SubstNorm P}

/-- The normalization `norm` keeps the type of every expression. -/
@[expose] def NormTyped (Typ : P.Expr → P.Ty → Prop) (norm : P.Expr → P.Expr) : Prop :=
  ∀ {e : P.Expr} {ty : P.Ty}, Typ e ty → Typ (norm e) ty

/-- The substituting normalization `norm` gives the type of every substituted expression. -/
@[expose] def SubstNormTyped (Typ : P.Expr → P.Ty → Prop) (norm : SubstNorm P) : Prop :=
  ∀ {g : P.Ident → Option P.Expr} {e : P.Expr} {ty : P.Ty}, Typ (WPOps.substFn e g) ty →
    Typ (norm g e) ty

omit [LawfulBEq P.Ident] in
/-- **The rewrite keeps the type** of an expression whose annotations agree with `Γ`, when the
    recorded right-hand sides have the types `Γ` gives their names and `norm` keeps the types of
    substituted expressions. -/
theorem rwE_typed (hL : TypedOpLaws Typ oe) (hN : SubstNormTyped Typ norm) {Γ : VarTyping P}
    {sc : Scope P} (hst : ScopeTyped Typ Γ sc) {e : P.Expr}
    (he : Γ.annotates (HasFvars.getTypedFvars e)) {ty : P.Ty} (hT : Typ e ty) :
    Typ (rwE norm sc e) ty :=
  hN (hL.substFn _ hT fun p hp v hv => by
    obtain ⟨T, hT', hvT⟩ := hst _ _ (look_some hv)
    exact Option.some.inj (hT'.symm.trans (he p.1 p.2 hp)) ▸ hvT)

/-- **The walk keeps `init`s typed** on a list in passive form whose annotations agree with `Γ`,
    when the recorded right-hand sides of the scope have the types `Γ` gives their names and
    `norm` keeps the types of substituted expressions. -/
private theorem walk_typed (hL : TypedOpLaws Typ oe) (hN : SubstNormTyped Typ norm) (cx : ICtx P)
    (ss : PStmts P) (hp : Block.passiveForm ss = true) :
    ∀ (st : GSt P) (Γ : VarTyping P), Block.fvarTypesWellAnnotated Γ ss →
    ScopeTyped Typ Γ st.scope → Block.initsTyped Typ ss →
    Block.initsTyped Typ (walk norm cx st ss).1 := by
  induction ss using Block.passiveForm.induct
  case' case2 x ty e md rest ih => rcases e with e | _
  case' case3 l e md rest ih | case4 l e md rest ih | case5 l e md rest ih => skip
  case' case6 t e md rest iht ihe ihr => skip
  all_goals intro st Γ hf hst hT
  case case1 => exact trivial
  case case7 => simp_all [Block.passiveForm]
  all_goals simp only [Block.passiveForm, Bool.and_eq_true] at hp
  all_goals simp only [walk, walkS, Block.fvarTypesWellAnnotated, Stmt.fvarTypesWellAnnotated,
    HasTypedVarsImp.typedReadVars, CmdExt.typedReadVars, Cmd.getTypedVars,
    ExprOrNondet.getTypedVars, Stmt.typedDefinedVars, HasTypedVarsImp.typedDefinedVars,
    CmdExt.typedDefinedVars, Cmd.typedDefinedVars, Block.initsTyped, Stmt.initsTyped,
    CmdExt.initsTyped] at hf hT ⊢
  case case2.det =>
    have ht' := rwE_typed hL hN hst hf.1 hT.1
    exact ⟨ht', ih hp _ _ hf.2 (scopeTyped_push hst fun d hd => (entry_some hd).1 ▸ ht') hT.2⟩
  case case2.nondet =>
    exact ⟨trivial, ih hp _ _ hf.2 (scopeTyped_push hst (val := none) nofun) hT.2⟩
  case case3 | case4 | case5 => exact ⟨trivial, ih hp st _ hf.2 hst hT.2⟩
  case case6 =>
    obtain ⟨⟨hpt, hpe⟩, hpr⟩ := hp
    obtain ⟨⟨-, hft, hfe⟩, hfr⟩ := hf
    obtain ⟨t1, k1, s1⟩ := (walk_frame norm cx st t).undo
    obtain ⟨-, -, s2⟩ := (GFrame.congr t1 k1 s1 (walk_frame norm cx _ e)).undo
    have hct {st' : GSt P} (h : ∀ x : P.Ident, st'.scope[x]? = st.scope[x]?) :
        ScopeTyped Typ Γ st'.scope := fun y d hy => hst y d ((h y).symm.trans hy)
    exact ⟨⟨iht hpt st Γ hft hst hT.1.1, ihe hpe _ Γ hfe (hct s1) hT.1.2⟩,
      ihr hpr _ _ hfr (hct s2) hT.2⟩

/-- **The inlining keeps `init`s typed.** Under the typing laws `TypedOpLaws`, for a substituting
    normalization `norm` that keeps the types of substituted expressions, on a list in passive
    form whose annotations agree with a typing `Γ`, every `init` of `defInline norm ss` has a
    right-hand side of its declared type when every `init` of `ss` has. -/
theorem defInline_initsTyped (hL : TypedOpLaws Typ oe) (hN : SubstNormTyped Typ norm)
    {ss : PStmts P}
    (hp : Block.passiveForm ss = true) {Γ : VarTyping P}
    (hf : Block.fvarTypesWellAnnotated Γ ss) (hT : Block.initsTyped Typ ss) :
    Block.initsTyped Typ (defInline norm ss) :=
  walk_typed hL hN _ ss hp {} Γ hf (fun _ _ h => by simp at h) hT

/-- **The inlining at a caller's choice of names keeps `init`s typed**: `defInline_initsTyped`
    for `defInlineWith norm sel`. -/
theorem defInlineWith_initsTyped (hL : TypedOpLaws Typ oe) (hN : SubstNormTyped Typ norm)
    {sel : Std.HashMap P.Ident Nat} {ss : PStmts P} (hp : Block.passiveForm ss = true)
    {Γ : VarTyping P} (hf : Block.fvarTypesWellAnnotated Γ ss) (hT : Block.initsTyped Typ ss) :
    Block.initsTyped Typ (defInlineWith norm sel ss) :=
  walk_typed hL hN _ ss hp {} Γ hf (fun _ _ h => by simp at h) hT


/-- **The walk keeps the conditions typed** on a list in passive form whose annotations agree with
    `Γ` and whose `init`s are typed, when the recorded right-hand sides of the scope have the
    types `Γ` gives their names and `norm` keeps the types of substituted expressions. -/
private theorem walk_condsTyped (hL : TypedOpLaws Typ oe) (hN : SubstNormTyped Typ norm)
    (cx : ICtx P) (ss : PStmts P) (hp : Block.passiveForm ss = true) :
    ∀ (st : GSt P) (Γ : VarTyping P), Block.fvarTypesWellAnnotated Γ ss →
    ScopeTyped Typ Γ st.scope → Block.initsTyped Typ ss → Block.condsTyped Typ ss →
    Block.condsTyped Typ (walk norm cx st ss).1 := by
  induction ss using Block.passiveForm.induct
  case' case2 x ty e md rest ih => rcases e with e | _
  case' case3 l e md rest ih | case4 l e md rest ih | case5 l e md rest ih => skip
  case' case6 t e md rest iht ihe ihr => skip
  all_goals intro st Γ hf hst hT hc
  case case1 => exact trivial
  case case7 => simp_all [Block.passiveForm]
  all_goals simp only [Block.passiveForm, Bool.and_eq_true] at hp
  all_goals simp only [walk, walkS, Block.fvarTypesWellAnnotated, Stmt.fvarTypesWellAnnotated,
    HasTypedVarsImp.typedReadVars, CmdExt.typedReadVars, Cmd.getTypedVars,
    ExprOrNondet.getTypedVars, Stmt.typedDefinedVars, HasTypedVarsImp.typedDefinedVars,
    CmdExt.typedDefinedVars, Cmd.typedDefinedVars, Block.initsTyped, Stmt.initsTyped,
    CmdExt.initsTyped, Block.condsTyped, Stmt.condsTyped, CmdExt.condsTyped] at hf hT hc ⊢
  case case2.det =>
    have ht' := rwE_typed hL hN hst hf.1 hT.1
    exact ⟨trivial,
      ih hp _ _ hf.2 (scopeTyped_push hst fun d hd => (entry_some hd).1 ▸ ht') hT.2 hc.2⟩
  case case2.nondet =>
    exact ⟨trivial, ih hp _ _ hf.2 (scopeTyped_push hst (val := none) nofun) hT.2 hc.2⟩
  case case3 | case4 | case5 =>
    exact ⟨rwE_typed hL hN hst hf.1 hc.1, ih hp st _ hf.2 hst hT.2 hc.2⟩
  case case6 =>
    obtain ⟨⟨hpt, hpe⟩, hpr⟩ := hp
    obtain ⟨⟨-, hft, hfe⟩, hfr⟩ := hf
    obtain ⟨t1, k1, s1⟩ := (walk_frame norm cx st t).undo
    obtain ⟨-, -, s2⟩ := (GFrame.congr t1 k1 s1 (walk_frame norm cx _ e)).undo
    have hct {st' : GSt P} (h : ∀ x : P.Ident, st'.scope[x]? = st.scope[x]?) :
        ScopeTyped Typ Γ st'.scope := fun y d hy => hst y d ((h y).symm.trans hy)
    exact ⟨⟨iht hpt st Γ hft hst hT.1.1 hc.1.1, ihe hpe _ Γ hfe (hct s1) hT.1.2 hc.1.2⟩,
      ihr hpr _ _ hfr (hct s2) hT.2 hc.2⟩

/-- **The inlining keeps the conditions typed.** Under the typing laws `TypedOpLaws`, for a
    substituting normalization `norm` that keeps the types of substituted expressions, on a list
    in passive form whose annotations agree with a typing `Γ` and whose `init`s are typed, every
    `assume`, `assert` and `cover` condition of `defInline norm ss` has the Boolean type when
    every such condition of `ss` has. -/
theorem defInline_condsTyped (hL : TypedOpLaws Typ oe) (hN : SubstNormTyped Typ norm)
    {ss : PStmts P} (hp : Block.passiveForm ss = true) {Γ : VarTyping P}
    (hf : Block.fvarTypesWellAnnotated Γ ss) (hT : Block.initsTyped Typ ss)
    (hc : Block.condsTyped Typ ss) : Block.condsTyped Typ (defInline norm ss) :=
  walk_condsTyped hL hN _ ss hp {} Γ hf (fun _ _ h => by simp at h) hT hc

/-- **The inlining at a caller's choice of names keeps the conditions typed**:
    `defInline_condsTyped` for `defInlineWith norm sel`. -/
theorem defInlineWith_condsTyped (hL : TypedOpLaws Typ oe) (hN : SubstNormTyped Typ norm)
    {sel : Std.HashMap P.Ident Nat} {ss : PStmts P} (hp : Block.passiveForm ss = true)
    {Γ : VarTyping P} (hf : Block.fvarTypesWellAnnotated Γ ss) (hT : Block.initsTyped Typ ss)
    (hc : Block.condsTyped Typ ss) : Block.condsTyped Typ (defInlineWith norm sel ss) :=
  walk_condsTyped hL hN _ ss hp {} Γ hf (fun _ _ h => by simp at h) hT hc

end -- public section

end DefInline
end Imperative
