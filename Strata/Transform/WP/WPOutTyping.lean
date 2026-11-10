/-
  Copyright Strata Contributors

  SPDX-License-Identifier: Apache-2.0 OR MIT
-/
module

public import Strata.Transform.WP.WPOutTypes
public import Strata.Transform.Passive.WellTyped
import Strata.Transform.Passive.SimulationProps
import Strata.DL.Imperative.StmtProps
import Strata.Transform.WP.WPOverEmit
import Strata.Transform.WP.WPOverEval
import Strata.Transform.WP.WPReads
import Strata.Util.ExceptProps

/-! # Statement lists and guarded items typed against the final types

A statement list whose every command is typed against one typing `Θ` of all the names it uses
(`Block.TyOK`): every `init` declares a ground type that `Θ` gives its variable when it gives one,
every `set` assigns a variable to which `Θ` gives a ground type, every right-hand side and
condition has the type of its variable or the Boolean type, every annotated free-variable
occurrence carries the type `Θ` gives its variable, and every `ite` is nondeterministic.  Such a
list is well typed under every typing `Γ` of its free variables agreeing with `Θ`
(`Block.wellTyped_of_tyOK`).

On the items of the WP walk, the typing is stated against the final type maps `T`, `Y` that
resolve the items, `Θ` being the final declared type of each name (`tyOpt`): every resolution of
a guarded expression is typed (`WOK`), straight-line items are typed (`PlainOK`), and a list of
items is typed when its straight-line items followed by a branching item, its runs of
obligations and the arms of its real branches are (`LOK`; the emission drops the other
straight-line items).  Resolution, merging of obligation runs and nesting keep the typing
(`resolveItems_IOK`, `mergeObls_IOK`, `nest_TyOK`).

Key definitions: `TypingLaws`, `AnnOK`, `ExprOK`, `CmdOK`, `Block.TyOK`, `tyOpt`, `WOK`,
`PlainOK`, `LOK`, `IOK`.

Key theorems: `Block.wellTyped_of_tyOK`, `resolveItems_IOK`, `mergeObls_IOK`, `nest_TyOK`,
`WOK.user`. -/

namespace Imperative
namespace WP

open BigStep

public section

variable {P : PureExpr} [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident] [HasBool P]
  [HasFvar P] [HasFvars P] [Hashable P.Ident] [LawfulHasFvars P]

section
variable [WPOps P]

/-- **The laws of a typing predicate and a ground-type predicate** the typing of the output of
    the WP phase needs: the laws of the conditional, the substitution and the annotated variables
    (`TypedLaws`), the Boolean literals have the Boolean type, a typed expression has a ground
    type, and a variable annotated with a ground type has that type. -/
structure TypingLaws (Typ : P.Expr → P.Ty → Prop) (Ground : P.Ty → Prop) : Prop
    extends TypedLaws Typ where
  /-- The literal `true` is Boolean. -/
  tt : Typ tt HasBool.boolTy
  /-- The literal `false` is Boolean. -/
  ff : Typ ff HasBool.boolTy
  /-- A typed expression has a ground type. -/
  ground : ∀ {e : P.Expr} {ty : P.Ty}, Typ e ty → Ground ty
  /-- A variable annotated with a ground type has that type. -/
  mkVar : ∀ (x : P.Ident) {ty : P.Ty}, Ground ty → Typ (HasFvar.mkVar x (some ty)) ty

/-- Every annotated free-variable occurrence of `e` carries the type `Θ` gives its variable. -/
@[expose] def AnnOK (Θ : VarTyping P) (e : P.Expr) : Prop :=
  ∀ p ∈ HasFvars.getTypedFvars e, Θ p.1 = some p.2

/-- `e` has the type `ty` under `Typ`, its annotations agreeing with `Θ`. -/
@[expose] def ExprOK (Typ : P.Expr → P.Ty → Prop) (Θ : VarTyping P) (e : P.Expr) (ty : P.Ty) :
    Prop :=
  Typ e ty ∧ AnnOK Θ e

/-- A command typed against `Θ`: an `init` declares a ground type that `Θ` gives its variable
    when it gives one, a `set` assigns a variable to which `Θ` gives a ground type, the
    right-hand sides have the type of their variable and the conditions the Boolean type, with
    annotations agreeing with `Θ`; there is no call. -/
@[expose] def CmdOK (Typ : P.Expr → P.Ty → Prop) (Ground : P.Ty → Prop) (Θ : VarTyping P) :
    CmdExt P → Prop
  | .cmd (.init x ty e _) => (∀ τ, Θ x = some τ → τ = ty) ∧ Ground ty ∧
    ∀ v, e = .det v → ExprOK Typ Θ v ty
  | .cmd (.set x e _) => ∃ τ, Θ x = some τ ∧ Ground τ ∧ ∀ v, e = .det v → ExprOK Typ Θ v τ
  | .cmd (.assume _ e _) | .cmd (.assert _ e _) | .cmd (.cover _ e _) =>
    ExprOK Typ Θ e HasBool.boolTy
  | .call _ _ _ => False

mutual
/-- A statement typed against `Θ`: a command typed against `Θ` (`CmdOK`), a block of such
    statements, or a nondeterministic `ite` of such statements. -/
@[expose] def Stmt.TyOK (Typ : P.Expr → P.Ty → Prop) (Ground : P.Ty → Prop) (Θ : VarTyping P) :
    Stmt P (CmdExt P) → Prop
  | .cmd c => CmdOK Typ Ground Θ c
  | .block _ b _ => Block.TyOK Typ Ground Θ b
  | .ite .nondet t e _ => Block.TyOK Typ Ground Θ t ∧ Block.TyOK Typ Ground Θ e
  | _ => False

/-- Every statement of the list typed against `Θ` (`Stmt.TyOK`). -/
@[expose] def Block.TyOK (Typ : P.Expr → P.Ty → Prop) (Ground : P.Ty → Prop) (Θ : VarTyping P) :
    List (Stmt P (CmdExt P)) → Prop
  | [] => True
  | s :: rest => Stmt.TyOK Typ Ground Θ s ∧ Block.TyOK Typ Ground Θ rest
end

variable {Typ : P.Expr → P.Ty → Prop} {Ground : P.Ty → Prop} {Θ : VarTyping P}

omit [DecidableEq P.Ident] [HasBool P] [WPOps P] in
/-- The annotations of an expression whose annotations agree with `Θ` agree with every typing that
    agrees with `Θ` on its free variables. -/
theorem AnnOK.annotates {Γ : VarTyping P} {e : P.Expr} (h : AnnOK Θ e)
    (hΓ : ∀ x ∈ exprFV e, ∀ τ, Θ x = some τ → Γ x = some τ) :
    Γ.annotates (HasFvars.getTypedFvars e) := fun x τ hx =>
  hΓ x (mem_exprFV.2 (LawfulHasFvars.mem_getFvars_of_typed e x τ hx)) τ (h (x, τ) hx)

omit [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident] [HasBool P] [HasFvar P] [HasFvars P]
  [Hashable P.Ident] [WPOps P] [LawfulHasFvars P] in
/-- Extending a typing with no definition leaves it unchanged. -/
theorem VarTyping.extend_nil (Γ : VarTyping P) : Γ.extend [] = Γ := rfl

section
omit [DecidableEq P.Ident] [HasBool P] [HasFvar P] [WPOps P] [LawfulHasFvars P]

/-- The target of a `set` is one of its free variables. -/
private theorem fv_set_tgt {x : P.Ident} {e : ExprOrNondet P} {md : MetaData P} :
    x ∈ Stmt.freeVars (.cmd (.cmd (.set x e md)) : Stmt P (CmdExt P)) := by
  cases e <;> simp [Stmt.freeVars]

/-- A free variable of the right-hand side of a `set` is one of its free variables. -/
private theorem fv_set_rhs {x y : P.Ident} {v : P.Expr} {md : MetaData P} (h : y ∈ exprFV v) :
    y ∈ Stmt.freeVars (.cmd (.cmd (.set x (.det v) md)) : Stmt P (CmdExt P)) := by
  simp [Stmt.freeVars, h]

/-- A free variable of an arm of a nondeterministic `ite` is one of its free variables. -/
private theorem fv_ite_arm {x : P.Ident} {t e : List (Stmt P (CmdExt P))} {md : MetaData P}
    (h : x ∈ Block.freeVars t ∨ x ∈ Block.freeVars e) :
    x ∈ Stmt.freeVars (.ite .nondet t e md) := by
  simp only [Stmt.freeVars, List.nil_append, List.mem_append]
  exact h

/-- A free variable of the rest of a list after a statement declaring nothing at its top level,
    or after an `init` of another name, is one of the list. -/
private theorem fv_rest {s : Stmt P (CmdExt P)} {rest : List (Stmt P (CmdExt P))} {x : P.Ident}
    (hx : x ∈ Block.freeVars rest) (hs : ∀ y ty e md, s = .cmd (.cmd (.init y ty e md)) → x ≠ y) :
    x ∈ Block.freeVars (s :: rest) := by
  unfold Block.freeVars
  split
  · rename_i y _ e _
    exact List.mem_append_right _ (List.mem_filter.2 ⟨hx, by simpa using hs _ _ _ _ rfl⟩)
  · exact List.mem_append_right _ hx
end

omit [HasBool P] [WPOps P] [LawfulHasFvars P] in
omit [BEq P.Ident] [LawfulBEq P.Ident] [Hashable P.Ident] in
/-- The typing after a statement: extended with its declared variable, when it declares one. -/
private theorem extend_stmt {Γ : VarTyping P} {s : Stmt P (CmdExt P)} {x : P.Ident} :
    Γ.extend (Stmt.typedDefinedVars s) x =
      match s with
      | .cmd (.cmd (.init y ty _ _)) => if y = x then some ty else Γ x
      | _ => Γ x := by
  rcases s with ((⟨y, ty, e, md⟩ | _ | _ | _ | _) | _) | _ | _ | _ | _ | _
  · by_cases h : y = x <;> simp [Stmt.typedDefinedVars, HasTypedVarsImp.typedDefinedVars,
      CmdExt.typedDefinedVars, Cmd.typedDefinedVars, VarTyping.extend, h]
  all_goals rfl

omit [LawfulHasFvars P] [WPOps P] in
/-- The free-variable typing condition after a statement typed against `Θ`: a typing agreeing with
    `Θ` on the free variables of `s :: rest`, extended with the declaration of `s`, agrees with
    `Θ` on the free variables of `rest`. -/
private theorem agree_rest {Γ : VarTyping P} {s : Stmt P (CmdExt P)}
    {rest : List (Stmt P (CmdExt P))} (hs : Stmt.TyOK Typ Ground Θ s)
    (hΓ : ∀ x ∈ Block.freeVars (s :: rest), ∀ τ, Θ x = some τ → Γ x = some τ) :
    ∀ x ∈ Block.freeVars rest, ∀ τ, Θ x = some τ →
      Γ.extend (Stmt.typedDefinedVars s) x = some τ := by
  intro x hx τ hτ
  rw [extend_stmt]
  split
  · rename_i y ty _ _
    split
    · rename_i hyx
      subst hyx
      exact congrArg some (hs.1 τ hτ).symm
    · rename_i hyx
      exact hΓ x (fv_rest hx fun _ _ _ _ he => by cases he; exact Ne.symm hyx) τ hτ
  · rename_i hni
    exact hΓ x (fv_rest hx fun y ty e md he => absurd he (hni y ty e md)) τ hτ

omit [DecidableEq P.Ident] [LawfulHasFvars P] in
mutual
/-- **A statement typed against `Θ` is well typed** under every typing `Γ` agreeing with `Θ` on
    its free variables: its right-hand sides and conditions are typed, its annotations agree with
    `Γ`, and every variable it assigns has a ground type. -/
theorem Stmt.wellTyped_of_tyOK [LawfulHasFvars P] (hL : TypingLaws Typ Ground) :
    ∀ (s : Stmt P (CmdExt P)) (Γ : VarTyping P), Stmt.TyOK Typ Ground Θ s →
      (∀ x ∈ Stmt.freeVars s, ∀ τ, Θ x = some τ → Γ x = some τ) →
      Stmt.rhsTyped Typ Γ s ∧ Stmt.condsTyped Typ s ∧ Stmt.fvarTypesWellAnnotated Γ s ∧
        Stmt.nondetGround Ground (fun _ => True) Γ s
  | .cmd (.cmd (.init _ _ (.det v) _)), _, h, hΓ =>
    ⟨(h.2.2 v rfl).1, trivial, (h.2.2 v rfl).2.annotates hΓ, fun _ => trivial, fun _ => h.2.1⟩
  | .cmd (.cmd (.init _ _ .nondet _)), _, h, _ =>
    ⟨trivial, trivial, fun _ _ h => (nomatch h), fun _ => trivial, fun _ => h.2.1⟩
  | .cmd (.cmd (.set x (.det v) _)), _, ⟨τ, hτ, hg, he⟩, hΓ =>
    ⟨⟨τ, hΓ x fv_set_tgt τ hτ, (he v rfl).1⟩, trivial,
      (he v rfl).2.annotates fun y hy => hΓ y (fv_set_rhs hy), fun _ => trivial,
      fun _ => ⟨τ, hΓ x fv_set_tgt τ hτ, hg⟩⟩
  | .cmd (.cmd (.set x .nondet _)), _, ⟨τ, hτ, hg, _⟩, hΓ =>
    ⟨trivial, trivial, fun _ _ h => (nomatch h), fun _ => trivial,
      fun _ => ⟨τ, hΓ x fv_set_tgt τ hτ, hg⟩⟩
  | .cmd (.cmd (.assume _ _ _)), _, h, hΓ | .cmd (.cmd (.assert _ _ _)), _, h, hΓ
  | .cmd (.cmd (.cover _ _ _)), _, h, hΓ => ⟨trivial, h.1, h.2.annotates hΓ, trivial⟩
  | .cmd (.call _ _ _), _, h, _ => h.elim
  | .block _ b _, Γ, h, hΓ =>
    (Block.wellTyped_of_tyOK hL b Γ h hΓ).elim fun ⟨h1, h2, h3⟩ h4 => ⟨h1, h2, h3, h4⟩
  | .ite .nondet t e _, Γ, ⟨ht, he⟩, hΓ =>
    (Block.wellTyped_of_tyOK hL t Γ ht fun x hx => hΓ x (fv_ite_arm (.inl hx))).elim
      fun ⟨t1, t2, t3⟩ t4 =>
    (Block.wellTyped_of_tyOK hL e Γ he fun x hx => hΓ x (fv_ite_arm (.inr hx))).elim
      fun ⟨e1, e2, e3⟩ e4 =>
    ⟨⟨trivial, t1, e1⟩, ⟨t2, e2⟩, ⟨fun _ _ h => (nomatch h), t3, e3⟩, t4, e4⟩
  | .ite (.det _) _ _ _, _, h, _ | .loop _ _ _ _ _, _, h, _ | .exit _ _, _, h, _
  | .typeDecl _ _, _, h, _ => h.elim

/-- **A statement list typed against `Θ` is well typed** under every typing `Γ` agreeing with `Θ`
    on its free variables: its expressions are typed (`Block.ExprsTyped`) and every variable it
    assigns has a ground type. -/
theorem Block.wellTyped_of_tyOK [LawfulHasFvars P] (hL : TypingLaws Typ Ground) :
    ∀ (ss : List (Stmt P (CmdExt P))) (Γ : VarTyping P), Block.TyOK Typ Ground Θ ss →
      (∀ x ∈ Block.freeVars ss, ∀ τ, Θ x = some τ → Γ x = some τ) →
      Block.ExprsTyped Typ Γ ss ∧ Block.nondetGround Ground (fun _ => True) Γ ss
  | [], _, _, _ => ⟨⟨trivial, trivial, trivial⟩, trivial⟩
  | s :: rest, Γ, ⟨hs, hr⟩, hΓ =>
    (Stmt.wellTyped_of_tyOK hL s Γ hs fun x hx => hΓ x (Block.freeVars_cons_sub x hx)).elim
      fun s1 ⟨s2, s3, s4⟩ =>
    (Block.wellTyped_of_tyOK hL rest _ hr (agree_rest hs hΓ)).elim fun ⟨r1, r2, r3⟩ r4 =>
    ⟨⟨⟨s1, r1⟩, ⟨s2, r2⟩, ⟨s3, r3⟩⟩, s4, r4⟩
end

end

/-! ## Items typed against the final types -/

section
variable [HasSubstFvar P] [HasIdent P] [iW : WPLang P]
variable {T : Std.HashMap P.Ident P.Ty} {Y : Std.HashMap P.Ident P.Ident}

/-- The final declared type of a name (`tyOfName`), as an optional type. -/
@[expose] def tyOpt (T : Std.HashMap P.Ident P.Ty) (Y : Std.HashMap P.Ident P.Ident) :
    VarTyping P :=
  fun x => match tyOfName T Y x with
    | .ok ty => some ty
    | .error _ => none

omit [LawfulBEq P.Ident] [LawfulHasFvars P] [HasIdent P] in
/-- The optional final type of a name is its final declared type. -/
theorem tyOpt_eq {x : P.Ident} {ty : P.Ty} : tyOpt T Y x = some ty ↔ tyOfName T Y x = .ok ty := by
  unfold tyOpt
  split <;> simp_all

/-- Every resolution of the guarded expression `w` (under the final maps `T`, `Y`) has the type
    `ty`, its annotations agreeing with the final declared types. -/
@[expose] def WOK (Typ : P.Expr → P.Ty → Prop) (T : Std.HashMap P.Ident P.Ty)
    (Y : Std.HashMap P.Ident P.Ident) (w : WExpr P) (ty : P.Ty) : Prop :=
  ∀ e, resolveE T Y w = .ok e → ExprOK Typ (tyOpt T Y) e ty

/-- The variables of the reach context `κ` have the Boolean final type. -/
@[expose] def REOK (T : Std.HashMap P.Ident P.Ty) (Y : Std.HashMap P.Ident P.Ident) (κ : RE P) :
    Prop :=
  ∀ y ∈ RE.vars κ, tyOfName T Y y = .ok HasBool.boolTy

/-- A straight-line item typed against the final types: an `init` declares, for every
    resolution of its type reference, a ground type that is the final type of its variable when
    it has one, with a value of that type; a `set` assigns a variable with a ground final type a
    value of that type; an `assume` has a Boolean condition. -/
@[expose] def PlainOK (Typ : P.Expr → P.Ty → Prop) (Ground : P.Ty → Prop)
    (T : Std.HashMap P.Ident P.Ty) (Y : Std.HashMap P.Ident P.Ident) : WItem P → Prop
  | .init x tr e => ∀ ty, RefTy T Y ty tr → (∀ τ, tyOfName T Y x = .ok τ → τ = ty) ∧ Ground ty ∧
    ∀ w, e = some w → WOK Typ T Y w ty
  | .set x e => ∃ τ, tyOfName T Y x = .ok τ ∧ Ground τ ∧ ∀ w, e = some w → WOK Typ T Y w τ
  | .assume _ e _ => WOK Typ T Y e HasBool.boolTy
  | _ => True

/-- The items of a list typed against the final types, `b` telling whether a branching item
    follows the list: a straight-line item when a branching item follows it (the emission drops
    the others), a run of obligations under a Boolean reach context with Boolean conditions, and
    the arms of a real branch (which ends the list). -/
@[expose] def LOK (Typ : P.Expr → P.Ty → Prop) (Ground : P.Ty → Prop)
    (T : Std.HashMap P.Ident P.Ty) (Y : Std.HashMap P.Ident P.Ident) (b : Bool) :
    List (WItem P) → Prop
  | [] => True
  | .obls r cs :: rest => (∀ κ, r = some κ → REOK T Y κ) ∧
    (∀ c ∈ cs, WOK Typ T Y c.2.2.1 HasBool.boolTy) ∧ LOK Typ Ground T Y b rest
  | .branch t e :: _ => LOK Typ Ground T Y false t ∧ LOK Typ Ground T Y false e
  | it :: rest => ((b || rest.any WItem.isBranching) = true → PlainOK Typ Ground T Y it) ∧
    LOK Typ Ground T Y b rest
  termination_by l => sizeOf l

/-- The flat items of a list typed against `Θ`, `b` telling whether a branching item follows the
    list: a straight-line statement when a branching item follows it, the statements of a run of
    obligations under a reach context whose variables `Θ` types Boolean, and the arms of a real
    branch (which ends the list). -/
@[expose] def IOK (Typ : P.Expr → P.Ty → Prop) (Ground : P.Ty → Prop) (Θ : VarTyping P)
    (b : Bool) : List (Item P) → Prop
  | [] => True
  | .plain s :: rest => ((b || rest.any Item.isBranching) = true → Stmt.TyOK Typ Ground Θ s) ∧
    IOK Typ Ground Θ b rest
  | .obls r cs :: rest => (∀ κ, r = some κ → ∀ y ∈ RE.vars κ, Θ y = some HasBool.boolTy) ∧
    Block.TyOK Typ Ground Θ cs ∧ IOK Typ Ground Θ b rest
  | .branch t e :: _ => IOK Typ Ground Θ false t ∧ IOK Typ Ground Θ false e
  termination_by l => sizeOf l

end

section
variable [HasSubstFvar P] [HasIdent P] [iW : WPLang P]
variable {T : Std.HashMap P.Ident P.Ty} {Y : Std.HashMap P.Ident P.Ident}
  {Typ : P.Expr → P.Ty → Prop} {Ground : P.Ty → Prop}

omit [LawfulBEq P.Ident] [LawfulHasFvars P] [HasIdent P] in
/-- The resolution of an optional guarded expression all of whose resolutions have the type `ty`
    is nondeterministic or a deterministic expression of type `ty`. -/
private theorem resolveOE_ok {e : Option (WExpr P)} {e' : ExprOrNondet P} {ty : P.Ty}
    (h : resolveOE T Y e = .ok e') (he : ∀ w, e = some w → WOK Typ T Y w ty) :
    ∀ v, e' = .det v → ExprOK Typ (tyOpt T Y) v ty := by
  intro v hv
  cases e with
  | none => cases h; cases hv
  | some w =>
    simp only [resolveOE, Except.bind_is_ok, Except.pure_is_ok] at h
    obtain ⟨v', hv', rfl⟩ := h
    cases hv
    exact he w rfl v hv'

omit [LawfulBEq P.Ident] [LawfulHasFvars P] [HasIdent P] in
/-- The resolution of a straight-line item typed against the final types is a statement typed
    against them. -/
private theorem resolveItem_plain {it : WItem P} {i : Item P} (hb : it.isBranching = false)
    (h : resolveItem T Y it = .ok i) (hok : PlainOK Typ Ground T Y it) :
    ∃ s, i = .plain s ∧ Stmt.TyOK Typ Ground (tyOpt T Y) s := by
  rcases it with ⟨x, tr, e⟩ | ⟨x, e⟩ | ⟨l, e, md⟩ | ⟨r, cs⟩ | ⟨t, e⟩
  · obtain ⟨ty, hr, e', he', rfl⟩ : ∃ ty, RefTy T Y ty tr ∧ ∃ e', resolveOE T Y e = .ok e' ∧
        i = .plain (mkInit x ty e') := by
      cases tr <;> simp only [resolveItem, Except.bind_is_ok, Except.pure_is_ok] at h <;>
        grind [RefTy]
    obtain ⟨h1, h2, h3⟩ := hok ty hr
    exact ⟨_, rfl, fun τ hτ => h1 τ (tyOpt_eq.1 hτ), h2, resolveOE_ok he' h3⟩
  · simp only [resolveItem, Except.bind_is_ok, Except.pure_is_ok] at h
    obtain ⟨e', he', rfl⟩ := h
    obtain ⟨τ, h1, h2, h3⟩ := hok
    exact ⟨_, rfl, τ, tyOpt_eq.2 h1, h2, resolveOE_ok he' h3⟩
  · simp only [resolveItem, Except.bind_is_ok, Except.pure_is_ok] at h
    obtain ⟨e', he', rfl⟩ := h
    exact ⟨_, rfl, hok e' he'⟩
  all_goals cases hb

omit [LawfulBEq P.Ident] [LawfulHasFvars P] [HasIdent P] in
/-- The resolution of a run of obligations with Boolean conditions is a run of `assert`s and
    `cover`s typed against the final types. -/
private theorem resolveObls_ok :
    ∀ (cs : List (Bool × String × WExpr P × MetaData P)) (cs' : PStmts P),
      cs.mapM (fun (isCover, l, e, md) => do
        let e ← resolveE T Y e
        pure (if isCover then (.cmd (.cmd (.cover l e md)) : PStmt P)
          else .cmd (.cmd (.assert l e md)))) = .ok cs' →
      (∀ c ∈ cs, WOK Typ T Y c.2.2.1 HasBool.boolTy) → Block.TyOK Typ Ground (tyOpt T Y) cs'
  | [], cs', h, _ => by cases h; trivial
  | c :: cs, cs', h, hc => by
    simp only [List.mapM_cons, Except.bind_is_ok, Except.pure_is_ok] at h
    obtain ⟨c', ⟨e', he', rfl⟩, cs'', hcs, rfl⟩ := h
    refine ⟨?_, resolveObls_ok cs cs'' hcs fun c hm => hc c (.tail _ hm)⟩
    have he := hc c (.head _) e' he'
    split <;> exact he

omit [LawfulBEq P.Ident] [LawfulHasFvars P] [HasIdent P] in
/-- Resolution keeps whether an item leaves the main path. -/
private theorem resolveItem_isBranching {it : WItem P} {i : Item P}
    (h : resolveItem T Y it = .ok i) : i.isBranching = it.isBranching := by
  rcases it with ⟨x, _ | _, e⟩ | ⟨x, e⟩ | ⟨l, e, md⟩ | ⟨r, cs⟩ | ⟨t, e⟩ <;>
    simp only [resolveItem, Except.bind_is_ok, Except.pure_is_ok] at h <;> grind [Item.isBranching,
      WItem.isBranching]

omit [LawfulBEq P.Ident] [LawfulHasFvars P] [HasIdent P] in
/-- Resolution keeps whether a list has an item leaving the main path. -/
private theorem resolveItems_any :
    ∀ (l : List (WItem P)) (is : List (Item P)), resolveItems T Y l = .ok is →
      is.any Item.isBranching = l.any WItem.isBranching
  | [], is, h => by cases h; rfl
  | a :: l, is, h => by
    obtain ⟨ia, il, ha, hl, rfl⟩ := resolveItems_cons_ok h
    rw [List.any_cons, List.any_cons, resolveItems_any l il hl, resolveItem_isBranching ha]

omit [LawfulBEq P.Ident] [LawfulHasFvars P] [HasIdent P] in
/-- **Resolution keeps the typing of items**: the resolution of items typed against the final
    types (`LOK`) is a list of flat items typed against them (`IOK`). -/
theorem resolveItems_IOK :
    ∀ (b : Bool) (l : List (WItem P)) (items : List (Item P)), resolveItems T Y l = .ok items →
      LOK Typ Ground T Y b l → IOK Typ Ground (tyOpt T Y) b items
  | _, [], _, h, _ => by cases h; simp [IOK]
  | b, .obls r cs :: rest, items, h, hl => by
    obtain ⟨i, is, hi, hr, rfl⟩ := resolveItems_cons_ok h
    simp only [resolveItem, Except.bind_is_ok, Except.pure_is_ok] at hi
    obtain ⟨cs', hcs, rfl⟩ := hi
    simp only [LOK] at hl
    simp only [IOK]
    exact ⟨fun κ hκ y hy => tyOpt_eq.2 (hl.1 κ hκ y hy), resolveObls_ok cs cs' hcs hl.2.1,
      resolveItems_IOK b rest is hr hl.2.2⟩
  | _, .branch t e :: rest, items, h, hl => by
    obtain ⟨i, is, hi, hr, rfl⟩ := resolveItems_cons_ok h
    simp only [resolveItem, Except.bind_is_ok, Except.pure_is_ok] at hi
    obtain ⟨t', ht, e', he, rfl⟩ := hi
    simp only [LOK] at hl
    simp only [IOK]
    exact ⟨resolveItems_IOK false t t' ht hl.1, resolveItems_IOK false e e' he hl.2⟩
  | b, .init x tr e :: rest, items, h, hl | b, .set x e :: rest, items, h, hl
  | b, .assume x e md :: rest, items, h, hl => by
    obtain ⟨i, is, hi, hr, rfl⟩ := resolveItems_cons_ok h
    simp only [LOK] at hl
    obtain ⟨s, rfl⟩ : ∃ s, i = .plain s := by
      have hb := resolveItem_isBranching hi
      cases i <;> first | exact ⟨_, rfl⟩ | cases hb
    simp only [IOK, resolveItems_any rest is hr]
    exact ⟨fun hb => (resolveItem_plain rfl hi (hl.1 hb)).elim fun _ ⟨he, hs⟩ =>
      Item.plain.inj he ▸ hs, resolveItems_IOK b rest is hr hl.2⟩
  termination_by _ l => sizeOf l
end

/-! ## Merging and nesting -/

section
variable [HasSubstFvar P] [HasIdent P] [iW : WPLang P]
variable {Typ : P.Expr → P.Ty → Prop} {Ground : P.Ty → Prop} {Θ : VarTyping P}

omit [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident] [HasFvar P] [Hashable P.Ident]
  [LawfulHasFvars P] [HasSubstFvar P] [HasIdent P] [iW : WPLang P] in
/-- A concatenation of statement lists typed against `Θ` is typed against `Θ`. -/
theorem Block.TyOK_append :
    ∀ (a b : PStmts P), Block.TyOK Typ Ground Θ a → Block.TyOK Typ Ground Θ b →
      Block.TyOK Typ Ground Θ (a ++ b)
  | [], _, _, hb => hb
  | _ :: a, b, ⟨hs, ha⟩, hb => ⟨hs, Block.TyOK_append a b ha hb⟩

omit [LawfulHasFvars P] [HasIdent P] in
/-- **Merging obligation runs keeps the typing of flat items.** -/
theorem mergeObls_IOK :
    ∀ (b : Bool) (l : List (Item P)), IOK Typ Ground Θ b l → IOK Typ Ground Θ b (mergeObls l)
  | _, [], _ => by simp [mergeObls, IOK]
  | b, .obls r cs :: rest, h => by
    simp only [IOK] at h
    have ih := mergeObls_IOK b rest h.2.2
    simp only [mergeObls]
    generalize mergeObls rest = M at ih ⊢
    rcases M with _ | ⟨_ | ⟨r', cs'⟩ | _, rest'⟩
    case cons.obls =>
      simp only [IOK] at ih
      dsimp only
      split
      · rename_i hr
        subst hr
        simp only [IOK]
        exact ⟨h.1, Block.TyOK_append _ _ h.2.1 ih.2.1, ih.2.2⟩
      · simp only [IOK]
        exact ⟨h.1, h.2.1, ih.1, ih.2.1, ih.2.2⟩
    all_goals
      dsimp only
      rw [IOK]
      exact ⟨h.1, h.2.1, ih⟩
  | _, .branch t e :: rest, h => by
    simp only [IOK] at h
    simp only [mergeObls, IOK]
    exact ⟨mergeObls_IOK false t h.1, mergeObls_IOK false e h.2⟩
  | b, .plain s :: rest, h => by
    simp only [IOK] at h
    simp only [mergeObls, IOK, (mergeObls_fv rest).1]
    exact ⟨h.1, mergeObls_IOK b rest h.2⟩
  termination_by _ l => sizeOf l
end

/-! ## Typed expressions -/

section
variable [HasSubstFvar P] [HasIdent P] [iW : WPLang P]
variable {Typ : P.Expr → P.Ty → Prop} {Ground : P.Ty → Prop} {Θ : VarTyping P}

omit [BEq P.Ident] [LawfulBEq P.Ident] [Hashable P.Ident] [HasIdent P] in
/-- A Boolean literal has no annotated free-variable occurrence. -/
theorem ann_lit (b : Bool) {p : P.Ident × P.Ty}
    (h : p ∈ HasFvars.getTypedFvars (if b then (tt : P.Expr) else ff)) : False := by
  have h' := LawfulHasFvars.mem_getFvars_of_typed _ p.1 p.2 h
  cases b <;> simp [WPLang.getFvars_tt, WPLang.getFvars_ff] at h'

omit [DecidableEq P.Ident] [BEq P.Ident] [LawfulBEq P.Ident] [HasBool P] [Hashable P.Ident]
  [HasSubstFvar P] [HasIdent P] iW in
/-- The only annotated free-variable occurrence of an annotated variable is itself. -/
theorem ann_mkVar {x : P.Ident} {ty : P.Ty} {p : P.Ident × P.Ty}
    (h : p ∈ HasFvars.getTypedFvars (HasFvar.mkVar x (some ty))) : p = (x, ty) := by
  simpa using LawfulHasFvars.mkTypedFvar_getTypedFvars x ty h

omit [BEq P.Ident] [LawfulBEq P.Ident] [Hashable P.Ident] [HasIdent P] in
/-- A Boolean literal is a Boolean expression without annotations. -/
theorem ExprOK.lit (hL : TypingLaws Typ Ground) (b : Bool) :
    ExprOK Typ Θ (if b then (tt : P.Expr) else ff) HasBool.boolTy :=
  ⟨by cases b <;> first | exact hL.tt | exact hL.ff, fun _ hp => (ann_lit b hp).elim⟩

omit [BEq P.Ident] [LawfulBEq P.Ident] [Hashable P.Ident] [HasIdent P] in
/-- A variable annotated with a ground type that `Θ` gives it has that type. -/
theorem ExprOK.var (hL : TypingLaws Typ Ground) {x : P.Ident} {ty : P.Ty} (hg : Ground ty)
    (hx : Θ x = some ty) : ExprOK Typ Θ (HasFvar.mkVar x (some ty)) ty :=
  ⟨hL.mkVar x hg, fun p hp => by obtain rfl := ann_mkVar hp; exact hx⟩

omit [BEq P.Ident] [LawfulBEq P.Ident] [Hashable P.Ident] [LawfulHasFvars P] [HasIdent P] in
/-- A conditional of a Boolean condition and two branches of type `ty` has type `ty`. -/
theorem ExprOK.ite (hL : TypingLaws Typ Ground) {c t f : P.Expr} {ty : P.Ty}
    (hc : ExprOK Typ Θ c HasBool.boolTy) (ht : ExprOK Typ Θ t ty) (hf : ExprOK Typ Θ f ty) :
    ExprOK Typ Θ (WPOps.ite c t f) ty :=
  ⟨hL.ite.2 ⟨hc.1, ht.1, hf.1⟩, fun p hp =>
    (WPLang.getTypedFvars_ite _ _ _ p hp).elim (hc.2 p) (·.elim (ht.2 p) (hf.2 p))⟩

omit [BEq P.Ident] [LawfulBEq P.Ident] [Hashable P.Ident] [HasIdent P] in
/-- The condition of a reach context whose variables `Θ` types Boolean is Boolean. -/
theorem ExprOK.reExpr (hL : TypingLaws Typ Ground) (κ : RE P)
    (h : ∀ y ∈ RE.vars κ, Θ y = some HasBool.boolTy) : ExprOK Typ Θ κ.expr HasBool.boolTy := by
  have hg : Ground HasBool.boolTy := hL.ground hL.tt
  have hv : ∀ y ∈ RE.vars κ, ExprOK Typ Θ (HasFvar.mkBoolVar y) HasBool.boolTy :=
    fun y hy => ExprOK.var hL hg (h y hy)
  have hn : ∀ {e : P.Expr}, ExprOK Typ Θ e HasBool.boolTy → ExprOK Typ Θ (notE e) HasBool.boolTy :=
    fun he => ExprOK.ite hL he (ExprOK.lit hL false) (ExprOK.lit hL true)
  cases κ with
  | top => exact ExprOK.lit hL true
  | name r => exact hv r (.head _)
  | neg g => exact hn (hv g (.head _))
  | andNeg q g =>
    exact ExprOK.ite hL (hv q (.head _)) (hn (hv g (.tail _ (.head _)))) (ExprOK.lit hL false)

omit [BEq P.Ident] [LawfulBEq P.Ident] [Hashable P.Ident] [HasIdent P] in
/-- The nesting of a list of statements around an obligation run is typed when the parts are. -/
private theorem reachPre_TyOK (hL : TypingLaws Typ Ground) (r : Option (RE P))
    (h : ∀ κ, r = some κ → ∀ y ∈ RE.vars κ, Θ y = some HasBool.boolTy) :
    Block.TyOK Typ Ground Θ (reachPre r) := by
  rcases r with _ | (_ | r | g | ⟨q, g⟩)
  iterate 2 trivial
  all_goals exact ⟨ExprOK.reExpr hL _ (h _ rfl), trivial⟩

omit [BEq P.Ident] [LawfulBEq P.Ident] [Hashable P.Ident] [HasIdent P] in
/-- **The nesting of flat items typed against `Θ` is typed against `Θ`.** -/
theorem nest_TyOK (hL : TypingLaws Typ Ground) :
    ∀ (b : Bool) (l : List (Item P)), IOK Typ Ground Θ b l → Block.TyOK Typ Ground Θ (nest l)
  | _, [], _ => trivial
  | b, .plain s :: rest, h => by
    simp only [IOK] at h
    simp only [nest, nestCons]
    split
    · rename_i hb
      exact ⟨h.1 (by simp [hb]), nest_TyOK hL b rest h.2⟩
    · trivial
  | b, .obls r cs :: rest, h => by
    simp only [IOK] at h
    have hpre := Block.TyOK_append _ _ (reachPre_TyOK hL r h.1) h.2.1
    simp only [nest, nestCons]
    split
    · exact ⟨⟨hpre, nest_TyOK hL b rest h.2.2⟩, trivial⟩
    · exact hpre
  | _, .branch t e :: rest, h => by
    simp only [IOK] at h
    have ht := nest_TyOK hL false t h.1
    have he := nest_TyOK hL false e h.2
    simp only [nest, nestCons]
    split
    · exact he
    · exact ht
    · exact ⟨⟨ht, he⟩, trivial⟩
  termination_by _ l => sizeOf l
end

/-! ## Typed guarded expressions -/

section
variable [HasSubstFvar P] [HasIdent P] [iW : WPLang P]
variable {Typ : P.Expr → P.Ty → Prop} {Ground : P.Ty → Prop}
  {T : Std.HashMap P.Ident P.Ty} {Y : Std.HashMap P.Ident P.Ident} {κ : RE P}

omit [LawfulBEq P.Ident] [HasIdent P] in
/-- A variable whose final types are the ground type `ty` has type `ty`. -/
theorem WOK.var (hL : TypingLaws Typ Ground) {x : P.Ident} {ty : P.Ty} (hg : Ground ty)
    (hx : ∀ τ, tyOfName T Y x = .ok τ → τ = ty) : WOK Typ T Y (.var x) ty := by
  intro e he
  simp only [resolveE, Except.bind_is_ok, Except.pure_is_ok] at he
  obtain ⟨τ, hτ, rfl⟩ := he
  obtain rfl := hx τ hτ
  exact ExprOK.var hL hg (tyOpt_eq.2 hτ)

omit [LawfulBEq P.Ident] [HasIdent P] in
/-- A variable with the Boolean final type is Boolean. -/
theorem WOK.bvar (hL : TypingLaws Typ Ground) {x : P.Ident}
    (hx : tyOfName T Y x = .ok HasBool.boolTy) : WOK Typ T Y (.var x) HasBool.boolTy :=
  WOK.var hL (hL.ground hL.tt) fun _ h => Except.ok.inj (h.symm.trans hx)

omit [LawfulBEq P.Ident] [HasIdent P] in
/-- A Boolean literal is Boolean. -/
theorem WOK.lit (hL : TypingLaws Typ Ground) (b : Bool) :
    WOK Typ T Y (.lit b) HasBool.boolTy := fun e he => by
  cases he
  exact ExprOK.lit hL b

omit [LawfulBEq P.Ident] [LawfulHasFvars P] [HasIdent P] in
/-- A conditional of a Boolean condition and two branches of type `ty` has type `ty`. -/
theorem WOK.ite (hL : TypingLaws Typ Ground) {c t f : WExpr P} {ty : P.Ty}
    (hc : WOK Typ T Y c HasBool.boolTy) (ht : WOK Typ T Y t ty) (hf : WOK Typ T Y f ty) :
    WOK Typ T Y (.ite c t f) ty := fun e he => by
  obtain ⟨c', t', f', h1, h2, h3, rfl⟩ := resolveE_ite.1 he
  exact ExprOK.ite hL (hc _ h1) (ht _ h2) (hf _ h3)

omit [LawfulBEq P.Ident] [HasIdent P] in
/-- The negation of a Boolean expression is Boolean. -/
theorem WOK.not (hL : TypingLaws Typ Ground) {a : WExpr P} (h : WOK Typ T Y a HasBool.boolTy) :
    WOK Typ T Y a.not HasBool.boolTy := by
  unfold WExpr.not
  split
  · exact WOK.lit hL _
  · exact WOK.ite hL h (WOK.lit hL _) (WOK.lit hL _)

omit [LawfulBEq P.Ident] [HasIdent P] in
/-- The conjunction of Boolean expressions is Boolean. -/
theorem WOK.and (hL : TypingLaws Typ Ground) {a b : WExpr P} (ha : WOK Typ T Y a HasBool.boolTy)
    (hb : WOK Typ T Y b HasBool.boolTy) : WOK Typ T Y (a.and b) HasBool.boolTy :=
  WOK.ite hL ha hb (WOK.lit hL _)

omit [LawfulBEq P.Ident] [HasIdent P] in
/-- The disjunction of Boolean expressions is Boolean. -/
theorem WOK.or (hL : TypingLaws Typ Ground) {a b : WExpr P} (ha : WOK Typ T Y a HasBool.boolTy)
    (hb : WOK Typ T Y b HasBool.boolTy) : WOK Typ T Y (a.or b) HasBool.boolTy :=
  WOK.ite hL ha (WOK.lit hL _) hb

omit [LawfulBEq P.Ident] [HasIdent P] in
/-- `ite(κ, t, f)` has type `ty` under a Boolean reach context when `t` and `f` do. -/
theorem WOK.kIte (hL : TypingLaws Typ Ground) (hκ : REOK T Y κ) {t f : WExpr P} {ty : P.Ty}
    (ht : WOK Typ T Y t ty) (hf : WOK Typ T Y f ty) : WOK Typ T Y (kIte κ t f) ty := by
  cases κ with
  | top => exact ht
  | name r => exact WOK.ite hL (WOK.bvar hL (hκ r (.head _))) ht hf
  | neg g => exact WOK.ite hL (WOK.bvar hL (hκ g (.head _))) hf ht
  | andNeg q g =>
    exact WOK.ite hL (WOK.bvar hL (hκ q (.head _)))
      (WOK.ite hL (WOK.bvar hL (hκ g (.tail _ (.head _)))) hf ht) hf

omit [LawfulBEq P.Ident] [HasIdent P] in
/-- The value of a Boolean reach context is Boolean. -/
theorem WOK.kExpr (hL : TypingLaws Typ Ground) (hκ : REOK T Y κ) :
    WOK Typ T Y (kExpr κ) HasBool.boolTy := by
  cases κ with
  | top => exact WOK.lit hL true
  | name r => exact WOK.bvar hL (hκ r (.head _))
  | neg g => exact WOK.not hL (WOK.bvar hL (hκ g (.head _)))
  | andNeg q g =>
    exact WOK.and hL (WOK.bvar hL (hκ q (.head _)))
      (WOK.not hL (WOK.bvar hL (hκ g (.tail _ (.head _)))))

omit [LawfulBEq P.Ident] [HasIdent P] in
/-- The disjunction of a list of Boolean expressions is Boolean. -/
theorem WOK.disjW (hL : TypingLaws Typ Ground) :
    ∀ l : List (WExpr P), (∀ a ∈ l, WOK Typ T Y a HasBool.boolTy) →
      WOK Typ T Y (disjW l) HasBool.boolTy
  | [], _ => WOK.lit hL false
  | [a], h => h a (.head _)
  | a :: b :: l, h => WOK.or hL (h a (.head _)) (WOK.disjW hL (b :: l) fun c hc => h c (.tail _ hc))

omit [LawfulHasFvars P] [HasIdent P] in
/-- The hash map that resolution builds from a renaming `ren` maps a variable to the variable
    annotated with the final type of a name to which `ren` renames it, and maps no variable that
    `ren` does not rename. -/
private theorem foldlM_ren_ty (L : List (P.Ident × P.Ident)) :
    ∀ (ren : List (P.Ident × P.Ident)) (h0 h : Std.HashMap P.Ident P.Expr), (∀ q ∈ ren, q ∈ L) →
    (∀ y v, h0[y]? = some v →
      ∃ q ∈ L, q.1 = y ∧ ∃ τ, tyOfName T Y q.2 = .ok τ ∧ v = HasFvar.mkVar q.2 (some τ)) →
    ren.foldlM (init := h0) (fun h (y, y') => do
      pure (h.insert y (HasFvar.mkVar y' (some (← tyOfName T Y y'))))) = Except.ok h →
    (∀ y v, h[y]? = some v →
      ∃ q ∈ L, q.1 = y ∧ ∃ τ, tyOfName T Y q.2 = .ok τ ∧ v = HasFvar.mkVar q.2 (some τ)) ∧
    ∀ y, h[y]? = none → h0[y]? = none ∧ ∀ q ∈ ren, q.1 ≠ y
  | [], h0, h, _, h0e, hf => by
    cases hf
    exact ⟨h0e, fun y hy => ⟨hy, nofun⟩⟩
  | (y, y') :: ps, h0, h, hL', h0e, hf => by
    simp only [List.foldlM_cons, bind, Except.bind, pure, Except.pure] at hf
    rcases hty : tyOfName T Y y' with _ | ty <;> simp only [hty, reduceCtorEq] at hf
    obtain ⟨h1, h2⟩ := foldlM_ren_ty L ps _ h (fun q hq => hL' q (.tail _ hq)) (fun z v hz => by
      rw [Std.HashMap.getElem?_insert] at hz
      split at hz
      · rename_i he
        cases hz
        exact ⟨(y, y'), hL' _ (.head _), by simpa using he, ty, hty, rfl⟩
      · exact h0e z v hz) hf
    refine ⟨h1, fun z hz => ?_⟩
    obtain ⟨hz1, hz2⟩ := h2 z hz
    rw [Std.HashMap.getElem?_insert] at hz1
    split at hz1
    · cases hz1
    · rename_i he
      refine ⟨hz1, fun q hq => ?_⟩
      rcases List.mem_cons.1 hq with rfl | hq
      · simpa using he
      · exact hz2 q hq

omit [HasIdent P] in
/-- **A renamed loop-free expression is typed** at the type `ty` of the loop-free expression when
    each annotated occurrence `(y, τ)` of it has, when `y` is not renamed, the final type `τ`, and
    every name to which `ren` renames `y` has the final type `τ`. -/
theorem WOK.user (hL : TypingLaws Typ Ground) {e : P.Expr} {ren : List (P.Ident × P.Ident)}
    {ty : P.Ty} (he : Typ e ty)
    (h1 : ∀ p ∈ HasFvars.getTypedFvars e, (∀ q ∈ ren, q.1 ≠ p.1) → tyOfName T Y p.1 = .ok p.2)
    (h2 : ∀ p ∈ HasFvars.getTypedFvars e, ∀ q ∈ ren, q.1 = p.1 → tyOfName T Y q.2 = .ok p.2) :
    WOK Typ T Y (.user e ren) ty := by
  intro e' hr
  cases ren with
  | nil =>
    cases hr
    exact ⟨he, fun p hp => tyOpt_eq.2 (h1 p hp nofun)⟩
  | cons q0 ps =>
    simp only [resolveE, Except.bind_is_ok, Except.pure_is_ok] at hr
    obtain ⟨hm, hf, rfl⟩ := hr
    obtain ⟨hs, hn⟩ := foldlM_ren_ty (q0 :: ps) (q0 :: ps) {} hm (fun _ h => h)
      (fun _ _ h => by simp at h) hf
    refine ⟨hL.substFn _ he fun p hp v hpv => ?_, fun p hp => ?_⟩
    · obtain ⟨q, hq, hq1, τ, hτ, rfl⟩ := hs p.1 v hpv
      obtain rfl := Except.ok.inj ((h2 p hp q hq hq1).symm.trans hτ)
      exact hL.var _ he hp
    · rcases WPLang.getTypedFvars_substFn e _ p hp with ⟨hp, hg⟩ | ⟨z, v, hz, hg, hpv⟩
      · exact tyOpt_eq.2 (h1 p hp (hn p.1 hg).2)
      · obtain ⟨q, hq, rfl, τ, hτ, rfl⟩ := hs z v hg
        obtain rfl := ann_mkVar hpv
        exact tyOpt_eq.2 hτ
end

/-! ## Item lists typed against the final types -/

section
variable [HasSubstFvar P] [HasIdent P] [iW : WPLang P]
variable {Typ : P.Expr → P.Ty → Prop} {Ground : P.Ty → Prop}
  {T : Std.HashMap P.Ident P.Ty} {Y : Std.HashMap P.Ident P.Ident}

omit [LawfulBEq P.Ident] [LawfulHasFvars P] [HasIdent P] in
/-- A concatenation of item lists is typed when its first part is, with the branching items of
    the second part following it, and its second part is. -/
theorem LOK_append :
    ∀ (b : Bool) (l1 l2 : List (WItem P)),
      LOK Typ Ground T Y (b || l2.any WItem.isBranching) l1 → LOK Typ Ground T Y b l2 →
      LOK Typ Ground T Y b (l1 ++ l2)
  | _, [], _, _, h2 => h2
  | b, .obls r cs :: rest, l2, h1, h2 => by
    simp only [LOK, List.cons_append] at h1 ⊢
    exact ⟨h1.1, h1.2.1, LOK_append b rest l2 h1.2.2 h2⟩
  | _, .branch t e :: rest, _, h1, _ => by
    simp only [LOK, List.cons_append] at h1 ⊢
    exact h1
  | b, .init x tr e :: rest, l2, h1, h2 | b, .set x e :: rest, l2, h1, h2
  | b, .assume x e md :: rest, l2, h1, h2 => by
    simp only [LOK, List.cons_append, List.any_append] at h1 ⊢
    refine ⟨fun hb => h1.1 ?_, LOK_append b rest l2 h1.2 h2⟩
    revert hb
    cases b <;> cases rest.any WItem.isBranching <;> cases l2.any WItem.isBranching <;> simp
  termination_by _ l => sizeOf l

omit [LawfulBEq P.Ident] [LawfulHasFvars P] [HasIdent P] in
/-- A list of items without branching items, after which no branching item follows, is
    typed. -/
theorem LOK_noBr :
    ∀ (l : List (WItem P)), l.any WItem.isBranching = false → LOK Typ Ground T Y false l
  | [], _ => by simp [LOK]
  | it :: rest, h => by
    simp only [List.any_cons, Bool.or_eq_false_iff] at h
    rcases it with _ | _ | _ | _ | _
    case obls | branch => cases h.1
    all_goals
      simp only [LOK, h.2, Bool.or_false, Bool.false_eq_true]
      exact ⟨nofun, LOK_noBr rest h.2⟩

omit [LawfulBEq P.Ident] [LawfulHasFvars P] [HasIdent P] in
/-- A list of items typed when a branching item follows it, if one follows whenever one
    follows under `b'`, is typed under `b'`. -/
theorem LOK.imp : ∀ {b b' : Bool} {l : List (WItem P)}, (b' = true → b = true) →
    LOK Typ Ground T Y b l → LOK Typ Ground T Y b' l
  | _, _, [], _, _ => by simp [LOK]
  | b, b', .obls r cs :: rest, hb, h => by
    simp only [LOK] at h ⊢
    exact ⟨h.1, h.2.1, LOK.imp hb h.2.2⟩
  | _, _, .branch t e :: rest, _, h => by
    simp only [LOK] at h ⊢
    exact h
  | b, b', .init x tr e :: rest, hb, h | b, b', .set x e :: rest, hb, h
  | b, b', .assume x e md :: rest, hb, h => by
    simp only [LOK] at h ⊢
    refine ⟨fun h' => h.1 ?_, LOK.imp hb h.2⟩
    revert h'
    cases b' <;> cases b <;> simp_all
  termination_by _ _ l => sizeOf l

omit [LawfulBEq P.Ident] [LawfulHasFvars P] [HasIdent P] in
/-- A list of straight-line items typed against the final types is typed. -/
theorem LOK_plain : ∀ {b : Bool} {l : List (WItem P)},
    (∀ it ∈ l, it.isBranching = false ∧ PlainOK Typ Ground T Y it) → LOK Typ Ground T Y b l
  | _, [], _ => by simp [LOK]
  | b, it :: rest, h => by
    have hr := LOK_plain (b := b) fun it hm => h it (.tail _ hm)
    obtain ⟨hb, hp⟩ := h it (.head _)
    rcases it with _ | _ | _ | _ | _
    case obls | branch => cases hb
    all_goals
      simp only [LOK]
      exact ⟨fun _ => hp, hr⟩
end

end -- public section

end WP
end Imperative
